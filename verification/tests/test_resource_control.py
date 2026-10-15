"""Scheduling and failure-status regressions for the Lean process resource guard."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

HELPER = Path(__file__).resolve().parents[1] / "resource-control.sh"
PIN = "6a10ac8c22beadecabdbb0919c2b50214762f91d"


class ResourceControlTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.toolchain = self.root / "toolchain"
        (self.toolchain / "bin").mkdir(parents=True)
        (self.toolchain / "lib").mkdir()
        (self.toolchain / "lib/sentinel").write_text("unchanged library")
        self.output = self.root / "output"
        self.output.mkdir()
        self.events = self.root / "events.jsonl"
        self.lean = self.toolchain / "bin/lean"
        self.lean.write_text("#!/usr/bin/env python3\n" +
            "import json,os,sys,time\n" +
            "from pathlib import Path\n" +
            "args=sys.argv[1:]\n" +
            f"prefix={str(self.toolchain)!r}\n" +
            f"pin={PIN!r}\n" +
            "if '--print-prefix' in args: print(prefix); sys.exit(0)\n" +
            "if '--githash' in args: print(pin); sys.exit(0)\n" +
            "events=Path(os.environ['TEST_EVENTS'])\n" +
            "def record(kind):\n" +
            " with events.open('a') as f: f.write(json.dumps({'kind':kind,'pid':os.getpid(),'args':args})+'\\n')\n" +
            "record('start'); time.sleep(0.04); record('end')\n" +
            "sys.exit(23 if '--fail' in args else 0)\n")
        self.lean.chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.toolchain / "bin") + ":" + os.environ["PATH"],
                        TEST_EVENTS=str(self.events))

    def run_shell(self, body):
        script = 'set -euo pipefail\nsource "$1"\noutput_dir=$2\n' + body
        return subprocess.run(['bash', '-c', script, 'resource-test', str(HELPER), str(self.output)],
                              env=self.env, text=True, capture_output=True)

    def test_concurrent_requests_are_serial_and_preserve_arguments(self):
        result = self.run_shell("""resource_control_init
trap 'resource_control_cleanup "$?"' EXIT
compiler_pids=()
for item in alpha beta gamma; do
  "$LEAN_SYSROOT/bin/lean" "$item" --trust=0 -DautoImplicit=false &
  compiler_pids+=("$!")
done
for compiler_pid in "${compiler_pids[@]}"; do wait "$compiler_pid"; done
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        records = [json.loads(line) for line in self.events.read_text().splitlines()]
        self.assertEqual([r['kind'] for r in records], ['start', 'end'] * 3)
        self.assertEqual({r['args'][1] for r in records}, {'alpha', 'beta', 'gamma'})
        for record in records:
            self.assertEqual(record['args'][0], '--threads=1')
            self.assertEqual(record['args'][2:], ['--trust=0', '-DautoImplicit=false'])
        self.assertEqual((self.output / 'pipeline-exit.txt').read_text().strip(), '0')
        self.assertIn('max_concurrent_lean_processes=1', (self.output / 'resource-policy.txt').read_text())
        invocations = (self.output / 'lean-processes.log').read_text().splitlines()
        self.assertEqual(len(invocations), 3)
        self.assertTrue(all('--threads=1' in line and '--trust=0' in line for line in invocations))

    def test_compiler_failure_status_propagates(self):
        result = self.run_shell("""resource_control_init
trap 'resource_control_cleanup "$?"' EXIT
"$LEAN_SYSROOT/bin/lean" --fail
""")
        self.assertEqual(result.returncode, 23, result.stderr)
        self.assertEqual((self.output / 'pipeline-exit.txt').read_text().strip(), '23')
        self.assertIn('exit:23', (self.output / 'resource-samples.log').read_text())

    def mock_unavailable_ps(self):
        ps = self.toolchain / 'bin/ps'
        ps.write_text('#!/usr/bin/env bash\n'
                      'printf "fatal library error, lookup self\\n" >&2\n'
                      'exit 70\n')
        ps.chmod(0o755)

    def test_unavailable_process_diagnostics_do_not_stop_verification(self):
        self.mock_unavailable_ps()
        result = self.run_shell("""resource_control_init
trap 'resource_control_cleanup "$?"' EXIT
resource_phase proof-check
"$LEAN_SYSROOT/bin/lean" verified --trust=0
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        samples = (self.output / 'resource-samples.log').read_text()
        self.assertIn('fatal library error, lookup self', samples)
        self.assertIn('process_diagnostics=unavailable', samples)
        self.assertIn('phase=proof-check', samples)
        self.assertEqual((self.output / 'pipeline-exit.txt').read_text().strip(), '0')
        records = [json.loads(line) for line in self.events.read_text().splitlines()]
        self.assertEqual([r['kind'] for r in records], ['start', 'end'])
        self.assertEqual(records[0]['args'], ['--threads=1', 'verified', '--trust=0'])

    def test_unavailable_process_diagnostics_preserve_compiler_failure(self):
        self.mock_unavailable_ps()
        result = self.run_shell("""resource_control_init
trap 'resource_control_cleanup "$?"' EXIT
"$LEAN_SYSROOT/bin/lean" --fail
""")
        self.assertEqual(result.returncode, 23, result.stderr)
        self.assertEqual((self.output / 'pipeline-exit.txt').read_text().strip(), '23')
        self.assertIn('exit:23', (self.output / 'resource-samples.log').read_text())

    def test_mirror_keeps_real_binary_and_libraries_unchanged(self):
        original = self.lean.read_bytes()
        result = self.run_shell("""resource_control_init
mirror=$resource_toolchain
test "$(cat "$LEAN_SYSROOT/lib/sentinel")" = 'unchanged library'
test "$LAKE_OVERRIDE_LEAN" = true
test "$PROOF_REAL_LEAN" = "$3"
resource_control_cleanup 0
test ! -e "$mirror"
""".replace('"$3"', '"' + str(self.lean) + '"'))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.lean.read_bytes(), original)
        self.assertEqual(list(self.output.glob('toolchain*')), [])
        self.assertEqual((self.toolchain / 'lib/sentinel').read_text(), 'unchanged library')

    def test_wrong_pinned_compiler_is_rejected_before_mirror(self):
        self.lean.write_text(self.lean.read_text().replace(PIN, '0' * 40))
        result = self.run_shell('resource_control_init\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse((self.output / 'lean-process-wrapper.txt').exists())

    def mock_free_disk(self, available):
        df = self.toolchain / 'bin/df'
        df.write_text('#!/usr/bin/env bash\n' +
                      "printf 'Filesystem 1024-blocks Used Available Capacity Mounted on\\n" +
                      f"/dev/fake 30000000 10000000 {available} 50%% /\\n'\n")
        df.chmod(0o755)

    def test_disk_floor_rejects_insufficient_space(self):
        self.mock_free_disk(100)
        result = self.run_shell('resource_require_disk complete-export 2097152\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Insufficient disk reserve', result.stderr)
        self.assertFalse((self.output / 'disk-reserve-checks.log').exists())

    def test_disk_floor_passes_at_exact_required_reserve(self):
        self.mock_free_disk(14680064)
        result = self.run_shell('resource_require_disk pre-cache 14680064\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('minimum_kib=14680064', (self.output / 'disk-reserve-checks.log').read_text())

    def test_owned_download_cache_release_preserves_other_caches_and_evidence(self):
        self.mock_free_disk(20000000)
        self.env['GITHUB_ACTIONS'] = 'true'
        self.env['RUNNER_ENVIRONMENT'] = 'github-hosted'
        other = self.root / 'other-cache'
        other.mkdir()
        (other / 'reference').write_text('keep')
        (self.output / 'certificate.json').write_text('existing evidence')
        result = self.run_shell("""resource_prepare_download_cache
owned=$resource_mathlib_cache
printf 'disposable download' > "$owned/download.ltar"
resource_release_download_cache
test ! -e "$owned"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((other / 'reference').read_text(), 'keep')
        self.assertEqual((self.output / 'certificate.json').read_text(), 'existing evidence')

    def checker_fixture(self):
        checker = self.root / 'checker'
        (checker / 'target/release').mkdir(parents=True)
        (checker / 'target/release/nanoda_bin').write_bytes(b'exact pinned checker executable')
        (checker / 'Cargo.lock').write_text('pinned dependency lock')
        (checker / 'src').mkdir()
        (checker / 'src/main.rs').write_text('checked source')
        for name in ('deps', 'build', '.fingerprint', 'incremental', 'examples'):
            (checker / 'target/release' / name).mkdir()
            (checker / 'target/release' / name / 'derived').write_text('rebuildable')
        return checker

    def test_hosted_checker_cleanup_preserves_binary_source_and_lock(self):
        checker = self.checker_fixture()
        self.env['GITHUB_ACTIONS'] = 'true'
        self.env['RUNNER_ENVIRONMENT'] = 'github-hosted'
        result = self.run_shell('checker_dir="' + str(checker) + '"\nresource_release_checker_intermediates\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(list((checker / 'target/release').iterdir()), [checker / 'target/release/nanoda_bin'])
        self.assertEqual((checker / 'target/release/nanoda_bin').read_bytes(), b'exact pinned checker executable')
        self.assertEqual((checker / 'Cargo.lock').read_text(), 'pinned dependency lock')
        self.assertEqual((checker / 'src/main.rs').read_text(), 'checked source')

    def test_local_checker_and_download_caches_are_untouched(self):
        checker = self.checker_fixture()
        self.env.pop('GITHUB_ACTIONS', None)
        result = self.run_shell('checker_dir="' + str(checker) + '"\nresource_prepare_download_cache\nresource_release_checker_intermediates\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((checker / 'target/release/deps/derived').is_file())
        self.assertFalse((self.output / 'disk-reserve-checks.log').exists())

    def test_self_hosted_actions_caches_are_untouched(self):
        checker = self.checker_fixture()
        self.env.update(GITHUB_ACTIONS='true', RUNNER_ENVIRONMENT='self-hosted')
        result = self.run_shell('checker_dir="' + str(checker) + '"\nresource_prepare_download_cache\nresource_release_checker_intermediates\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((checker / 'target/release/deps/derived').is_file())
        self.assertFalse((self.output / 'disk-reserve-checks.log').exists())

    def test_workflow_sdk_cleanup_is_inactive_on_self_hosted_runner(self):
        workflow = (HELPER.parent.parent / '.github/workflows/verify.yml').read_text()
        start = workflow.index('      - name: Reserve disk space for complete kernel evidence')
        end = workflow.index('      - name: Install pinned official Lean toolchain', start)
        block = workflow[start:end].split('        run: |\n', 1)[1]
        commands = '\n'.join(line[10:] for line in block.splitlines() if line.strip()) + '\n'
        self.env.update(GITHUB_ACTIONS='true', RUNNER_ENVIRONMENT='self-hosted')
        sudo = self.toolchain / 'bin/sudo'
        sudo.write_text('#!/usr/bin/env bash\nprintf "unexpected SDK cleanup" >&2\nexit 99\n')
        sudo.chmod(0o755)
        result = subprocess.run(['bash', '-c', commands], env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn('unexpected SDK cleanup', result.stderr)

    def test_exit_diagnostic_disk_failure_preserves_original_compiler_failure(self):
        result = self.run_shell("""resource_control_init
trap 'resource_control_cleanup "$?"' EXIT
ln -s /dev/full "$output_dir/pipeline-exit.txt"
"$LEAN_SYSROOT/bin/lean" --fail
""")
        self.assertEqual(result.returncode, 23, result.stderr)
        self.assertIn('original pipeline status=23', result.stderr)

    def test_diagnostics_do_not_mutate_after_final_checksum(self):
        result = self.run_shell("""resource_control_init
trap 'resource_control_cleanup "$?"' EXIT
resource_phase complete
resource_control_cleanup 0
trap - EXIT
(cd "$output_dir"; sha256sum * > artifact-SHA256SUMS)
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        checked = subprocess.run(['sha256sum', '--check', 'artifact-SHA256SUMS'], cwd=self.output,
                                 text=True, capture_output=True)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)


if __name__ == '__main__':
    unittest.main()
