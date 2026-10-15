"""Tracking contracts are mocked; no MLflow run or scientific comparison is created."""
import json
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

import pytest

import figures
import track_experiment as tracking


def test_tracking_health_check_uses_standard_http_without_local_helpers(monkeypatch):
    requests = []
    class Response:
        def __enter__(self):
            return self
        def __exit__(self, *args):
            return None
        status = 200
    def health(url, timeout):
        requests.append((url, timeout))
        return Response()
    monkeypatch.setattr(tracking, "urlopen", health, raising=False)
    def local_helper(*args, **kwargs):
        pytest.fail("public tracking must not require local mlflow-status/mlflow-start commands")
    monkeypatch.setattr(tracking.subprocess, "run", local_helper)
    tracking.check_tracking_service("http://127.0.0.1:5000")
    assert requests == [("http://127.0.0.1:5000/health", 20)]


class Client:
    def __init__(self):
        self.events = []
    def get_experiment_by_name(self, name):
        return SimpleNamespace(experiment_id='unit-test-experiment')
    def create_run(self, experiment_id, tags):
        self.events.append(('create', tags))
        return SimpleNamespace(info=SimpleNamespace(run_id='unit-test-run'))
    def log_param(self, *args):
        self.events.append(('param', args))
    def log_metric(self, *args):
        self.events.append(('metric', args))
    def set_tag(self, *args):
        self.events.append(('tag', args))
    def log_artifacts(self, run_id, directory):
        assert (Path(directory) / 'engine_stderr.log').exists()
        self.events.append(('artifacts', directory))
    def log_artifact(self, run_id, file):
        assert Path(file).exists()
        self.events.append(('artifact', file))
    def set_terminated(self, run_id, status):
        self.events.append(('terminated', status))


def test_nonfinite_missing_and_boolean_metrics_are_not_logged():
    values = {'good': 3, 'missing': None, 'nan': float('nan'), 'infinite': float('inf'),
              'boolean': True, 'nested': {'residual': 0.125, 'unavailable': None}}
    assert tracking.finite_metrics(values) == {'good': 3.0, 'nested.residual': 0.125}


def test_unversioned_source_is_never_tagged_clean():
    tags = tracking.provenance_tags({'commit': None, 'branch': None, 'dirty': None,
                                     'repository_detected': False})
    assert tags['source.git.commit'] == 'uncommitted'
    assert tags['source.git.dirty'] == 'unknown-no-git'
    assert tags['source.provenance'] == 'uncommitted-source-manifest'


@pytest.mark.parametrize('return_code,quality,expected', [(0, True, 'FINISHED'), (1, True, 'FAILED'), (0, False, 'FAILED')])
def test_engine_failures_remain_tracked_with_artifacts(tmp_path, return_code, quality, expected):
    args = tracking.parse_args(['--python', sys.executable, '--output', str(tmp_path)])
    client = Client()
    def child(command, **kwargs):
        assert command[command.index('--mlflow-run-id') + 1] == 'unit-test-run'
        data = {'metadata': {'complete': True, 'source_unchanged': True, 'all_quality_passed': quality},
                'analytic': [], 'solves': [], 'comparisons': []}
        (tmp_path / 'results.json').write_text(json.dumps(data))
        return subprocess.CompletedProcess(command, return_code, stdout='child output', stderr='child diagnostic')
    summary = tracking.execute(args, client=client, process_runner=child)
    assert summary['status'] == expected
    assert summary['run_id'] == 'unit-test-run'
    assert ('terminated', expected) in client.events
    assert any(e[0] == 'artifacts' for e in client.events)
    assert (tmp_path / 'engine_stderr.log').read_text() == 'child diagnostic'
    assert json.loads((tmp_path / 'tracking_result.json').read_text()) == summary


def test_child_exception_preserves_failed_run_identity(tmp_path):
    args = tracking.parse_args(['--python', sys.executable, '--output', str(tmp_path)])
    client = Client()
    def broken_child(*args, **kwargs):
        raise OSError('synthetic spawn error')
    summary = tracking.execute(args, client=client, process_runner=broken_child)
    assert summary['status'] == 'FAILED' and summary['run_id'] == 'unit-test-run'
    assert 'synthetic spawn error' in summary['error']
    assert ('terminated', 'FAILED') in client.events
    assert any(e[0] == 'artifacts' for e in client.events)


def test_nonempty_output_is_rejected_before_tracking(tmp_path):
    (tmp_path / 'old.json').write_text('retained')
    args = tracking.parse_args(['--python', sys.executable, '--output', str(tmp_path)])
    client = Client()
    with pytest.raises(FileExistsError):
        tracking.execute(args, client=client)
    assert not client.events
    assert (tmp_path / 'old.json').read_text() == 'retained'


def test_figure_data_selection_does_not_invent_missing_values():
    rows = [{'action': None}, {'action': float('nan')}, {'action': True},
            {'action': 0.25, 'quality_passed': False}]
    assert figures.finite_rows(rows, 'action') == [rows[-1]]


def test_virtual_environment_interpreter_symlink_is_not_dereferenced(tmp_path):
    interpreter = tmp_path / 'venv' / 'bin' / 'python'
    interpreter.parent.mkdir(parents=True)
    interpreter.symlink_to(Path(sys.executable).resolve())
    output = tmp_path / 'results'
    args = tracking.parse_args(['--python', str(interpreter), '--output', str(output)])
    client = Client()
    def child(command, **kwargs):
        assert command[0] == str(interpreter.absolute())
        assert command[0] != str(interpreter.resolve())
        output.mkdir()
        (output / 'results.json').write_text(json.dumps({
            'metadata': {'complete': True, 'source_unchanged': True, 'all_quality_passed': True},
            'analytic': [], 'solves': [], 'comparisons': []}))
        return subprocess.CompletedProcess(command, 0, stdout='', stderr='')
    summary = tracking.execute(args, client=client, process_runner=child)
    assert summary['status'] == 'FINISHED'
    saved = json.loads((output / 'tracking_metadata.json').read_text())
    assert saved['configuration']['numerical_python'] == str(interpreter.absolute())
