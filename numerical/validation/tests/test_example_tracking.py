"""Mocked example tracking checks; no run or numerical study is created."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

import pytest

from test_tracking import Client

spec = importlib.util.spec_from_file_location("example_tracking", Path(__file__).resolve().parents[2] / "track_example.py")
tracking = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tracking)


@pytest.mark.parametrize("example", list(tracking.EXAMPLES))
@pytest.mark.parametrize("return_code", [0, 1])
def test_examples_receive_real_wrapper_id_and_retain_failure_artifacts(tmp_path, example, return_code):
    args = tracking.parse_args(["--example", example, "--python", sys.executable,
                                "--output", str(tmp_path), "--tracking-uri", "unit-test-uri"])
    client = Client()
    def child(command, **kwargs):
        option = tracking.EXAMPLES[example][2]
        assert command[command.index(option) + 1] == "unit-test-run"
        if example == "rotating-reaction":
            assert command[command.index("--experiment-name") + 1] == tracking.EXAMPLES[example][1]
        assert kwargs["cwd"] == tracking.PROJECT / "numerical" / example
        return subprocess.CompletedProcess(command, return_code, stdout="out", stderr="diagnostics")
    result = tracking.execute(args, client=client, process_runner=child)
    expected = "FINISHED" if return_code == 0 else "FAILED"
    assert result["status"] == expected
    assert result["run_id"] == "unit-test-run"
    assert ("terminated", expected) in client.events
    assert (tmp_path / "engine_stderr.log").read_text() == "diagnostics"
    assert json.loads((tmp_path / "tracking_result.json").read_text()) == result


def test_nonempty_output_preserved_before_creating_example_run(tmp_path):
    (tmp_path / "original.json").write_text("retained")
    args = tracking.parse_args(["--example", "reaction-zero", "--python", sys.executable,
                                "--output", str(tmp_path), "--tracking-uri", "unit-test-uri"])
    client = Client()
    with pytest.raises(FileExistsError):
        tracking.execute(args, client=client)
    assert client.events == []
    assert (tmp_path / "original.json").read_text() == "retained"
