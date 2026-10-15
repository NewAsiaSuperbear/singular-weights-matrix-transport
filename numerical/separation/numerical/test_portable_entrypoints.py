"""Portable CLI contracts; the quadrature study is not executed."""
import subprocess

from numerical import run_demo


def test_default_cli_does_not_require_tracking():
    args = run_demo.parse_args([])
    assert args.mlflow_run_id is None
    assert args.git_provenance is None


def test_no_git_metadata_is_unknown(monkeypatch):
    def unavailable(*args, **kwargs):
        raise subprocess.CalledProcessError(128, "git")
    monkeypatch.setattr(run_demo.subprocess, "check_output", unavailable)
    state = run_demo.git_state()
    assert state == {"repository_detected": False, "commit": None, "branch": None,
                     "dirty": None, "status_porcelain": None}
