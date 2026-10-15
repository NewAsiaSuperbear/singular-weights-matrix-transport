"""External MLflow wrapper for the matrix-transport numerical engine.

Run with the dedicated MLflow Python environment. The child numerical process
keeps its own pinned environment and has no MLflow dependency.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any
from urllib.parse import urlparse

PROJECT = Path(__file__).resolve().parents[2]
ENGINE = Path(__file__).with_name("experiments.py")
EXPERIMENT = "matrix-transport-consolidated-validation"


def finite_metrics(values: dict[str, Any], prefix: str = "") -> dict[str, float]:
    """Only finite numeric scalars enter MLflow metrics; raw artifacts retain other fields."""
    metrics = {}
    for key, value in values.items():
        name = re.sub(r"[^\w.\-/ ]", "_", prefix + str(key))
        if isinstance(value, dict):
            metrics.update(finite_metrics(value, name + "."))
        elif isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value):
            metrics[name] = float(value)
    return metrics


def result_metrics(data: dict[str, Any]) -> dict[str, float]:
    analytic, solves = data.get("analytic", []), data.get("solves", [])
    metrics = {
        "analytic_case_count": float(len(analytic)), "solver_case_count": float(len(solves)),
        "failed_analytic_checks": float(sum(not row.get("passed", False) for row in analytic)),
        "failed_solver_checks": float(sum(not row.get("quality", {}).get("passed", False) for row in solves)),
    }
    metrics.update(finite_metrics(data.get("metadata", {}), "metadata."))
    for index, row in enumerate(analytic):
        metrics.update(finite_metrics(row, f"analytic.{index}."))
    for row in data.get("comparisons", []):
        metrics.update(finite_metrics(row, f"case.{row['case_id']}."))
    return metrics


def source_state() -> dict[str, Any]:
    def read(*args):
        return subprocess.check_output(["git", "-C", str(PROJECT), *args], text=True,
                                       stderr=subprocess.DEVNULL).strip()
    try:
        status = read("status", "--porcelain")
        return {"commit": read("rev-parse", "HEAD"), "branch": read("branch", "--show-current"),
                "dirty": bool(status), "status_porcelain": status, "repository_detected": True}
    except (OSError, subprocess.CalledProcessError):
        return {"commit": None, "branch": None, "dirty": None,
                "status_porcelain": None, "repository_detected": False}


def provenance_tags(state: dict[str, Any]) -> dict[str, str]:
    return {"source.git.commit": state.get("commit") or "uncommitted",
            "source.git.branch": state.get("branch") or "none",
            "source.git.dirty": "unknown-no-git" if state.get("dirty") is None else str(state["dirty"]).lower(),
            "source.provenance": "git-and-source-manifest" if state.get("repository_detected") else "uncommitted-source-manifest",
            "source.manifest": "source_hashes.json"}


def check_tracking_service(uri: str) -> None:
    """Apply the shared local tracking policy before a meaningful local experiment."""
    parsed = urlparse(uri)
    if parsed.hostname not in ("127.0.0.1", "localhost") or parsed.port != 5000:
        return
    status = subprocess.run(["mlflow-status"], text=True, capture_output=True, timeout=20)
    text = status.stdout + status.stderr
    if status.returncode != 0 or "RUNNING" not in text.upper() or "NOT RUNNING" in text.upper():
        started = subprocess.run(["mlflow-start"], text=True, capture_output=True, timeout=45)
        status = subprocess.run(["mlflow-status"], text=True, capture_output=True, timeout=20)
        if started.returncode != 0 or status.returncode != 0 or "RUNNING" not in status.stdout + status.stderr:
            raise RuntimeError("MLflow tracking service is not running: " + status.stdout + status.stderr)


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--python", type=Path, required=True, help="pinned numerical-environment Python")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--tracking-uri", default="http://127.0.0.1:5000")
    parser.add_argument("--seed", type=int, default=921, choices=[921])
    parser.add_argument("--meshes", type=int, nargs="+", default=[8, 16, 32])
    parser.add_argument("--nx", type=int, default=4)
    parser.add_argument("--profile-nt", type=int, default=16)
    parser.add_argument("--tolerance", type=float, default=1e-9)
    return parser.parse_args(argv)


def execute(args, *, client=None, process_runner=subprocess.run) -> dict[str, Any]:
    # Preserve the invoked venv path: dereferencing bin/python loses pyvenv.cfg.
    numerical_python, output = args.python.absolute(), args.output.resolve()
    if not numerical_python.is_file():
        raise FileNotFoundError(f"numerical Python does not exist: {numerical_python}")
    if output.exists() and any(output.iterdir()):
        raise FileExistsError("choose an empty output directory; existing research artifacts are preserved")
    if client is None:
        check_tracking_service(args.tracking_uri)
        from mlflow.tracking import MlflowClient
        client = MlflowClient(tracking_uri=args.tracking_uri)
    experiment = client.get_experiment_by_name(EXPERIMENT)
    experiment_id = client.create_experiment(EXPERIMENT) if experiment is None else experiment.experiment_id
    state = source_state()
    tags = {**provenance_tags(state), "mlflow.runName": "weighted-bures-and-weight-limits-seed921",
            "method": "existing weighted SDP and independent Bures/path evaluation",
            "purpose": "compare weight-limit discretizations with formally proved statements"}
    run_id = client.create_run(experiment_id, tags=tags).info.run_id
    params = {"seed": args.seed, "meshes": json.dumps(args.meshes), "profile_nx": args.nx,
              "profile_nt": args.profile_nt, "solver_tolerance": args.tolerance,
              "solver_max_iter": 300, "numerical_python": str(numerical_python)}
    command = [str(numerical_python), str(ENGINE), "--output", str(output), "--mlflow-run-id", run_id,
               "--seed", str(args.seed), "--meshes", *map(str, args.meshes), "--nx", str(args.nx),
               "--profile-nt", str(args.profile_nt), "--tolerance", str(args.tolerance)]
    started = time.perf_counter()
    summary = {"experiment": EXPERIMENT, "run_id": run_id, "tracking_uri": args.tracking_uri,
               "output": str(output), "status": "FAILED", "engine_return_code": None, "error": None}
    stdout, stderr, data = "", "", None
    try:
        for key, value in params.items():
            client.log_param(run_id, key, value)
        completed = process_runner(command, cwd=PROJECT, text=True, capture_output=True)
        summary["engine_return_code"] = completed.returncode
        stdout, stderr = completed.stdout or "", completed.stderr or ""
        results = output / "results.json"
        if results.exists():
            data = json.loads(results.read_text())
            for key, value in result_metrics(data).items():
                client.log_metric(run_id, key, value)
            for row in data.get("solves", []):
                client.set_tag(run_id, f"case.{row['case_id']}.status", row["result"]["status"])
                client.set_tag(run_id, f"case.{row['case_id']}.quality_passed", str(row["quality"]["passed"]).lower())
        complete = data is not None and data["metadata"].get("complete", False)
        valid = complete and data["metadata"].get("source_unchanged", False) and data["metadata"].get("all_quality_passed", False)
        if completed.returncode == 0 and valid:
            summary["status"] = "FINISHED"
        else:
            summary["error"] = "numerical engine failed or one or more recorded checks did not pass"
    except Exception as error:
        summary["error"] = f"{type(error).__name__}: {error}"
    finally:
        output.mkdir(parents=True, exist_ok=True)
        (output / "engine_stdout.log").write_text(stdout)
        (output / "engine_stderr.log").write_text(stderr)
        hashes = {}
        for source in (Path(__file__), Path(__file__).with_name("figures.py")):
            if source.exists():
                relative = str(source.relative_to(PROJECT))
                hashes[relative] = hashlib.sha256(source.read_bytes()).hexdigest()
                destination = output / "source" / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, destination)
        (output / "orchestration_source_hashes.json").write_text(json.dumps(hashes, indent=2) + "\n")
        summary["runtime_seconds"] = time.perf_counter() - started
        record = {**summary, "command": command, "configuration": params, "source": state,
                  "finished_utc": datetime.now(timezone.utc).isoformat(), "orchestration_sha256": hashes}
        (output / "tracking_metadata.json").write_text(json.dumps(record, indent=2) + "\n")
        try:
            client.log_metric(run_id, "wrapper.runtime_seconds", summary["runtime_seconds"])
            client.set_tag(run_id, "engine.return_code", str(summary["engine_return_code"]))
            if summary["error"]:
                client.set_tag(run_id, "failure.reason", summary["error"][:4000])
            client.log_artifacts(run_id, str(output))
        except Exception as error:
            summary["status"] = "FAILED"
            summary["error"] = f"artifact/metadata tracking failed: {type(error).__name__}: {error}"
        record.update(summary)
        (output / "tracking_metadata.json").write_text(json.dumps(record, indent=2) + "\n")
        (output / "tracking_result.json").write_text(json.dumps(summary, indent=2) + "\n")
        try:
            client.log_artifact(run_id, str(output / "tracking_result.json"))
            client.log_artifact(run_id, str(output / "tracking_metadata.json"))
        except Exception as error:
            summary["status"] = "FAILED"
            summary["error"] = f"final status tracking failed: {type(error).__name__}: {error}"
        try:
            client.set_terminated(run_id, status=summary["status"])
            summary["tracking_termination_recorded"] = True
        except Exception as error:
            summary["status"] = "FAILED"
            summary["tracking_termination_recorded"] = False
            summary["error"] = f"run termination tracking failed: {type(error).__name__}: {error}"
        (output / "tracking_result.json").write_text(json.dumps(summary, indent=2) + "\n")

    return summary


def main(argv=None) -> int:
    summary = execute(parse_args(argv))
    print(json.dumps(summary))
    return 0 if summary["status"] == "FINISHED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
