"""Optional external MLflow tracking for the retained standalone examples."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

PROJECT = Path(__file__).resolve().parents[1]
EXAMPLES = {
    "reaction-zero": ("numerical.run_experiments", "matrix-transport-reaction-zero", "--mlflow-run-id"),
    "rotating-reaction": ("numerical.experiments", "matrix-transport-rotating-reaction", "--tracking-run-id"),
    "separation": ("numerical.run_demo", "matrix-transport-separation", "--mlflow-run-id"),
}


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--example", choices=EXAMPLES, required=True)
    parser.add_argument("--python", type=Path, required=True, help="numerical-environment Python")
    parser.add_argument("--output", type=Path, required=True, help="new empty output directory")
    parser.add_argument("--tracking-uri", required=True, help="existing MLflow tracking URI")
    return parser.parse_args(argv)


def execute(args, *, client=None, process_runner=subprocess.run):
    output, python = args.output.resolve(), args.python.absolute()
    if not python.is_file():
        raise FileNotFoundError(f"numerical Python does not exist: {python}")
    if output.exists() and any(output.iterdir()):
        raise FileExistsError("choose an empty output directory; existing research artifacts are preserved")
    if client is None:
        from mlflow.tracking import MlflowClient
        client = MlflowClient(tracking_uri=args.tracking_uri)
    module, experiment_name, id_option = EXAMPLES[args.example]
    experiment = client.get_experiment_by_name(experiment_name)
    experiment_id = client.create_experiment(experiment_name) if experiment is None else experiment.experiment_id
    run_id = client.create_run(experiment_id, tags={"mlflow.runName": args.example + "-seed921"}).info.run_id
    command = [str(python), "-m", module, "--output", str(output), id_option, run_id]
    if args.example == "rotating-reaction":
        command += ["--experiment-name", experiment_name]
    record = {"experiment": experiment_name, "run_id": run_id, "status": "FAILED",
              "example": args.example, "command": command, "engine_return_code": None,
              "error": None, "wrapper_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    started = time.perf_counter()
    stdout, stderr = "", ""
    try:
        client.log_param(run_id, "seed", 921)
        client.log_param(run_id, "example", args.example)
        completed = process_runner(command, cwd=PROJECT / "numerical" / args.example,
                                   text=True, capture_output=True)
        stdout, stderr = completed.stdout or "", completed.stderr or ""
        record["engine_return_code"] = completed.returncode
        if completed.returncode == 0:
            record["status"] = "FINISHED"
        else:
            record["error"] = "numerical example returned a nonzero exit code"
    except Exception as error:
        record["error"] = f"{type(error).__name__}: {error}"
    finally:
        output.mkdir(parents=True, exist_ok=True)
        (output / "engine_stdout.log").write_text(stdout)
        (output / "engine_stderr.log").write_text(stderr)
        record["runtime_seconds"] = time.perf_counter() - started
        (output / "tracking_result.json").write_text(json.dumps(record, indent=2) + "\n")
        try:
            client.log_artifacts(run_id, str(output))
        except Exception as error:
            record.update(status="FAILED", error=f"artifact tracking failed: {type(error).__name__}: {error}")
        try:
            client.set_terminated(run_id, status=record["status"])
        except Exception as error:
            record.update(status="FAILED", error=f"tracking termination failed: {type(error).__name__}: {error}")
        (output / "tracking_result.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def main(argv=None):
    record = execute(parse_args(argv))
    print(json.dumps(record))
    return 0 if record["status"] == "FINISHED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
