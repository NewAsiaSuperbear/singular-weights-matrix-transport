"""Optional MLflow wrapper: run with a separate environment containing mlflow.

python numerical/track_experiment.py --python .venv-numerics/bin/python
"""
from pathlib import Path
import argparse
import json
import subprocess
import mlflow

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser();parser.add_argument("--python",required=True)
parser.add_argument("--tracking-uri",default="http://127.0.0.1:5000")
args=parser.parse_args()
mlflow.set_tracking_uri(args.tracking_uri)
mlflow.set_experiment("matrix-transport-reaction-zero")
with mlflow.start_run(run_name="matrix-SDP-reaction-zero-tol1e-10-seed0921") as run:
    run_id=run.info.run_id
    print("MLflow run:",run_id,flush=True)
    mlflow.log_params({"seed":921,"seed_display":"0921","nx":16,"nt":16,
                       "solver":"CLARABEL","tolerance":1e-10,"method":"staggered-PSD-SDP"})
    source=(ROOT/"numerical").glob("*.py")
    for path in source:mlflow.log_artifact(str(path),artifact_path="source")
    mlflow.log_artifact(str(ROOT/"numerical/requirements.txt"),artifact_path="source")
    for name,cmd in [("git.commit",["rev-parse","HEAD"]),("git.branch",["branch","--show-current"]),
                     ("git.dirty",["status","--porcelain"])]:
        value=subprocess.check_output(["git",*cmd],cwd=ROOT,text=True).strip()
        mlflow.set_tag(name,str(bool(value)) if name=="git.dirty" else value)
    output=ROOT/"docs/numerical-data"
    try:
        subprocess.run([args.python,"-m","numerical.run_experiments","--mlflow-run-id",run_id,"--output",str(output)],cwd=ROOT,check=True)
        summary=json.loads((output/"summary.json").read_text())
        mlflow.log_metrics(summary["metrics"])
        mlflow.set_tag("interpretation","Discrete evidence; continuum theorem checked separately with Lean/Nanoda")
        mlflow.log_dict(summary["metadata"],"provenance.json")
        mlflow.log_artifacts(str(output),artifact_path="results")
    except Exception:
        mlflow.set_tag("experiment_status","failed")
        raise
    mlflow.set_tag("experiment_status","completed")
    print("Completed MLflow run:",run_id,flush=True)
