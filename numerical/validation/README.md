# Matrix transport numerical comparisons

The engine compares the existing weighted SDP with the exact rotating-reaction
Bures formula, the reaction-free reference on the same grid, and the large
entrywise-transport estimate. It uses seed 921; all configured computations are
deterministic. The original solver tolerances and returned data are preserved.

The default design contains nine spectral Bures/explicit-path checks, two SPD
rotating reaction weights at 8, 16, and 32 time intervals, a balanced reference
and three finite reaction weights on one fixed grid, and transport scales 1, 2,
and 4. Identical solves are reused and identified. The nonuniform endpoint
profiles are positive definite, have equal total matrix I, and each have hub
moment 1/6 about x=1/2. Their continuum upper bound is 1/(3 t²).

Use the existing numerical environment or create a project virtual environment.
From the package root, the standalone entry point requires no tracking server:

```bash
python3 -m venv .venv-numerics
.venv-numerics/bin/python -m pip install -r numerical/validation/requirements.txt
.venv-numerics/bin/python numerical/validation/experiments.py --output output/numerical/validation
```

`--mlflow-run-id` is optional: omitted IDs are recorded as JSON null. The engine
records a supplied ID without creating a run or adding an MLflow dependency.

`results.json` preserves every solver result, including mass, flux, reaction,
statuses, exceptions, feasibility residuals, PSD cone errors, and independent
quadratic costs with range residuals. `summary.csv` records comparisons, signed
differences from analytic values or continuum bounds, and diagnostics.
`metadata.json`, `source_hashes.json`, and copied source files record the exact
code, environment, configuration, and Git state. An existing nonempty output
directory is rejected so earlier results are preserved.

A solver status other than `optimal`, a failed fixed feasibility/objective
check, or an independent path-check failure gives a nonzero exit code. Such
results remain in the artifacts. Grid values are discretizations of the
continuum problem; their differences from continuum bounds are recorded
without interpreting them as proofs or counterexamples. The solver accepts
SPD weights; singular limits are illustrated by positive-weight sequences.

Correctness tests do not execute the scientific sweep or create MLflow runs:

```bash
cd numerical/validation
python -m pytest -q tests
```

Optional tracking uses standard MLflow commands. Install the tracking dependency
in a separate environment and start a server in another terminal (or use an
existing tracking URI). For a local server, run these from the package root:

```bash
python3 -m venv .venv-tracking
.venv-tracking/bin/python -m pip install -r numerical/requirements-tracking.txt
.venv-tracking/bin/mlflow server --backend-store-uri sqlite:///output/mlflow.db \
  --default-artifact-root ./output/mlflow-artifacts --host 127.0.0.1 --port 5000
```

Create `output/` before starting that server. The wrapper uses the server's HTTP
health endpoint; no local service-management scripts are required. Then run:

```bash
.venv-tracking/bin/python numerical/validation/track_experiment.py \
  --python .venv-numerics/bin/python \
  --output output/numerical/validation \
  --tracking-uri http://127.0.0.1:5000
```

The wrapper prints the MLflow experiment name and run ID as JSON. It uploads
artifacts even when the numerical engine fails, and terminates such runs with
status `FAILED`. Missing Git history is recorded as uncommitted source-manifest
provenance, with no claim of a clean committed tree.

After computation, create standalone PDF and PNG figures from its actual data:

```bash
python numerical/validation/figures.py \
  --input output/numerical/validation/results.json \
  --output output/numerical/validation/figures
```

The three panels show rotating reaction regimes, temporal SDP errors, and large
entrywise transport. Red crosses identify finite values whose numerical checks
failed. The theoretical reference lines are labelled separately. The figures
retain their source run ID; they do not trigger another numerical experiment.

Independent rotating-reaction reference values use the already established
2-by-2 trace-square-root Bures formula evaluated with 60-digit standard-library
Decimal arithmetic. Matrix inverses, congruences, determinants, and the final
subtraction use `Decimal.from_float` inputs. This avoids cancellation when the
weighted trace terms are large and the action is small. The original float64
spectral value and its error remain recorded, including their separate failure
flag; the analytic check uses the high-precision reference with the same 1e-7
relative tolerance. Neither solver tolerances nor feasibility checks change.

For the retained numerical examples, run `python -m pytest tests` from each
of reaction-zero and rotating-reaction, and `python -m pytest numerical` from
separation; archived result-source snapshots are outside the active test suite.
See [the numerical index](../README.md) for their independent entry points.
