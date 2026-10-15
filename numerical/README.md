# Numerical reproduction

The [main validation engine](validation/README.md) reproduces the manuscript's
numerical comparisons. The retained examples provide additional illustrations:

| Example | Entry point and dependencies | Evidence |
|---|---|---|
| [Reaction zero](reaction-zero/README.md) | Finite-volume matrix SDP; CVXPY and Clarabel | Full fields, residuals, time and mesh refinement, offline HTML |
| [Rotating reaction](rotating-reaction/README.md) | Analytic formulas and optimal paths; NumPy | Actions, full paths and consistency checks |
| [Model separation](separation/README.md) | Floating-point quadrature; NumPy and Plotly | Feasible-path bounds, certificate bounds and interactive plot |

All computation entry points work without MLflow. Omitted run IDs are recorded
as null. The fixed seed is 921, and source hashes accompany results even when a
source ZIP has no Git metadata. Null Git commit/branch/dirty fields mean unknown
provenance; they do not claim a clean committed tree.

Keep the supplied result directories and their source snapshots intact. Use new
output directories for new runs. Historical source snapshots describe the code
that actually produced those results, and may differ from corrected current code.

Optional tracking uses [requirements-tracking.txt](requirements-tracking.txt)
in a separate environment. See [the validation README](validation/README.md)
for a portable MLflow server setup. To track any retained example, from the
package root run:

```bash
.venv-tracking/bin/python numerical/track_example.py \
  --example rotating-reaction --python .venv-numerics/bin/python \
  --output output/numerical/rotating-reaction --tracking-uri http://127.0.0.1:5000
```

Choose `reaction-zero`, `rotating-reaction`, or `separation` for `--example`.
The wrapper creates the real run, supplies its ID, saves stdout/stderr, uploads
all output artifacts and prints the experiment name and run ID. Engine failures
are retained as failed tracked runs. The wrapper does not start a server.
