# Smooth model-separation numerical example

From the package root, use the numerical environment (or create it with
`python3 -m venv .venv-numerics`), then run:

```bash
.venv-numerics/bin/python -m pip install -r numerical/separation/numerical/requirements.txt
cd numerical/separation
../../.venv-numerics/bin/python -m numerical.run_demo --output ../../output/numerical/separation
../../.venv-numerics/bin/python -m pytest -q numerical
```

The CLI reads [experiment_config.json](numerical/experiment_config.json) by
default. It requires no tracking server. Optional `--mlflow-run-id` records an
actual externally created run; omitted IDs are null. See
[optional tracking](../README.md) for automatic run creation and logging.

The output includes quadrature values and refinement errors, test-function
coefficients, the configuration, checks, source hashes, static figures and the
self-contained `interactive_separation.html`. Plotly is included in the pinned
dependencies, so the interactive output works offline. Git state is detected
when available; source ZIPs record null commit/branch/dirty values. An optional
`--git-provenance` may supply a real external source-state record.

The full model and Kantorovich--Bures curves are feasible-path upper bounds and
dual-certificate lower bounds in the Li-Zou normalization, not computed optimal
distances. Floating-point quadrature is not interval certification. The smooth
exponential bump is a concrete instance of the mechanism in the manuscript's
[separation proof](../../manuscript/sections/separation.tex).
