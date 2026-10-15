# Rotating-reaction numerical example

From the package root, use the numerical environment (or create it with
`python3 -m venv .venv-numerics`), then run:

```bash
.venv-numerics/bin/python -m pip install -r numerical/rotating-reaction/numerical/requirements.txt
cd numerical/rotating-reaction
../../.venv-numerics/bin/python -m numerical.experiments --output ../../output/numerical/rotating-reaction
../../.venv-numerics/bin/python -m pytest -q tests
```

This evaluates analytic formulas and actual optimal paths; it does not solve an
SDP. No tracking server is required. Optional `--tracking-run-id` and
`--experiment-name` must be supplied together and identify an actual external
run; omitted values are null. See [optional tracking](../README.md) for a wrapper
that creates the run and logs the output.

The archived [results](docs/numerical-data/results.json) and
[summary](docs/numerical-data/summary.csv) retain the original run metadata and
source snapshots. Current formulas refer to the manuscript's
[pure-reaction proof](../../manuscript/sections/bures.tex) and
[rotating-family proposition](../../manuscript/sections/examples.tex).
Floating-point consistency diagnostics are not new theorem certificates.
