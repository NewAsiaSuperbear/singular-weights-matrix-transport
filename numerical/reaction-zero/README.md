# Reaction-zero numerical example

From the package root, install the pinned solver dependencies in a project
environment, then run the example from its own directory:

```bash
python3 -m venv .venv-numerics
.venv-numerics/bin/python -m pip install -r numerical/reaction-zero/numerical/requirements.txt
cd numerical/reaction-zero
../../.venv-numerics/bin/python -m numerical.run_experiments --output ../../output/numerical/reaction-zero
../../.venv-numerics/bin/python -m pytest -q tests
```

The entry point requires no tracking server. Optional `--mlflow-run-id` records a
real ID supplied by an external wrapper; omission records null. For automatic
run creation and artifact logging, see [optional tracking](../README.md).

The archived [summary](docs/numerical-data/summary.json),
[metrics](docs/numerical-data/metrics.csv), [full solutions](docs/numerical-data/solutions.json)
and [convergence figure](docs/numerical-data/convergence.pdf) retain their original
metadata. They are numerical evidence rather than certified continuum bounds.
[MODEL.md](numerical/MODEL.md) describes the discrete action and diagnostics.
The reaction-zero theorem is in the manuscript's
[convergent and singular weights section](../../manuscript/sections/finite_weights.tex).

Open [the offline explorer](docs/numerical.html) in a browser. To rebuild it from
the supplied unchanged arrays, run `python -m numerical.render_demo` from this
directory. This renders existing data and performs no scientific computation.
The optional browser checks need `numerical/browser-requirements.txt` and a
Playwright Chromium installation; run `python tests/check_browser.py` here.
