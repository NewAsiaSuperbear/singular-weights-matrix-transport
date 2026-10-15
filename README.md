# Singular weights and operator dependence in matrix-valued transport

**Weiyan WU**

[Paper (PDF)](paper.pdf) · [LaTeX source](manuscript/main.tex) · [Lean proofs](formal/) · [Numerical experiments](numerical/) · [Verification](reproducibility/README.md)

This repository accompanies the paper *Singular weights and operator dependence in matrix-valued transport*. It contains the mathematical formalization, numerical implementations, recorded results and manuscript sources.

The paper studies convergent and singular transport and reaction weights, large-transport limits, weighted Bures formulas, rotating examples and dependence on the transport operator.

| Directory | Contents |
|---|---|
| `manuscript/` | LaTeX source, bibliography and publication figure |
| `formal/` | Lean 4 formalization and pinned mathlib dependency |
| `numerical/validation/` | Main SDP implementation, tests and recorded comparisons |
| `numerical/reaction-zero/` | Reaction-zero example and saved numerical solutions |
| `numerical/rotating-reaction/` | Exact rotating-reaction formulas, paths and figures |
| `numerical/separation/` | Smooth model-separation example |
| `verification/` | Declaration inventories, manuscript correspondence and kernel checks |
| `reproducibility/` | Verification instructions and recorded scientific provenance |

## Build the paper

With a TeX distribution containing `latexmk` and pdfLaTeX:

```bash
cd manuscript
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The supplied [paper.pdf](paper.pdf) has 24 pages. Figure 1 appears on page 22.

## Build the Lean formalization

Install [elan](https://github.com/leanprover/elan), then run:

```bash
cd formal
lake exe cache get
lake build MatrixTransport MatrixTransport.Paper
```

The project pins Lean `v4.34.0-rc2` and mathlib commit `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. The correspondence between the manuscript and Lean declarations is described in [STATEMENT_MAP.md](verification/STATEMENT_MAP.md).

## Run the numerical examples

From the repository root:

```bash
python3 -m venv .venv-numerics
.venv-numerics/bin/python -m pip install -r numerical/validation/requirements.txt
.venv-numerics/bin/python numerical/validation/experiments.py \
  --output output/numerical/validation
```

Saved results are available in [numerical/validation/results/](numerical/validation/results/). Regenerate Figure 1 directly from these results:

```bash
.venv-numerics/bin/python numerical/validation/figures.py \
  --input numerical/validation/results/results.json \
  --output output/figures
```

Run the numerical correctness tests with:

```bash
cd numerical/validation
../../.venv-numerics/bin/python -m pytest -q tests
```

See the [numerical index](numerical/README.md) for the other examples and optional experiment tracking. Saved numerical arrays, solver diagnostics and execution-source snapshots are included for reproducibility.

## Continuous integration

The [Lean and Nanoda workflow](.github/workflows/verify.yml) runs on pushes to `main`, pull requests and manual dispatch. It builds the formalization, checks all selected declarations with Lean at trust level zero, compares fresh declaration types with the manuscript correspondence, and independently checks the complete exported dependency closure with Nanoda. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.

Each run uploads its kernel certificate, complete verification logs and compressed declaration export as a GitHub Actions artifact. The [verification instructions](reproducibility/README.md) give the commands for local reproduction.

## Citation and licenses

Please cite the accompanying paper; citation metadata is in [CITATION.cff](CITATION.cff). Software is licensed under [MIT](LICENSE). The paper, original figures and numerical datasets are licensed under [CC BY 4.0](LICENSE-PAPER.md). Third-party material retains its original terms.
