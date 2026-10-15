# Reproducibility

## Formal verification

The formalization uses Lean `v4.34.0-rc2`, mathlib commit `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, Lean exporter commit `483e011449cce37c3f8ad5e2aae434cbb1d2e53c` and Nanoda commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`.

The [GitHub Actions workflow](../.github/workflows/verify.yml) builds the project, runs the trust-level-zero collector and declaration-type dump, checks manuscript correspondence, exports the selected declarations, and verifies their full dependency closure with Nanoda. It checks 3323 selected project declarations. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.

For a local run, install the pinned Lean toolchain and Rust, then run these commands from the repository root:

```bash
git clone https://github.com/leanprover/lean4export .proof-tools/exporter
git -C .proof-tools/exporter checkout 483e011449cce37c3f8ad5e2aae434cbb1d2e53c
git clone https://github.com/ammkrn/nanoda_lib .proof-tools/checker
git -C .proof-tools/checker checkout 3a2407216ee84a75f9e1aead6803d0578be06ae7
bash verification/check-kernels.sh
```

The source tree must match a Git commit. The output directory defaults to `.verification/` and must be empty. To retain several runs, set `PROOF_OUTPUT_DIR` to a new directory for each run. The output includes `certificate.json`, source and control hashes, complete logs, fresh declaration types and a compressed declaration export.

[kernel-certificate.json](kernel-certificate.json) preserves the recorded baseline kernel evidence for the included proof sources. New CI runs generate certificates for their exact repository commit and controls.

## Manuscript correspondence

The correspondence records contain 797 manuscript assertions, including 741 mathematical assertions, and 79 paragraph units. [STATEMENT_MAP.md](../verification/STATEMENT_MAP.md) describes the principal declarations; [MATHEMATICAL_SCOPE.json](../verification/MATHEMATICAL_SCOPE.json) records additional directly derived passages.

Check stored source and declaration bindings without compiling Lean:

```bash
python3 verification/check_atom_map.py --source-bindings-only
python3 verification/verify_manifest.py --formal-dir formal --mode check
python3 -m unittest discover -s verification/tests -v
```

The full kernel workflow compares these records with a fresh declaration-type dump and checks the exported proof terms independently.

## Numerical results

The [numerical index](../numerical/README.md) gives the experiment entry points and pinned dependencies. Recorded results include full arrays, solver statuses, feasibility residuals, independently evaluated costs and source snapshots. Run metadata identifies the original execution; the snapshots preserve the exact code used to produce those results.

Figure 1 is generated from [results.json](../numerical/validation/results/results.json). Its [source record](../manuscript/figures/figure_source.json) identifies the input hash, rendering script, plotted cases and theoretical references. Rendering the figure reuses the stored data. [numerical-provenance.json](numerical-provenance.json) records the exported metadata and source-snapshot hashes.

## Source inventory

[SOURCE_MANIFEST.json](../SOURCE_MANIFEST.json) contains SHA-256 hashes for the distributed files. The Lean-specific source inventory is [verification/source-hashes.json](../verification/source-hashes.json). The manuscript PDF and all recorded numerical arrays are supplied with the repository.
