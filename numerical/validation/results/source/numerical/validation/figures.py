"""Standalone publication figure from recorded numerical results; no experiment is run."""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import os
from pathlib import Path


def finite_rows(rows, *keys):
    return [r for r in rows if all(isinstance(r.get(k), (int, float))
            and not isinstance(r[k], bool) and math.isfinite(r[k]) for k in keys)]


def create_figure(results: str | Path, output: str | Path) -> list[Path]:
    data = json.loads(Path(results).read_text())
    if not data.get("metadata", {}).get("complete", False):
        raise ValueError("results do not contain a complete recorded computation")
    analytic = finite_rows(data.get("analytic", []), "epsilon", "angle_exponent", "exact_action")
    comparison = data.get("comparisons", [])
    rotating = finite_rows([r for r in comparison if r.get("family") == "rotating_temporal_sdp"],
                           "epsilon", "theta", "nt", "action", "exact_action")
    transport = finite_rows([r for r in comparison if r.get("family") == "large_transport"],
                            "transport_scale", "action", "continuum_upper_bound")
    if not analytic or not rotating or not transport:
        raise ValueError("recorded data for all three figure panels are required")
    os.environ.setdefault("MPLCONFIGDIR", "/tmp/matrix-transport-validation-matplotlib")
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.size": 18, "axes.labelsize": 18, "legend.fontsize": 14,
                         "pdf.fonttype": 42, "ps.fonttype": 42})
    fig, axes = plt.subplots(1, 3, figsize=(13.5, 5.5), constrained_layout=True)
    target = 2 * (math.sqrt(2) - 1) ** 2
    for exponent in sorted({r["angle_exponent"] for r in analytic}, reverse=True):
        rows = sorted([r for r in analytic if r["angle_exponent"] == exponent], key=lambda r: r["epsilon"])
        axes[0].plot([r["epsilon"] for r in rows], [r["exact_action"] for r in rows], "o-",
                     label=rf"$\theta=\varepsilon^{{{exponent:g}}}$")
        bad = [r for r in rows if not r.get("passed", False)]
        if bad:
            axes[0].plot([r["epsilon"] for r in bad], [r["exact_action"] for r in bad], "rx", ms=9)
    axes[0].axhline(target, color="black", ls=":", label=r"$2(\sqrt{2}-1)^2$")
    axes[0].axhline(target + 0.5, color="gray", ls="--", label=r"critical limit $2(\sqrt{2}-1)^2+1/2$")
    axes[0].set(xscale="log", yscale="log", xlabel=r"$\varepsilon$", ylabel="Exact minimum action",
                title="(a) Rotating reaction regimes")
    axes[0].invert_xaxis()
    for epsilon, theta in sorted({(r["epsilon"], r["theta"]) for r in rotating}):
        rows = sorted([r for r in rotating if (r["epsilon"], r["theta"]) == (epsilon, theta)], key=lambda r: r["nt"])
        errors = [abs(r["action"] - r["exact_action"]) for r in rows]
        axes[1].plot([r["nt"] for r in rows], errors, "o-", label=rf"$\varepsilon={epsilon:g},\theta={theta:g}$")
        bad = [(r, e) for r, e in zip(rows, errors) if not r.get("quality_passed", False)]
        if bad:
            axes[1].plot([r["nt"] for r, _ in bad], [e for _, e in bad], "rx", ms=9)
    axes[1].set(xscale="log", yscale="log", xlabel="Time intervals", ylabel=r"$|V_{\rm grid}-V_{\rm exact}|$",
                title="(b) Temporal SDP error")
    rows = sorted(transport, key=lambda r: r["transport_scale"])
    axes[2].plot([r["transport_scale"] for r in rows], [r["action"] for r in rows], "o-", label="SDP grid value")
    axes[2].plot([r["transport_scale"] for r in rows], [r["continuum_upper_bound"] for r in rows], "k--",
                 label=r"continuum upper bound $1/(3t^2)$")
    bad = [r for r in rows if not r.get("quality_passed", False)]
    if bad:
        axes[2].plot([r["transport_scale"] for r in bad], [r["action"] for r in bad], "rx", ms=9)
    axes[2].set(xscale="log", yscale="log", xlabel=r"Transport scale $t$", ylabel="Action",
                title="(c) Large entrywise transport")
    axes[2].text(0.04, 0.05, r"Bures limit $E_H=0$", transform=axes[2].transAxes)
    from matplotlib.ticker import NullFormatter
    time_ticks = sorted({r["nt"] for r in rotating})
    scale_ticks = sorted({r["transport_scale"] for r in transport})
    axes[1].set_xticks(time_ticks, [str(x) for x in time_ticks])
    axes[2].set_xticks(scale_ticks, [f"{x:g}" for x in scale_ticks])
    axes[1].xaxis.set_minor_formatter(NullFormatter())
    axes[2].xaxis.set_minor_formatter(NullFormatter())
    for ax in axes:
        ax.grid(alpha=0.25)
        ax.legend()
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    paths = [output / "theory_comparisons.pdf", output / "theory_comparisons.png"]
    for path in paths:
        if path.exists():
            raise FileExistsError(f"existing figure is preserved: {path}")
    fig.savefig(paths[0], bbox_inches="tight")
    fig.savefig(paths[1], dpi=300, bbox_inches="tight")
    plt.close(fig)
    (output / "figure_source.json").write_text(json.dumps({
        "results": str(Path(results).resolve()),
        "results_sha256": hashlib.sha256(Path(results).read_bytes()).hexdigest(),
        "figure_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "mlflow_run_id": data["metadata"].get("mlflow_run_id"),
        "analytic_records": len(analytic), "rotating_sdp_records": len(rotating),
        "large_transport_records": len(transport),
        "red_crosses": "finite recorded values with failed numerical diagnostics",
        "references": "dashed/dotted lines are proved-theory references, not additional experimental data",
    }, indent=2) + "\n")
    return paths


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(argv)
    print(json.dumps({"figures": [str(p) for p in create_figure(args.input, args.output)]}))


if __name__ == "__main__":
    main()
