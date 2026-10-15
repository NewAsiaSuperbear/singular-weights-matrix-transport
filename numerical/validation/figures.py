"""Standalone publication figure from recorded numerical results; no experiment is run."""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import os
from fractions import Fraction
from pathlib import Path

V_STAR = 2 * (math.sqrt(2) - 1) ** 2
EXACT_COLOR = "#1f4e79"
CASE_COLORS = ("#1f4e79", "#c0392b")
REFERENCE_COLOR = "0.15"


def finite_rows(rows, *keys):
    return [r for r in rows if all(isinstance(r.get(k), (int, float))
            and not isinstance(r[k], bool) and math.isfinite(r[k]) for k in keys)]


def mark_failed(ax, xs, ys, passed):
    bad = [(x, y) for x, y, ok in zip(xs, ys, passed) if not ok]
    if bad:
        ax.plot([x for x, _ in bad], [y for _, y in bad], "x", color="red", ms=5, mew=1.0, zorder=6)


def line_angle(ax, xs, ys):
    (x0, y0), (x1, y1) = ax.transData.transform([(xs[0], ys[0]), (xs[-1], ys[-1])])
    return math.degrees(math.atan2(y1 - y0, x1 - x0))


def regime_facets(axes, analytic):
    from matplotlib.ticker import MaxNLocator, NullLocator
    exponents = sorted({r["angle_exponent"] for r in analytic}, reverse=True)
    if len(exponents) != len(axes):
        raise ValueError("panel (a) needs exactly one facet per recorded angle exponent")
    for index, (ax, exponent) in enumerate(zip(axes, exponents)):
        rows = sorted([r for r in analytic if r["angle_exponent"] == exponent], key=lambda r: r["epsilon"])
        eps = [r["epsilon"] for r in rows]
        values = [r["exact_action"] for r in rows]
        power = Fraction(exponent).limit_denominator(16)
        regime = rf"$\theta=\varepsilon^{{{power.numerator}/{power.denominator}}}$"
        ax.plot(eps, values, "o-", color=EXACT_COLOR, ms=3.6, lw=1.0, zorder=3)
        mark_failed(ax, eps, values, [r.get("passed", False) for r in rows])
        if exponent > 0.5 or math.isclose(exponent, 0.5):
            critical = math.isclose(exponent, 0.5)
            limit = V_STAR + 0.5 if critical else V_STAR
            label = r"$V_*+1/2$" if critical else r"$V_*=2(\sqrt{2}-1)^2$"
            ax.axhline(limit, color=REFERENCE_COLOR, ls="--", lw=0.9, zorder=2)
            ax.annotate(label, xy=(1, limit), xycoords=("axes fraction", "data"), xytext=(-3, -3.5),
                        textcoords="offset points", ha="right", va="top", fontsize=7.5)
            low, high = min(values + [limit]), max(values + [limit])
            ax.set_ylim(low - 0.32 * (high - low), high + 0.1 * (high - low))
            ax.yaxis.set_major_locator(MaxNLocator(nbins=6, steps=[1, 2, 5, 10]))
            ax.ticklabel_format(axis="y", style="plain", useOffset=False)
            title = rf"{regime}: $V\to V_*+1/2$" if critical else rf"{regime}: $V\to V_*$"
            scale = "linear"
        else:
            asymptote = [r["theta"] ** 4 / (2 * r["epsilon"] ** 2) for r in rows]
            ax.plot(eps, asymptote, ls="--", color=REFERENCE_COLOR, lw=0.9, zorder=2)
            ax.set_yscale("log")
            ax.set_ylim(min(values) / 2.5, max(asymptote) * 4)
            ax.annotate(r"$V\sim\theta^4/(2\varepsilon^2)$", xy=(eps[0], asymptote[0]), xytext=(-6, 2),
                        textcoords="offset points", ha="right", va="bottom", fontsize=7.5)
            title = rf"{regime}: $V\to\infty$"
            scale = "log scale"
        ax.set_xscale("log")
        ax.set_xlim(max(eps) * 1.6, min(eps) / 1.6)
        ax.set_xticks(eps)
        ax.xaxis.set_minor_locator(NullLocator())
        ax.set_xlabel(r"$\varepsilon$")
        ax.set_ylabel(("Exact action $V$" if index == 0 else "$V$") + f", {scale}")
        ax.set_title(("(a)  " if index == 0 else "") + title, loc="left")
        ax.grid(alpha=0.25, which="major")


def refinement_panel(ax, rotating):
    from matplotlib.ticker import NullLocator
    cases = sorted({(r["epsilon"], r["theta"]) for r in rotating}, reverse=True)
    styles = (dict(marker="o", ms=6.5, mfc="white", mew=1.0, ls="-", lw=1.3),
              dict(marker="s", ms=2.6, ls=(0, (3.0, 1.6)), lw=1.0))
    observed, all_errors, all_nt = [], [], set()
    for index, (epsilon, theta) in enumerate(cases):
        rows = sorted([r for r in rotating if (r["epsilon"], r["theta"]) == (epsilon, theta)],
                      key=lambda r: r["nt"])
        nts = [r["nt"] for r in rows]
        errors = [abs(r["action"] - r["exact_action"]) for r in rows]
        ax.plot(nts, errors, color=CASE_COLORS[index % 2], zorder=3 + index, **styles[index % 2],
                label=rf"$(\varepsilon,\theta)=({epsilon:g},{theta:g})$")
        mark_failed(ax, nts, errors, [r.get("quality_passed", False) for r in rows])
        ratios = [e0 / e1 for n0, n1, e0, e1 in zip(nts, nts[1:], errors, errors[1:])
                  if n1 == 2 * n0 and e1 > 0]
        observed.append({"epsilon": epsilon, "theta": theta, "nt": nts, "error_ratios": ratios})
        all_errors += errors
        all_nt.update(nts)
    ticks = sorted(all_nt)
    ax.set_xscale("log", base=2)
    ax.set_xlim(ticks[0] / 1.3, ticks[-1] * 1.3)
    ax.set_xticks(ticks, [str(n) for n in ticks])
    ax.xaxis.set_minor_locator(NullLocator())
    ax.set_yscale("log")
    ax.set_ylim(min(all_errors) / 2, max(all_errors) * 2.2)
    ax.set(xlabel=r"Time intervals $N_t$", ylabel=r"$|V_{\rm grid}-V_{\rm exact}|$")
    nx = sorted({r["nx"] for r in rotating if "nx" in r})
    ax.set_title("(b) Temporal SDP error" + (rf", $N_x={nx[0]}$" if len(nx) == 1 else ""), loc="left")
    ax.legend(loc="upper right", frameon=False, handlelength=2.6, borderaxespad=0.3, labelspacing=0.35)
    ratios = [q for case in observed for q in case["error_ratios"]]
    if ratios:
        ax.text(0.04, 0.05, "Observed error ratio at each\n"
                + rf"doubling of $N_t$: {min(ratios):.3f}–{max(ratios):.3f}",
                transform=ax.transAxes, ha="left", va="bottom", fontsize=7)
    ax.grid(alpha=0.25, which="major")
    return observed


def transport_panel(ax, zero_ax, transport):
    from matplotlib.ticker import NullLocator
    rows = sorted(transport, key=lambda r: r["transport_scale"])
    if {r.get("hub_limit") for r in rows} != {0.0}:
        raise ValueError("panel (c) zero strip represents the recorded Bures limit E_H=0")
    scales = [r["transport_scale"] for r in rows]
    values = [r["action"] for r in rows]
    bound = [r["continuum_upper_bound"] for r in rows]
    ax.plot(scales, bound, ls="--", color=REFERENCE_COLOR, lw=1.0, zorder=2)
    ax.plot(scales, values, "o-", color=EXACT_COLOR, ms=4.0, lw=1.1, zorder=3)
    mark_failed(ax, scales, values, [r.get("quality_passed", False) for r in rows])
    ax.set_xscale("log")
    ax.set_xlim(scales[0] / 1.18, scales[-1] * 1.18)
    ax.set_yscale("log")
    ax.set_ylim(min(values) / 2.4, max(bound) * 4)
    grid = sorted({(r.get("nx"), r.get("nt")) for r in rows})
    sdp_label = "SDP grid values" + (rf" ($N_x={grid[0][0]}$, $N_t={grid[0][1]}$)" if len(grid) == 1 else "")
    middle = len(rows) // 2
    for ys, text in ((bound, r"continuum upper bound $1/(3t^2)$"), (values, sdp_label)):
        ax.annotate(text, xy=(scales[middle], ys[middle]), xytext=(0, 3.5), textcoords="offset points",
                    ha="center", va="bottom", rotation=line_angle(ax, scales, ys),
                    rotation_mode="anchor", fontsize=7.5)
    zero_ax.axhline(0.0, color=REFERENCE_COLOR, ls=":", lw=1.3)
    zero_ax.set_ylim(-0.7, 1.3)
    zero_ax.set_yticks([0.0], ["0"])
    zero_ax.yaxis.set_minor_locator(NullLocator())
    zero_ax.text(0.02, 0.64, r"$E_H=0$: continuum lower bound and $t\to\infty$ limit",
                 transform=zero_ax.transAxes, ha="left", va="center", fontsize=7)
    ax.spines["bottom"].set_visible(False)
    zero_ax.spines["top"].set_visible(False)
    ax.tick_params(axis="x", which="both", bottom=False, labelbottom=False)
    zero_ax.set_xticks(scales, [f"{s:g}" for s in scales])
    zero_ax.xaxis.set_minor_locator(NullLocator())
    zero_ax.set_xlabel(r"Transport scale $t$")
    ax.set_ylabel("Action")
    ax.set_title("(c) Large entrywise transport", loc="left")
    ax.grid(alpha=0.25, which="major")
    zero_ax.grid(alpha=0.25, axis="x")
    marks = dict(marker=[(-1, -0.5), (1, 0.5)], markersize=5, linestyle="none", color="k",
                 mec="k", mew=0.6, clip_on=False)
    ax.plot([0, 1], [0, 0], transform=ax.transAxes, **marks)
    zero_ax.plot([0, 1], [1, 1], transform=zero_ax.transAxes, **marks)


def create_figure(results: str | Path, output: str | Path) -> list[Path]:
    data = json.loads(Path(results).read_text())
    if not data.get("metadata", {}).get("complete", False):
        raise ValueError("results do not contain a complete recorded computation")
    analytic = finite_rows(data.get("analytic", []), "epsilon", "angle_exponent", "theta", "exact_action")
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
    plt.rcParams.update({"font.size": 8, "axes.labelsize": 8, "axes.titlesize": 8,
                         "xtick.labelsize": 7.5, "ytick.labelsize": 7.5, "legend.fontsize": 7,
                         "lines.linewidth": 1.1, "lines.markersize": 3.5, "axes.linewidth": 0.6,
                         "grid.linewidth": 0.5, "xtick.major.width": 0.6, "ytick.major.width": 0.6,
                         "xtick.minor.width": 0.5, "ytick.minor.width": 0.5, "axes.titlepad": 4.0,
                         "pdf.fonttype": 42, "ps.fonttype": 42})
    fig = plt.figure(figsize=(154 / 25.4, 112 / 25.4))
    outer = fig.add_gridspec(2, 1, height_ratios=(1, 1.25), left=0.085, right=0.985,
                             top=0.95, bottom=0.075, hspace=0.42)
    top = outer[0].subgridspec(1, 3, wspace=0.50)
    bottom = outer[1].subgridspec(1, 2, wspace=0.26)
    transport_grid = bottom[0, 1].subgridspec(2, 1, height_ratios=(1, 0.24), hspace=0.06)
    regime_facets([fig.add_subplot(top[0, column]) for column in range(3)], analytic)
    observed = refinement_panel(fig.add_subplot(bottom[0, 0]), rotating)
    transport_ax = fig.add_subplot(transport_grid[0])
    transport_panel(transport_ax, fig.add_subplot(transport_grid[1], sharex=transport_ax), transport)
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    paths = [output / "theory_comparisons.pdf", output / "theory_comparisons.png"]
    for path in paths:
        if path.exists():
            raise FileExistsError(f"existing figure is preserved: {path}")
    fig.savefig(paths[0], bbox_inches="tight", pad_inches=0.02)
    fig.savefig(paths[1], dpi=300, bbox_inches="tight", pad_inches=0.02)
    plt.close(fig)
    (output / "figure_source.json").write_text(json.dumps({
        "results": str(Path(results).resolve()),
        "results_sha256": hashlib.sha256(Path(results).read_bytes()).hexdigest(),
        "figure_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "mlflow_run_id": data["metadata"].get("mlflow_run_id"),
        "matplotlib_version": matplotlib.__version__,
        "analytic_records": len(analytic), "rotating_sdp_records": len(rotating),
        "large_transport_records": len(transport),
        "red_crosses": "finite recorded values with failed numerical diagnostics",
        "references": "proved-theory references, not data: panel (a) dashed V_*, V_*+1/2 and the "
                      "Proposition 7.1 asymptotic reference theta^4/(2 epsilon^2); panel (c) dashed "
                      "continuum upper bound 1/(3t^2) and dotted E_H=0 on the zero strip. Panel (b) has "
                      "no theoretical reference: its solid and dashed lines join recorded errors of the "
                      "two configurations",
        "panel_a": "exact_action per angle_exponent facet; linear ordinate for the two bounded regimes, "
                   "logarithmic for the divergent regime; theta^4/(2 epsilon^2) from recorded theta, epsilon",
        "panel_b": "|action - exact_action| for both recorded cases on shared log-log axes, without offsets",
        "observed_refinement_ratios": observed,
        "panel_c": "action and continuum_upper_bound on a logarithmic axis; recorded hub_limit E_H=0 "
                   "on a separate linear zero strip below an axis break",
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
