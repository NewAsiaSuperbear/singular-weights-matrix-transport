"""Quadrature refinement and portable visualizations of transport bounds.

Tracking is optional; an external wrapper may supply its real run ID. Optimal
distances are not computed. Bounds use Li-Zou WB normalization.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import time

import numpy as np

from numerical.transport_demo import (
    analytic_rho_bound,
    disk_grid,
    frequency_result,
    test_function_coefficients,
    wave_fields,
)

PROJECT = Path(__file__).resolve().parents[1]
CAPTION = (
    "Concrete numerical illustration of the same mechanism; the exponential bump is not "
    "Lean's noncomputable choice. Curves are bounds, not optimal distances. Floating-point "
    "quadrature is not interval certification. Li-Zou WB normalization; BV d_KB² = 2 B_KB²."
)
POSITIVE_FIELDS = (
    "full_path_upper", "reaction_path_upper", "beta_ibp", "beta_direct",
    "kb_certificate_lower", "full_generic_upper", "bump_mass", "bump_squared_mass",
)
PAIRING_FIELDS = tuple(f"pairing_{i}" for i in range(6))


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False, allow_nan=False) + "\n")


def write_csv(path, rows):
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def source_hashes():
    return {
        str(path.relative_to(PROJECT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted((PROJECT / "numerical").glob("*.py"))
    }


def git_state():
    def read(*args):
        return subprocess.check_output(["git", "-C", str(PROJECT), *args], text=True,
                                       stderr=subprocess.DEVNULL).strip()
    try:
        status = read("status", "--porcelain")
        return {"repository_detected": True, "commit": read("rev-parse", "HEAD"),
                "branch": read("branch", "--show-current"), "dirty": bool(status),
                "status_porcelain": status}
    except (OSError, subprocess.CalledProcessError):
        return {"repository_detected": False, "commit": None, "branch": None,
                "dirty": None, "status_porcelain": None}


def evaluate(config):
    coeffs = test_function_coefficients(config["seed"], config["test_count"])
    results = []
    for level, (nr, ntheta) in enumerate(config["quadrature_levels"]):
        grid = disk_grid(config["radius"], nr, ntheta)
        for j in config["frequencies"]:
            result = frequency_result(j, grid, config["epsilon"], coeffs)
            result.update(level=level, radial_nodes=nr, angular_nodes=ntheta)
            s = result["certificate_s"]
            # For Phi=(s cos(kx)-s²t)E the only nonzero HJ eigenvalue is
            # -s² + .5*(s cos(kx)-s²t)²; its displayed analytic upper bound
            # follows from |cos|<=1 and 0<=t<=1.
            result["hj_scalar_upper_analytic"] = -s**2 + 0.5 * (s + s**2) ** 2
            sample_x = np.linspace(-1.0, 1.0, 2049)
            sample_t = np.linspace(0.0, 1.0, 33)
            phi = s * np.cos(2 * np.pi * j * sample_x[None, :]) - s**2 * sample_t[:, None]
            result["hj_scalar_max_sampled"] = float(np.max(-s**2 + 0.5 * phi**2))
            results.append(result)
    return coeffs, results


def refinement_and_checks(config, results):
    fine_level = len(config["quadrature_levels"]) - 1
    lookup = {(row["level"], row["j"]): row for row in results}
    fine = [lookup[(fine_level, j)] for j in config["frequencies"]]
    refinement = []
    for level in range(fine_level):
        for j in config["frequencies"]:
            row, reference = lookup[(level, j)], lookup[(fine_level, j)]
            for field in POSITIVE_FIELDS + ("mass_perturbation",) + PAIRING_FIELDS:
                absolute = abs(row[field] - reference[field])
                denominator = max(abs(row[field]), abs(reference[field]), 1e-12)
                relative = absolute / denominator
                refinement.append({
                    "level": level, "reference_level": fine_level, "j": j,
                    "field": field, "absolute_difference": absolute,
                    "relative_difference_with_1e_minus12_floor": relative,
                })
    identity_tol = config["identity_absolute_tolerance"]
    bound_tol = config["bounds_absolute_tolerance"]
    abs_tol = config["refinement_absolute_tolerance"]
    rel_tol = config["refinement_relative_tolerance"]
    core_refinement = [r for r in refinement if r["field"] in POSITIVE_FIELDS]
    checks = {
        "all_values_finite": all(np.isfinite(v) for row in results for v in row.values()),
        "analytic_positive_eigenvalue_gt_half": all(r["positive_eigenvalue_bound"] > 0.5 for r in results),
        "analytic_uniform_s_bound_le_one_eighth": config["epsilon"] * config["radius"]**2 / 2 <= 1 / 8,
        "sampled_s_le_analytic_bound": all(0 <= r["certificate_s"] <= config["epsilon"] * config["radius"]**2 / 2 + bound_tol for r in results),
        "mass_identity": all(abs(r["mass_perturbation"]) <= identity_tol for r in results),
        "integration_by_parts_identity": all(abs(r["beta_direct"] - r["beta_ibp"]) <= identity_tol for r in results),
        "full_path_below_generic_upper": all(r["full_path_upper"] <= r["full_generic_upper"] + bound_tol for r in results),
        "kb_certificate_below_reaction_upper": all(r["kb_certificate_lower"] <= r["reaction_path_upper"] + bound_tol for r in results),
        "analytic_hj_upper_nonpositive": all(r["hj_scalar_upper_analytic"] <= bound_tol for r in results),
        "sampled_hj_below_analytic_upper": all(r["hj_scalar_max_sampled"] <= r["hj_scalar_upper_analytic"] + bound_tol for r in results),
        "core_refinement_within_declared_tolerances": all(r["absolute_difference"] <= abs_tol or r["relative_difference_with_1e_minus12_floor"] <= rel_tol for r in core_refinement),
        "all_refinement_absolute_within_tolerance": all(r["absolute_difference"] <= abs_tol for r in refinement),
    }
    metrics = {
        "max_mass_absolute": max(abs(r["mass_perturbation"]) for r in results),
        "max_beta_identity_absolute": max(abs(r["beta_direct"] - r["beta_ibp"]) for r in results),
        "max_refinement_absolute": max(r["absolute_difference"] for r in refinement),
        "max_core_refinement_relative": max(r["relative_difference_with_1e_minus12_floor"] for r in core_refinement),
        "minimum_analytic_eigenvalue_lower": min(r["positive_eigenvalue_bound"] for r in results),
        "maximum_certificate_s": max(r["certificate_s"] for r in results),
        "kb_lower_positive_limit": fine[-1]["kb_limit"],
        "largest_frequency": fine[-1]["j"],
        "largest_frequency_full_upper": fine[-1]["full_path_upper"],
        "largest_frequency_kb_lower": fine[-1]["kb_certificate_lower"],
        "largest_frequency_kb_reaction_upper": fine[-1]["reaction_path_upper"],
        "largest_frequency_lower_to_full_upper_ratio": fine[-1]["kb_certificate_lower"] / fine[-1]["full_path_upper"],
        "largest_frequency_max_continuous_pairing_absolute": max(abs(fine[-1][k]) for k in PAIRING_FIELDS),
    }
    return fine, refinement, checks, metrics


def static_plots(config, fine, output):
    os.environ.setdefault("MPLCONFIGDIR", str(PROJECT / "tools" / "matplotlib-cache"))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator

    plt.rcParams.update({"font.size": 10, "savefig.dpi": 180, "axes.spines.top": False, "axes.spines.right": False})
    fig, axes = plt.subplots(1, 3, figsize=(14.0, 4.6), layout="constrained")
    fig.set_layout_engine("constrained", rect=(0.0, 0.14, 1.0, 0.84))
    x = np.linspace(-0.6, 0.6, 2401)
    for j in (2, 8, 32):
        _, rho = wave_fields(x, np.zeros_like(x), j, config["radius"], config["epsilon"])
        axes[0].plot(x, 1 + rho, lw=1.0, label=f"j = {j}")
    axes[0].axhline(1, color="0.55", ls=":", lw=0.8)
    axes[0].set(xlabel="x along y = 0", ylabel="$G_{22}(x,0)$", title="Smooth, uniformly positive endpoints", ylim=(0.68, 1.32))
    axes[0].legend(frameon=False, fontsize=8, ncol=3)

    js = np.array([r["j"] for r in fine])
    for key, label, marker, color in (
        ("full_path_upper", "$B_{\\rm full}^2$: feasible path upper", "o", "#1f77b4"),
        ("kb_certificate_lower", "$B_{\\rm KB}^2$: certificate lower", "s", "#d62728"),
        ("reaction_path_upper", "$B_{\\rm KB}^2$: reaction path upper", "^", "#ff7f0e"),
    ):
        axes[1].loglog(js, [r[key] for r in fine], marker=marker, ms=3, color=color, label=label)
    axes[1].axhline(fine[-1]["kb_limit"], color="0.45", ls="--", lw=0.8, label="Positive lower-bound limit")
    axes[1].set(xlabel="Oscillation frequency j (k = 2πj)", ylabel="Squared-cost bounds", title="Full upper vanishes; KB lower stays positive")
    axes[1].legend(frameon=False, fontsize=7.5, loc="lower left")
    axes[1].grid(alpha=0.18, which="both")

    for i in range(6):
        axes[2].loglog(js, np.maximum([abs(r[f"pairing_{i}"]) for r in fine], 1e-18), marker=".", ms=4, label=f"Test {i + 1}")
    axes[2].set(xlabel="Oscillation frequency j", ylabel="Absolute continuous-test pairing", title="Six illustrative weak-star test pairings", ylim=(5e-19, 1e-2))
    axes[2].legend(frameon=False, fontsize=7, ncol=2)
    axes[2].grid(alpha=0.18, which="both")
    for ax in axes[1:]:
        ax.xaxis.set_major_locator(FixedLocator([2, 4, 8, 16, 32, 64]))
        ax.xaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{value:g}"))
        ax.xaxis.set_minor_locator(NullLocator())
    fig.suptitle("Matrix transport: an explicit separation mechanism (seed 0921)", fontsize=13)
    fig.text(0.01, 0.01, "Bounds evaluated by floating-point quadrature; no optimal-distance solver. Test-pairing display floor: 10⁻¹⁸.\nExplicit R = 0.4 exponential bump; same mechanism as the formal theorem, a separate concrete instance.", fontsize=8)
    for ext in ("pdf", "png", "svg"):
        fig.savefig(output / f"two_model_separation.{ext}", bbox_inches="tight")
    plt.close(fig)

    coords = np.linspace(-1, 1, 601)
    xx, yy = np.meshgrid(coords, coords)
    outside = xx**2 + yy**2 > 1
    fig, axes = plt.subplots(1, 3, figsize=(10.7, 3.5), layout="constrained")
    for ax, j in zip(axes, (2, 8, 24)):
        _, rho = wave_fields(xx, yy, j, config["radius"], config["epsilon"])
        values = np.ma.array(1 + rho, mask=outside)
        im = ax.imshow(values, origin="lower", extent=(-1, 1, -1, 1), cmap="RdBu_r", vmin=0.5, vmax=1.5)
        ax.set(title=f"j = {j}", xlabel="x", ylabel="y", aspect="equal")
    fig.colorbar(im, ax=axes, label="$G_{22}$ (common scale)", shrink=0.8)
    fig.suptitle("Smooth positive matrix density on the unit disk; G₁₁ = 1", fontsize=12)
    for ext in ("png", "pdf"):
        fig.savefig(output / f"endpoint_density.{ext}", bbox_inches="tight")
    plt.close(fig)


def interactive_plot(config, fine, output):
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots

    x = np.linspace(-0.6, 0.6, 2401)
    fig = make_subplots(rows=1, cols=2, subplot_titles=("Endpoint profile G22(x, 0)", "Squared-cost upper and lower bounds"))
    profiles = []
    for j in config["frequencies"]:
        _, rho = wave_fields(x, np.zeros_like(x), j, config["radius"], config["epsilon"])
        profiles.append(1 + rho)
    fig.add_trace(go.Scatter(x=x, y=profiles[0], mode="lines", name="G22", line={"color": "#1565c0"}), row=1, col=1)
    js = [r["j"] for r in fine]
    for key, name, color in (
        ("full_path_upper", "Full: feasible path upper", "#1f77b4"),
        ("kb_certificate_lower", "KB: certificate lower", "#d62728"),
        ("reaction_path_upper", "KB: reaction path upper", "#ff7f0e"),
    ):
        fig.add_trace(go.Scatter(x=js, y=[r[key] for r in fine], mode="lines+markers", name=name, line={"color": color}), row=1, col=2)
    fig.add_trace(go.Scatter(x=[js[0]], y=[fine[0]["full_path_upper"]], mode="markers", name="Selected frequency", marker={"size": 14, "symbol": "circle-open", "color": "black"}), row=1, col=2)
    frames = [go.Frame(name=str(j), data=[go.Scatter(y=profile), go.Scatter(x=[j], y=[r["full_path_upper"]])], traces=[0, 4]) for j, profile, r in zip(js, profiles, fine)]
    fig.frames = frames
    steps = [{"method": "animate", "label": str(j), "args": [[str(j)], {"mode": "immediate", "frame": {"duration": 0, "redraw": False}, "transition": {"duration": 0}}]} for j in js]
    fig.update_layout(
        title="Smooth positive matrix transport example — seed 0921",
        height=600, template="plotly_white", margin={"l": 70, "r": 35, "t": 100, "b": 170},
        sliders=[{"active": 0, "currentvalue": {"prefix": "Oscillation frequency j = "}, "steps": steps, "pad": {"t": 40}, "y": -0.12}],
        legend={"orientation": "h", "x": 0, "y": 1.13, "font": {"size": 11}},
    )
    fig.update_xaxes(title_text="x at y = 0", row=1, col=1)
    fig.update_yaxes(title_text="G22", range=[0.68, 1.32], row=1, col=1)
    fig.update_xaxes(type="log", title_text="Oscillation frequency j", row=1, col=2)
    fig.update_yaxes(type="log", title_text="Squared-cost bounds", row=1, col=2)
    fig.add_annotation(x=0, y=-0.42, xref="paper", yref="paper", xanchor="left", showarrow=False, align="left", text="Feasible-path upper bounds and a dual-certificate lower bound; no optimal-distance solve.<br>Floating-point quadrature; explicit exponential bump, a concrete illustration of the same mechanism.<br>Li-Zou WB normalization; original BV squared KB distance is twice this normalization.", font={"size": 11})
    fig.write_html(output / "interactive_separation.html", include_plotlyjs=True, full_html=True, auto_play=False)


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=PROJECT / "numerical" / "experiment_config.json")
    parser.add_argument("--output", type=Path, default=PROJECT / "artifacts" / "visualization")
    parser.add_argument("--mlflow-run-id", help="Optional real run ID supplied by an external MLflow wrapper.")
    parser.add_argument("--git-provenance", type=Path, help="JSON with commit, branch, dirty state captured by the external tracking wrapper.")
    return parser.parse_args(argv)


def main(argv=None):
    args = parse_args(argv)
    config = json.loads(args.config.read_text())
    if config["seed"] != 921 or config["seed_label"] != "0921":
        raise ValueError("This project uses the reproduction seed 0921 (integer 921)")
    if config["test_count"] != 6:
        raise ValueError("This illustration is configured for six fixed continuous tests")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    source_before = source_hashes()
    coefficients, results = evaluate(config)
    fine, refinement, checks, metrics = refinement_and_checks(config, results)
    write_csv(output / "quadrature_results.csv", results)
    write_csv(output / "quadrature_refinement.csv", refinement)
    write_json(output / "test_function_coefficients.json", {"seed": 921, "seed_label": "0921", "function": "cos(a*x + b*y + phase)", "columns": ["a", "b", "phase"], "coefficients": coefficients.tolist()})
    write_json(output / "experiment_config.json", config)
    static_plots(config, fine, output)
    interactive_plot(config, fine, output)
    source_after = source_hashes()
    checks["source_unchanged_during_run"] = source_before == source_after
    metrics["runtime_seconds"] = time.perf_counter() - started
    import matplotlib
    import plotly
    provenance = json.loads(args.git_provenance.read_text()) if args.git_provenance else git_state()
    summary = {
        "experiment": config["experiment"], "run_name": config["run_name"],
        "mlflow_run_id": args.mlflow_run_id, "seed": 921, "seed_label": "0921",
        "status": "passed" if all(checks.values()) else "failed",
        "checks": checks, "metrics": metrics, "source_sha256": source_after,
        "git": provenance, "environment": {"python": platform.python_version(), "numpy": np.__version__, "matplotlib": matplotlib.__version__, "plotly": plotly.__version__},
        "caption": CAPTION,
        "limitations": ["Floating-point quadrature is not an interval or formal certificate.", "Six continuous tests illustrate convergence; the all-test weak-star result is supplied by the Lean theorem.", "Displayed feasible-path upper and dual-certificate lower bounds do not determine exact optimal distances.", "The explicit exponential numerical bump is a separate concrete realization of the construction, not evaluation of Lean's noncomputable chosen bump."],
    }
    write_json(output / "experiment_summary.json", summary)
    manifest = {str(p.relative_to(output)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(output.iterdir()) if p.is_file() and p.name != "artifact_sha256.json"}
    write_json(output / "artifact_sha256.json", manifest)
    print(json.dumps({"status": summary["status"], "mlflow_run_id": args.mlflow_run_id, "metrics": metrics, "checks": checks}, indent=2))
    if not all(checks.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
