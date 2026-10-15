"""Artifacts for an evaluation of exact formulas, not an SDP solve.

Tracking is optional. An external wrapper may supply its real run and experiment
identifiers; this environment need not contain MLflow. The default scientific
sweep is never run at import.
"""

from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import time
from typing import Any

import numpy as np

from .rotating_family import (SEED, SINGULAR_TARGET_ACTION, optimal_path,
                              path_diagnostics, quadratic_energy_density)

PROJECT = Path(__file__).resolve().parents[1]
METHOD = "exact analytic closed form and explicit optimal path; no SDP optimization"


def source_hashes() -> dict[str, str]:
    """Hash every new production and verification Python source file."""
    files = sorted([*PROJECT.glob("numerical/**/*.py"), *PROJECT.glob("tests/**/*.py")])
    return {str(p.relative_to(PROJECT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def _git_state() -> dict[str, Any]:
    def read(*args: str) -> str:
        return subprocess.check_output(["git", "-C", str(PROJECT), *args], text=True,
                                       stderr=subprocess.DEVNULL).strip()
    try:
        status = read("status", "--porcelain")
        return {"commit": read("rev-parse", "HEAD"), "branch": read("branch", "--show-current"),
                "dirty": bool(status), "status_porcelain": status}
    except (subprocess.CalledProcessError, OSError):
        return {"commit": None, "branch": None, "dirty": None, "status_porcelain": None}


def family_definitions() -> list[dict[str, Any]]:
    return [
        {"family": f"power_p{p:g}", "kind": "power", "exponent": p, "amplitude": 1.0}
        for p in (0.75, 0.5, 0.25)
    ] + [
        {"family": f"critical_a{a:g}", "kind": "critical", "exponent": 0.5, "amplitude": a}
        for a in (0.5, 1.0, 2.0)
    ]


def evaluate_case(epsilon: float, family: dict[str, Any], time_samples: int = 201
                  ) -> tuple[dict[str, Any], dict[str, Any]]:
    if isinstance(time_samples, bool) or int(time_samples) != time_samples or time_samples < 2:
        raise ValueError("time_samples must be an integer at least two")
    time_samples = int(time_samples)
    epsilon = float(epsilon)
    if not np.isfinite(epsilon) or epsilon <= 0:
        raise ValueError("epsilon must be finite and strictly positive")
    theta = float(family["amplitude"] * epsilon ** family["exponent"])
    path = optimal_path(epsilon, theta, np.linspace(0.0, 1.0, time_samples))
    p = family["exponent"]
    if p > 0.5:
        limit, status = SINGULAR_TARGET_ACTION, "singular_target"
    elif p == 0.5:
        limit = SINGULAR_TARGET_ACTION + family["amplitude"] ** 4 / 2.0
        status = "finite_critical"
    else:
        limit, status = None, "divergent"
    row = {
        **family, "epsilon": float(epsilon), "theta": theta,
        "theta_over_sqrt_epsilon": theta / np.sqrt(epsilon),
        "sin_squared_over_epsilon": np.sin(theta) ** 2 / epsilon,
        "exact_action": path["exact_action"], "singular_target_action": SINGULAR_TARGET_ACTION,
        "action_minus_target": path["exact_action"] - SINGULAR_TARGET_ACTION,
        "limit_status": status, "limit_action": limit,
        "asymptotic_main_term": theta ** 4 / (2.0 * epsilon ** 2),
        **path_diagnostics(path),
    }
    return row, path


def _jsonable(value: Any) -> Any:
    if isinstance(value, np.ndarray):
        return value.tolist()
    if isinstance(value, np.generic):
        return value.item()
    if isinstance(value, dict):
        return {k: _jsonable(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [_jsonable(v) for v in value]
    return value


def _plots(rows: list[dict[str, Any]], paths: list[dict[str, Any]], output: Path) -> None:
    # Keep Matplotlib's cache on the permitted portable workspace or /tmp.
    os.environ.setdefault("MPLCONFIGDIR", "/tmp/matrix-partial-reaction-matplotlib")
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, axes = plt.subplots(1, 2, figsize=(12, 4.5), constrained_layout=True)
    families = list(dict.fromkeys(row["family"] for row in rows))
    for family in families:
        selected = [row for row in rows if row["family"] == family]
        kind = selected[0]["kind"]
        ax = axes[0 if kind == "power" else 1]
        eps = [row["epsilon"] for row in selected]
        line, = ax.plot(eps, [row["exact_action"] for row in selected],
                        marker=".", markersize=3, label=family)
        if kind == "critical":
            ax.axhline(selected[0]["limit_action"], color=line.get_color(), ls="--", alpha=0.6)
    for ax in axes:
        ax.set_xscale("log")
        ax.invert_xaxis()
        ax.set_xlabel("epsilon (vanishing reaction eigenvalue)")
        ax.set_ylabel("exact minimum action = 2 Bures squared")
        ax.grid(alpha=0.25)
        ax.legend(fontsize=8)
    axes[0].set_yscale("log")
    axes[0].axhline(SINGULAR_TARGET_ACTION, color="black", ls=":", label="singular target")
    axes[0].legend(fontsize=8)
    axes[0].set_title("theta = epsilon^p")
    axes[1].set_title("theta = a sqrt(epsilon); dashed lines: exact limits")
    fig.suptitle("Specified uniform 2-by-2 family: analytic evaluation, no SDP solver")
    fig.savefig(output / "action_thresholds.png", dpi=180)
    plt.close(fig)

    # One genuine path per family at the sampled epsilon closest to 1e-2.
    selected_paths = []
    for family in families:
        candidates = [path for path in paths if path["family"] == family]
        if candidates:
            selected_paths.append(min(candidates, key=lambda path: abs(np.log10(path["epsilon"]) + 2.0)))
    if not selected_paths:
        return
    fig, axes = plt.subplots(len(selected_paths), 2, figsize=(12, 3.0 * len(selected_paths)),
                             squeeze=False, constrained_layout=True)
    for axs, path in zip(axes, selected_paths):
        t, g, r = path["times"], path["mass"], path["reaction"]
        for i, j in ((0, 0), (1, 1), (0, 1)):
            axs[0].plot(t, g[:, i, j], label=f"G{i+1}{j+1}")
        for i, j in ((0, 0), (0, 1), (1, 0), (1, 1)):
            axs[1].plot(t, r[:, i, j], label=f"R{i+1}{j+1}")
        for ax in axs:
            ax.set_xlabel("time")
            ax.grid(alpha=0.25)
            ax.legend(fontsize=8)
        axs[0].set_title(f"{path['family']}, epsilon={path['epsilon']:.2g}: actual G(t)")
        axs[1].set_title("actual full R(t); sym R = dG/dt")
    fig.suptitle("Explicit globally optimal paths; spatially uniform, zero flux")
    fig.savefig(output / "optimal_paths.png", dpi=180)
    plt.close(fig)


def write_artifacts(rows: list[dict[str, Any]], paths: list[dict[str, Any]],
                    metadata: dict[str, Any], output_directory: str | Path) -> dict[str, str]:
    """Export already-computed data; also usable in a tiny pytest smoke check."""
    if not rows:
        raise ValueError("rows cannot be empty")
    hashes = source_hashes()
    if metadata.get("source_sha256", hashes) != hashes:
        raise RuntimeError("Python sources changed during the run; preserve source provenance")
    output = Path(output_directory)
    output.mkdir(parents=True, exist_ok=True)
    with (output / "summary.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(_jsonable(rows))
    saved_paths = []
    for path in paths:
        saved_paths.append({**path, "energy_density": quadratic_energy_density(
            path["mass"], path["reaction"], path["epsilon"], path["theta"])})
    payload = _jsonable({"metadata": metadata, "summary": rows, "paths": saved_paths})
    (output / "results.json").write_text(json.dumps(payload, indent=2, allow_nan=False), encoding="utf-8")
    (output / "metadata.json").write_text(json.dumps(_jsonable(metadata), indent=2, allow_nan=False),
                                          encoding="utf-8")
    (output / "source_hashes.json").write_text(json.dumps(hashes, indent=2), encoding="utf-8")
    for relative in hashes:
        target = output / "source" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(PROJECT / relative, target)
        if hashlib.sha256(target.read_bytes()).hexdigest() != hashes[relative]:
            raise RuntimeError("Python source changed while its artifact snapshot was copied")
    _plots(rows, paths, output)
    return {name: str(output / name) for name in (
        "summary.csv", "results.json", "metadata.json", "source_hashes.json",
        "action_thresholds.png", "optimal_paths.png")}


def run_experiment(output_directory: str | Path, *, tracking_run_id: str | None = None,
                   experiment_name: str | None = None, epsilon_min: float = 1e-8,
                   epsilon_max: float = 1e-1, epsilon_count: int = 29,
                   time_samples: int = 201, seed: int = SEED) -> dict[str, Any]:
    """Scientific sweep with optional externally supplied tracking context."""
    if tracking_run_id == "" or experiment_name == "" or ((tracking_run_id is None) != (experiment_name is None)):
        raise ValueError("supply both real tracking_run_id and experiment_name, or omit both")
    if not (0 < epsilon_min <= epsilon_max <= 1):
        raise ValueError("require 0 < epsilon_min <= epsilon_max <= 1")
    if isinstance(epsilon_count, bool) or int(epsilon_count) != epsilon_count or epsilon_count < 2:
        raise ValueError("epsilon_count must be an integer at least two")
    epsilon_count = int(epsilon_count)
    if isinstance(seed, bool) or seed != SEED:
        raise ValueError("this project uses seed 0921 (integer 921)")
    started = time.perf_counter()
    hashes, git = source_hashes(), _git_state()
    epsilons = np.geomspace(epsilon_max, epsilon_min, epsilon_count)
    targets = [1e-2, 1e-4, 1e-6]
    saved_indices = {int(np.argmin(np.abs(np.log10(epsilons) - np.log10(target)))) for target in targets}
    rows, paths = [], []
    for family in family_definitions():
        for i, epsilon in enumerate(epsilons):
            row, path = evaluate_case(float(epsilon), family, time_samples)
            rows.append(row)
            if i in saved_indices:
                paths.append({"family": family["family"], **path})
    metrics = {
        "case_count": len(rows), "saved_path_count": len(paths),
        "unique_parameter_pair_count": len({(row["epsilon"], row["theta"]) for row in rows}),
        "max_factor_endpoint_residual": max(row["factor_endpoint_residual"] for row in rows),
        "max_ce_scaled_residual": max(row["ce_scaled_residual"] for row in rows),
        "max_endpoint_scaled_residual": max(row["endpoint_scaled_residual"] for row in rows),
        "min_mass_eigenvalue": min(row["mass_min_eigenvalue"] for row in rows),
        "min_ak_eigenvalue": min(row["ak_min_eigenvalue"] for row in rows),
        "max_ak_symmetry_error": max(row["ak_symmetry_error"] for row in rows),
        "max_energy_relative_error": max(row["energy_density_relative_error"] for row in rows),
        "max_independent_action_relative_error": max(row["independent_action_relative_error"] for row in rows),
        "max_constancy_relative_error": max(row["energy_density_constancy_relative_error"] for row in rows),
    }
    metadata = {
        "project": "matrix-transport-partial-reaction", "method": METHOD,
        "experiment_name": experiment_name, "tracking_run_id": tracking_run_id,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "seed": SEED, "seed_label": "0921", "stochastic_sampling": False,
        "seed_use": "reserved project seed; formulas and grids are deterministic",
        "duplicate_curve_note": "power_p0.5 and critical_a1 are the same angle schedule, shown in both panels",
        "arithmetic": "float64, with rationalized action and rationalized A22-minus-one",
        "scope": "uniform I2 to diag(2,1), standard no-flux divergence, fixed PSD L",
        "certification_scope": "float64 consistency checks of analytic formulas; no SDP gap or new theorem certificate",
        "config": {"epsilon_min": epsilon_min, "epsilon_max": epsilon_max,
                   "epsilon_count": epsilon_count, "time_samples": time_samples,
                   "path_target_epsilons": targets, "families": family_definitions()},
        "git": git, "source_sha256": hashes,
        "environment": {"python": platform.python_version(), "numpy": np.__version__,
                        "matplotlib": version("matplotlib")},
        "metrics": metrics, "evaluation_runtime_seconds": time.perf_counter() - started,
    }
    artifacts = write_artifacts(rows, paths, metadata, output_directory)
    return {"metadata": metadata, "artifacts": artifacts,
            "total_runtime_seconds": time.perf_counter() - started}


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    parser.add_argument("--tracking-run-id", help="Optional real run ID supplied by an external wrapper")
    parser.add_argument("--experiment-name", help="Experiment name for the supplied tracking run")
    parser.add_argument("--epsilon-min", type=float, default=1e-8)
    parser.add_argument("--epsilon-max", type=float, default=1e-1)
    parser.add_argument("--epsilon-count", type=int, default=29)
    parser.add_argument("--time-samples", type=int, default=201)
    return parser.parse_args(argv)


def main() -> None:
    args = parse_args()
    result = run_experiment(args.output, tracking_run_id=args.tracking_run_id,
                            experiment_name=args.experiment_name, epsilon_min=args.epsilon_min,
                            epsilon_max=args.epsilon_max, epsilon_count=args.epsilon_count,
                            time_samples=args.time_samples)
    print(json.dumps(result, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
