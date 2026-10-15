"""Theory-directed numerical comparisons using the existing SDP and rotating formulas.

This engine writes artifacts and does not import an MLflow client. A research run
is tracked by an external wrapper; ordinary correctness tests use mocked solves.
"""
from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
from decimal import Decimal, localcontext
from functools import lru_cache
import hashlib
import importlib.util
from importlib.metadata import version
import json
import math
from pathlib import Path
import platform
import shutil
import subprocess
import time
import traceback
from typing import Any

import numpy as np

if __package__:
    from .solver import solve_transport
else:
    from solver import solve_transport

PROJECT = Path(__file__).resolve().parents[2]
LEGACY_FORMULAS = PROJECT / "numerical/rotating-reaction/numerical/rotating_family.py"
SEED = 921
EXPERIMENT = "matrix-transport-consolidated-validation"


@lru_cache(maxsize=1)
def rotating_formulas():
    spec = importlib.util.spec_from_file_location("matrix_transport_rotating_formula", LEGACY_FORMULAS)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load existing rotating formulas: {LEGACY_FORMULAS}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sqrt_psd(matrix: Any) -> np.ndarray:
    """Spectral evaluation of the existing PSD square-root formula; no regularization."""
    matrix = np.asarray(matrix, dtype=float)
    if matrix.shape != (2, 2) or not np.isfinite(matrix).all():
        raise ValueError("matrix must be finite and 2-by-2")
    if not np.allclose(matrix, matrix.T, atol=1e-12, rtol=1e-12):
        raise ValueError("matrix must be symmetric")
    eigenvalues, vectors = np.linalg.eigh((matrix + matrix.T) / 2)
    scale = max(1.0, float(np.max(np.abs(eigenvalues))))
    if eigenvalues.min() < -1e-12 * scale:
        raise ValueError("matrix must be positive semidefinite")
    return (vectors * np.sqrt(np.maximum(eigenvalues, 0.0))) @ vectors.T


def weighted_bures_value(H: Any, A0: Any, A1: Any) -> float:
    """Independent spectral evaluation of 2*d_B^2(H^-1 A0 H^-1,H^-1 A1 H^-1)."""
    H = np.asarray(H, dtype=float)
    if H.shape != (2, 2) or not np.isfinite(H).all():
        raise ValueError("H must be finite and 2-by-2")
    if not np.allclose(H, H.T, atol=1e-12, rtol=1e-12) or np.linalg.eigvalsh(H).min() <= 0:
        raise ValueError("H must be symmetric positive definite")
    A0, A1 = np.asarray(A0, dtype=float), np.asarray(A1, dtype=float)
    sqrt_psd(A0)
    sqrt_psd(A1)
    inverse = np.linalg.solve(H, np.eye(2))
    X, Y = inverse @ A0 @ inverse, inverse @ A1 @ inverse
    S = sqrt_psd(X)
    return float(2 * (np.trace(X) + np.trace(Y) - 2 * np.trace(sqrt_psd(S @ Y @ S))))


def weighted_bures_value_decimal(H: Any, A0: Any, A1: Any, *, precision: int = 60) -> float:
    """Independent 2-by-2 Bures reference without float64 cancellation.

    For PSD X,Y, tr sqrt(sqrt(X) Y sqrt(X)) equals
    sqrt(tr(XY)+2 sqrt(det(X) det(Y))). The inverse, congruences,
    determinants and final subtraction use Decimal.from_float inputs.
    """
    if isinstance(precision, bool) or not isinstance(precision, int) or precision < 30:
        raise ValueError("precision must be an integer at least thirty")
    H = np.asarray(H, dtype=float)
    A0, A1 = np.asarray(A0, dtype=float), np.asarray(A1, dtype=float)
    if H.shape != (2, 2) or not np.isfinite(H).all():
        raise ValueError("H must be finite and 2-by-2")
    if not np.allclose(H, H.T, atol=1e-12, rtol=1e-12) or np.linalg.eigvalsh(H).min() <= 0:
        raise ValueError("H must be symmetric positive definite")
    sqrt_psd(A0)
    sqrt_psd(A1)
    with localcontext() as context:
        context.prec = precision
        def matrix(A):
            return [[Decimal.from_float(float(A[i, j])) for j in range(2)] for i in range(2)]
        def product(A, B):
            return [[sum((A[i][k] * B[k][j] for k in range(2)), Decimal(0))
                     for j in range(2)] for i in range(2)]
        def determinant(A):
            return A[0][0] * A[1][1] - A[0][1] * A[1][0]
        h = matrix(H)
        det_h = determinant(h)
        if det_h <= 0:
            raise ValueError("H must have positive determinant in the high-precision reference")
        inverse = [[h[1][1] / det_h, -h[0][1] / det_h],
                   [-h[1][0] / det_h, h[0][0] / det_h]]
        X = product(product(inverse, matrix(A0)), inverse)
        Y = product(product(inverse, matrix(A1)), inverse)
        det_x, det_y = determinant(X), determinant(Y)
        if det_x < 0 or det_y < 0:
            raise ValueError("endpoint congruence has negative determinant in the high-precision reference")
        XY = product(X, Y)
        radicand = XY[0][0] + XY[1][1] + 2 * (det_x * det_y).sqrt()
        if radicand < 0:
            raise ValueError("negative Bures square-root radicand")
        value = 2 * (X[0][0] + X[1][1] + Y[0][0] + Y[1][1] - 2 * radicand.sqrt())
        return float(value)


def profile_endpoints(nx: int) -> tuple[np.ndarray, np.ndarray]:
    """Cell samples of two noncommuting SPD profiles with total matrix I.

    G0=I+cos(2πx)diag(1,-1)/4; G1=I+sin(2πx)[[0,1],[1,0]]/4.
    Their traces are exactly two. Their continuum hub moments at x*=1/2
    are both 1/6, so E_H=0 and the continuum upper bound is 1/(3*t^2).
    """
    if isinstance(nx, bool) or not isinstance(nx, int) or nx < 2:
        raise ValueError("nx must be an integer at least two")
    x = (np.arange(nx) + 0.5) / nx
    I = np.eye(2)
    T = np.diag([1.0, -1.0])
    S = np.array([[0.0, 1.0], [1.0, 0.0]])
    return (I + 0.25 * np.cos(2 * np.pi * x)[:, None, None] * T,
            I + 0.25 * np.sin(2 * np.pi * x)[:, None, None] * S)


def solver_quality(result: dict[str, Any]) -> dict[str, Any]:
    """Fixed feasibility/objective checks; retain failures without repairing solver data."""
    diagnostics = result.get("diagnostics") or {}
    independent = result.get("independent_quadratic_cost") or {}
    checks = {"optimal_status": result.get("status") == "optimal"}
    for name in ("ce_max_frobenius_residual", "ce_max_scaled_residual",
                 "endpoint_max_frobenius_residual", "endpoint_max_scaled_residual",
                 "cone_max_scaled_violation", "max_rho_symmetry_error", "boundary_flux_max_frobenius"):
        value = diagnostics.get(name)
        checks[name] = value is not None and math.isfinite(value) and value <= 1e-7
    value = independent.get("max_range_residual")
    checks["range_residual"] = value is not None and math.isfinite(value) and value <= 1e-7
    value = diagnostics.get("rho_min_eigenvalue")
    checks["mass_psd"] = value is not None and math.isfinite(value) and value >= -1e-7
    actual, recomputed = result.get("primal_total"), independent.get("total")
    checks["objective_agreement"] = (
        actual is not None and recomputed is not None and math.isfinite(actual)
        and math.isfinite(recomputed) and abs(actual - recomputed) <= 1e-7 + 1e-6 * abs(recomputed))
    return {"passed": all(checks.values()), "checks": checks,
            "failed_checks": [name for name, passed in checks.items() if not passed]}


def source_hashes() -> dict[str, str]:
    files = [Path(__file__), Path(__file__).with_name("solver.py"), LEGACY_FORMULAS]
    files += list(Path(__file__).parent.glob("tests/*.py"))
    files += [p for p in (Path(__file__).with_name("requirements.txt"), Path(__file__).with_name("README.md")) if p.exists()]
    return {str(p.relative_to(PROJECT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}


def git_state() -> dict[str, Any]:
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


def analytic_check(epsilon: float, theta: float) -> dict[str, Any]:
    legacy = rotating_formulas()
    path = legacy.optimal_path(epsilon, theta, np.linspace(0, 1, 129))
    diagnostics = legacy.path_diagnostics(path)
    spectral = weighted_bures_value(path["weight"], legacy.G0, legacy.G1)
    high_precision = weighted_bures_value_decimal(path["weight"], legacy.G0, legacy.G1)
    exact = path["exact_action"]
    scale = max(1.0, abs(exact))
    error = abs(spectral - exact) / scale
    reference_error = abs(high_precision - exact) / scale
    return {"family": "rotating_formula_path", "epsilon": epsilon, "theta": theta,
            "exact_action": exact, "independent_spectral_bures": spectral,
            "spectral_relative_error": error, "float64_reference_passed": error <= 1e-7,
            "independent_decimal_bures": high_precision, "decimal_reference_relative_error": reference_error,
            "reference_precision_decimal_digits": 60, **diagnostics,
            "passed": reference_error <= 1e-7 and diagnostics["ce_scaled_residual"] <= 1e-7
            and diagnostics["endpoint_scaled_residual"] <= 1e-7
            and diagnostics["mass_min_eigenvalue"] >= -1e-7
            and diagnostics["independent_action_relative_error"] <= 1e-7
            and diagnostics["factor_endpoint_residual"] <= 1e-7
            and diagnostics["ak_symmetry_error"] <= 1e-7
            and diagnostics["ak_min_eigenvalue"] > 0
            and diagnostics["mass_symmetry_error"] <= 1e-7
            and diagnostics["energy_density_relative_error"] <= 1e-7
            and diagnostics["energy_density_constancy_relative_error"] <= 1e-7}


def write_artifacts(data: dict[str, Any], output: Path) -> None:
    """Update this run's artifacts, retaining every status and full solver field."""
    output.mkdir(parents=True, exist_ok=True)
    (output / "results.json").write_text(json.dumps(data, indent=2, allow_nan=False) + "\n")
    (output / "metadata.json").write_text(json.dumps(data["metadata"], indent=2, allow_nan=False) + "\n")
    (output / "source_hashes.json").write_text(json.dumps(data["metadata"]["source_sha256"], indent=2) + "\n")
    rows = data["analytic"] + data["comparisons"]
    if rows:
        columns = sorted({key for row in rows for key in row})
        with (output / "summary.csv").open("w", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=columns)
            writer.writeheader()
            writer.writerows(rows)


def run_experiment(output: str | Path, *, seed: int = SEED, meshes=(8, 16, 32),
                   nx: int = 4, profile_nt: int = 16, tolerance: float = 1e-9,
                   mlflow_run_id: str | None = None) -> dict[str, Any]:
    """Run the configured comparisons. Scientific execution is controlled by the caller."""
    output = Path(output)
    if output.exists() and any(output.iterdir()):
        raise FileExistsError("choose an empty output directory; previous research artifacts are preserved")
    if seed != SEED:
        raise ValueError("this fixed design uses seed 921")
    if not meshes or any(isinstance(n, bool) or not isinstance(n, int) or n < 1 for n in meshes):
        raise ValueError("meshes must be positive integer time resolutions")
    if isinstance(profile_nt, bool) or not isinstance(profile_nt, int) or profile_nt < 1:
        raise ValueError("profile_nt must be a positive integer")
    if not math.isfinite(tolerance) or tolerance <= 0:
        raise ValueError("tolerance must be finite and positive")
    initial, final = profile_endpoints(nx)
    started = time.perf_counter()
    hashes = source_hashes()
    metadata = {"experiment": EXPERIMENT, "mlflow_run_id": mlflow_run_id, "seed": seed,
                "stochastic": False, "started_utc": datetime.now(timezone.utc).isoformat(),
                "source_sha256": hashes, "git": git_state(), "python": platform.python_version(),
                "platform": platform.platform(), "versions": {p: version(p) for p in ("numpy", "cvxpy", "clarabel", "scipy")},
                "meshes": list(meshes), "profile_nx": nx, "profile_nt": profile_nt,
                "solver_tolerance": tolerance, "solver_max_iter": 300, "complete": False,
                "theory_comparison": "SDP grid values are discretizations; signed bound differences are recorded, not formal certificates",
                "analytic_reference": {"method": "2-by-2 trace-square-root Bures formula; inverse and congruences from Decimal.from_float inputs",
                                       "precision_decimal_digits": 60, "relative_tolerance": 1e-7,
                                       "float64_spectral_reference": "retained diagnostic with separate pass flag"},
                "hub": {"location": 0.5, "M0": 1 / 6, "M1": 1 / 6, "B_squared": 1 / 3, "E_H": 0.0}}
    data = {"metadata": metadata, "analytic": [], "solves": [], "comparisons": []}
    output.mkdir(parents=True, exist_ok=True)
    for name in hashes:
        destination = output / "source" / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(PROJECT / name, destination)
    write_artifacts(data, output)
    cache = {}

    def solve(case_id, family, a, b, H, nt, L=None, **reference):
        key = json.dumps({"initial": a.tolist(), "final": b.tolist(), "H": None if H is None else H.tolist(),
                          "L": None if L is None else L.tolist(), "nt": nt, "tolerance": tolerance}, sort_keys=True)
        reused = cache.get(key)
        if reused is None:
            try:
                result = solve_transport(a, b, H, L=L, nt=nt, tolerance=tolerance)
            except Exception as error:
                result = {"status": "exception", "reason": f"{type(error).__name__}: {error}",
                          "traceback": traceback.format_exc(), "primal_total": None}
            cache[key] = (case_id, result)
        else:
            result = reused[1]
        quality = solver_quality(result)
        data["solves"].append({"case_id": case_id, "family": family, "nt": nt, "nx": len(a),
                               "H": None if H is None else H.tolist(), "L": None if L is None else L.tolist(),
                               "initial": a.tolist(), "final": b.tolist(), "reused_case_id": None if reused is None else reused[0],
                               "reference": reference, "quality": quality, "result": result})
        row = {"case_id": case_id, "family": family, "nt": nt, "nx": len(a),
               "status": result["status"], "quality_passed": quality["passed"],
               "failed_checks": ";".join(quality["failed_checks"]), "action": result.get("primal_total"),
               "reused_case_id": None if reused is None else reused[0], **reference}
        row.update({"diagnostic_" + k: v for k, v in (result.get("diagnostics") or {}).items()})
        row.update({"independent_" + k: v for k, v in (result.get("independent_quadratic_cost") or {}).items()})
        row["runtime_seconds"] = result.get("runtime_seconds")
        if row["action"] is not None:
            for label in ("exact_action", "balanced_reference", "continuum_upper_bound"):
                if reference.get(label) is not None:
                    row["action_minus_" + label] = row["action"] - reference[label]
        data["comparisons"].append(row)
        write_artifacts(data, output)
        return result

    for exponent in (0.75, 0.5, 0.25):
        for epsilon in (0.1, 0.01, 0.001):
            try:
                row = analytic_check(epsilon, epsilon ** exponent)
            except Exception as error:
                row = {"family": "rotating_formula_path", "epsilon": epsilon,
                       "theta": epsilon ** exponent, "passed": False, "status": "exception",
                       "reason": f"{type(error).__name__}: {error}", "traceback": traceback.format_exc()}
            row["angle_exponent"] = exponent
            data["analytic"].append(row)
            write_artifacts(data, output)
    legacy = rotating_formulas()
    for epsilon, theta in ((0.4, 0.2), (0.2, 0.35)):
        path = legacy.optimal_path(epsilon, theta, np.array([0.0, 1.0]))
        for nt in meshes:
            solve(f"rotating_eps{epsilon}_theta{theta}_nt{nt}", "rotating_temporal_sdp",
                  legacy.G0[None], legacy.G1[None], path["weight"], nt,
                  epsilon=epsilon, theta=theta, exact_action=path["exact_action"])
    balanced = solve("balanced_profile", "reaction_zero_reference", initial, final, None, profile_nt)
    for epsilon in (1.0, 0.25, 0.0625):
        solve(f"reaction_zero_eps{epsilon}", "reaction_zero", initial, final, epsilon * np.eye(2), profile_nt,
              epsilon=epsilon, balanced_reference=balanced.get("primal_total"))
    for t in (1.0, 2.0, 4.0):
        # L=None is exactly identity and allows reuse of the epsilon=1 case.
        L = None if t == 1.0 else t * np.eye(2)
        solve(f"large_transport_t{t}", "large_transport", initial, final, np.eye(2), profile_nt, L,
              transport_scale=t, continuum_upper_bound=1 / (3 * t * t), hub_limit=0.0)
    hashes_after = source_hashes()
    metadata.update(complete=True, duration_seconds=time.perf_counter() - started,
                    finished_utc=datetime.now(timezone.utc).isoformat(), source_unchanged=hashes == hashes_after,
                    source_sha256_after=hashes_after, git_after=git_state(),
                    unique_solver_calls=len(cache), solver_case_requests=len(data["solves"]),
                    all_quality_passed=all(r["passed"] for r in data["analytic"]) and
                    all(r["quality"]["passed"] for r in data["solves"]))
    write_artifacts(data, output)
    if not metadata["source_unchanged"]:
        raise RuntimeError("source changed during the experiment; results and both source states must be reviewed")
    return data


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--meshes", type=int, nargs="+", default=[8, 16, 32])
    parser.add_argument("--nx", type=int, default=4)
    parser.add_argument("--profile-nt", type=int, default=16)
    parser.add_argument("--tolerance", type=float, default=1e-9)
    parser.add_argument("--mlflow-run-id")
    args = parser.parse_args(argv)
    data = run_experiment(args.output, seed=args.seed, meshes=tuple(args.meshes), nx=args.nx,
                          profile_nt=args.profile_nt, tolerance=args.tolerance, mlflow_run_id=args.mlflow_run_id)
    print(json.dumps({"output": str(args.output), "experiment": EXPERIMENT,
                      "mlflow_run_id": args.mlflow_run_id, "all_quality_passed": data["metadata"]["all_quality_passed"]}))
    return 0 if data["metadata"]["all_quality_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
