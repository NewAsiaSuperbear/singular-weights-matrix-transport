"""A two-by-two matrix transport SDP on the unit time and space intervals.

The spatial operator is entrywise divergence of the symmetric flux. Boundary fluxes
are zero. Mass samples are PSD; flux and reaction matrices are fully unrestricted.
Each quadratic perspective has its own 4-by-4 PSD epigraph. This numerical model
and its floating-point diagnostics are not an additional formal certificate.
"""

from __future__ import annotations

from collections.abc import Mapping
from time import perf_counter
from typing import Any

import cvxpy as cp
import numpy as np


class BalancedInfeasibleError(ValueError):
    """No reaction-free path can connect these integrated matrix endpoints."""


def _endpoints(value: Any, name: str) -> np.ndarray:
    if np.iscomplexobj(value):
        raise ValueError(f"{name} must be real")
    array = np.asarray(value, dtype=float)
    if array.ndim != 3 or array.shape[1:] != (2, 2) or len(array) == 0:
        raise ValueError(f"{name} must have shape (nx, 2, 2), with nx >= 1")
    if not np.isfinite(array).all():
        raise ValueError(f"{name} must contain only finite numbers")
    scale = np.maximum(1.0, np.max(np.abs(array), axis=(-2, -1)))
    if np.any(np.max(np.abs(array - array.swapaxes(-1, -2)), axis=(-2, -1)) > 1e-10 * scale):
        raise ValueError(f"{name} must be symmetric")
    array = (array + array.swapaxes(-1, -2)) / 2
    if np.any(np.linalg.eigvalsh(array).min(axis=-1) < -1e-10 * scale):
        raise ValueError(f"{name} must be positive semidefinite")
    return array


def _weight_inverse(H: Any) -> np.ndarray:
    if np.iscomplexobj(H):
        raise ValueError("H must be real")
    weight = np.asarray(H, dtype=float)
    if weight.shape != (2, 2) or not np.isfinite(weight).all():
        raise ValueError("H must be a finite 2-by-2 matrix")
    scale = max(1.0, float(np.max(np.abs(weight))))
    if np.max(np.abs(weight - weight.T)) > 1e-10 * scale:
        raise ValueError("H must be symmetric positive definite")
    weight = (weight + weight.T) / 2
    if np.linalg.eigvalsh(weight).min() <= 0:
        raise ValueError("H must be symmetric positive definite")
    inverse = np.linalg.solve(weight, np.eye(2))
    if not np.isfinite(inverse).all():
        raise ValueError("H has no finite floating-point inverse")
    return inverse


def _finite_float(value: Any) -> float | None:
    if value is None:
        return None
    result = float(value)
    return result if np.isfinite(result) else None


def _backend_diagnostics(problem: cp.Problem) -> dict[str, Any]:
    """Best-effort backend statistics; a missing optional interface remains explicit."""
    result: dict[str, Any] = {
        "dual_objective": None,
        "primal_dual_gap": None,
        "relative_primal_dual_gap": None,
        "backend_primal_residual": None,
        "backend_dual_residual": None,
        "backend_statistics_source": None,
    }
    # CVXPY 1.7 does not forward these Clarabel statistics through extra_stats.
    # Reading its optional cache supplies diagnostics only; solving never depends on it.
    backend = getattr(problem, "_solver_cache", {}).get("CLARABEL")
    if backend is None or not hasattr(backend, "get_solution"):
        return result
    try:
        solution = backend.get_solution()
    except (AttributeError, RuntimeError, TypeError):
        return result
    primal = _finite_float(getattr(solution, "obj_val", None))
    dual = _finite_float(getattr(solution, "obj_val_dual", None))
    result["dual_objective"] = dual
    result["backend_primal_residual"] = _finite_float(getattr(solution, "r_prim", None))
    result["backend_dual_residual"] = _finite_float(getattr(solution, "r_dual", None))
    result["backend_statistics_source"] = "Clarabel.get_solution via optional CVXPY cache"
    if primal is not None and dual is not None:
        gap = abs(primal - dual)
        result["primal_dual_gap"] = gap
        result["relative_primal_dual_gap"] = gap / max(1.0, abs(primal), abs(dual))
    return result


def _quadratic_cost(
    blocks: list[tuple[np.ndarray, np.ndarray]], factor: float
) -> tuple[float | None, float]:
    """Evaluate tr(Z.T pinv(X) Z), checking the singular-X range condition."""
    cost, maximum_range_error, valid = 0.0, 0.0, True
    for X, Z in blocks:
        eigenvalues, eigenvectors = np.linalg.eigh((X + X.T) / 2)
        scale = max(1.0, float(np.max(np.abs(eigenvalues))))
        retained = eigenvalues > 1e-10 * scale
        inverse_eigenvalues = np.zeros(2)
        inverse_eigenvalues[retained] = 1 / eigenvalues[retained]
        inverse = (eigenvectors * inverse_eigenvalues) @ eigenvectors.T
        range_error = float(np.linalg.norm(Z - X @ inverse @ Z, "fro"))
        maximum_range_error = max(maximum_range_error, range_error)
        if eigenvalues.min() < -1e-7 * scale or range_error > 1e-7 * max(
            1.0, float(np.linalg.norm(Z, "fro"))
        ):
            valid = False
        cost += float(np.trace(Z.T @ inverse @ Z))
    return (factor * cost if valid else None), maximum_range_error


def _cone_diagnostics(blocks: list[np.ndarray]) -> tuple[float | None, float]:
    """Absolute minimum eigenvalue and maximum spectral-scale PSD violation."""
    spectra = [np.linalg.eigvalsh(block) for block in blocks]
    minimum = min((float(values.min()) for values in spectra), default=None)
    scaled = max((max(0.0, -float(values.min())) / max(1.0, float(np.max(np.abs(values))))
                  for values in spectra), default=0.0)
    return minimum, scaled


def solve_transport(
    initial: Any,
    final: Any,
    H: Any | None = None,
    *,
    nt: int = 20,
    tolerance: float = 1e-8,
    solver_options: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Solve the specified matrix SDP and return JSON-serializable arrays and diagnostics.

    ``H=None`` imposes R=0 and omits its epigraph. Otherwise H must be SPD.
    Mass lives at time knots and cell centers; flux includes both zero boundary
    faces, and reactions live at time midpoints and cell centers. Objectives are
    ``dt * dx / 2`` times the sums of their separate epigraph traces.
    Invalid inputs raise ValueError. Structurally incompatible balanced endpoints
    raise BalancedInfeasibleError before invoking the solver; other infeasible
    solves return their status with null solution data.
    Scaled residuals use a unit floor: CE terms use their cellwise Frobenius
    scales, endpoints their own Frobenius scales, and PSD cones their spectral
    scales. The signed epigraph slack compares against the independently
    recomputed objective; neither diagnostic repairs the returned solver values.
    """
    started = perf_counter()
    initial, final = _endpoints(initial, "initial"), _endpoints(final, "final")
    if initial.shape != final.shape:
        raise ValueError("initial and final must have identical shapes")
    if isinstance(nt, bool) or not isinstance(nt, (int, np.integer)) or nt < 1:
        raise ValueError("nt must be a positive integer")
    if not np.isfinite(tolerance) or tolerance <= 0:
        raise ValueError("tolerance must be finite and positive")
    nx = len(initial)
    dt, dx = 1.0 / nt, 1.0 / nx
    balanced = H is None
    H_inverse = None if balanced else _weight_inverse(H)
    initial_mass, final_mass = dx * initial.sum(axis=0), dx * final.sum(axis=0)
    if balanced and np.linalg.norm(final_mass - initial_mass, "fro") > 1e-9 * max(
        1.0, float(np.linalg.norm(initial_mass, "fro")), float(np.linalg.norm(final_mass, "fro"))
    ):
        raise BalancedInfeasibleError("balanced endpoints have unequal integrated matrices")

    rho = [[cp.Variable((2, 2), symmetric=True) for _ in range(nx)] for _ in range(nt + 1)]
    flux = [[cp.Variable((2, 2)) for _ in range(nx - 1)] for _ in range(nt)]
    reaction = None if balanced else [[cp.Variable((2, 2)) for _ in range(nx)] for _ in range(nt)]
    constraints = [G >> 0 for row in rho for G in row]
    constraints += [rho[0][i] == initial[i] for i in range(nx)]
    constraints += [rho[nt][i] == final[i] for i in range(nx)]
    Xcell = [[(rho[k][i] + rho[k + 1][i]) / 2 for i in range(nx)] for k in range(nt)]
    Sq, Sr, cone_blocks = [], [], []
    zero = np.zeros((2, 2))

    def sym(matrix: Any) -> Any:
        return (matrix + matrix.T) / 2

    for k in range(nt):
        for i in range(nx):
            left = zero if i == 0 else flux[k][i - 1]
            right = zero if i == nx - 1 else flux[k][i]
            R = zero if balanced else reaction[k][i]
            constraints.append(
                (rho[k + 1][i] - rho[k][i]) / dt + (sym(right) - sym(left)) / dx == sym(R)
            )
            if not balanced:
                S = cp.Variable((2, 2), symmetric=True)
                Z = R @ H_inverse
                block = cp.bmat([[Xcell[k][i], Z], [Z.T, S]])
                constraints.append(block >> 0)
                Sr.append(S)
                cone_blocks.append(block)
        for f in range(nx - 1):
            X = (Xcell[k][f] + Xcell[k][f + 1]) / 2
            Q, S = flux[k][f], cp.Variable((2, 2), symmetric=True)
            block = cp.bmat([[X, Q], [Q.T, S]])
            constraints.append(block >> 0)
            Sq.append(S)
            cone_blocks.append(block)

    factor = dt * dx / 2
    objective = factor * sum((cp.trace(S) for S in Sq + Sr), start=0)
    problem = cp.Problem(cp.Minimize(objective), constraints)
    options = {"tol_gap_abs": tolerance, "tol_gap_rel": tolerance, "tol_feas": tolerance, "max_iter": 300}
    options.update(dict(solver_options or {}))
    if "solver" in options:
        raise ValueError("solve_transport uses CLARABEL; solver_options cannot override solver")
    result: dict[str, Any] = {
        "status": None, "solver": "CLARABEL", "balanced": balanced, "nt": int(nt), "nx": nx,
        "dt": dt, "dx": dx, "time": np.linspace(0, 1, nt + 1).tolist(),
        "time_midpoints": ((np.arange(nt) + 0.5) * dt).tolist(),
        "x": ((np.arange(nx) + 0.5) * dx).tolist(), "x_faces": np.linspace(0, 1, nx + 1).tolist(),
        "rho": None, "flux": None, "reaction": None,
        "primal_total": None, "primal_transport": None, "primal_reaction": None,
        "independent_quadratic_cost": None, "reaction_tv": None, "diagnostics": None,
        "iterations": None, "runtime_seconds": None, "solver_time_seconds": None,
    }
    try:
        problem.solve(solver="CLARABEL", **options)
    except cp.error.SolverError as error:
        result.update(status="solver_error", reason=str(error), runtime_seconds=perf_counter() - started)
        return result
    result.update(
        status=problem.status, iterations=problem.solver_stats.num_iters,
        solver_time_seconds=_finite_float(problem.solver_stats.solve_time),
        runtime_seconds=perf_counter() - started,
    )
    if problem.status not in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE):
        return result
    G = np.asarray([[cell.value for cell in row] for row in rho])
    Q = np.zeros((nt, nx + 1, 2, 2))
    if nx > 1:
        Q[:, 1:-1] = np.asarray([[face.value for face in row] for row in flux])
    R = np.zeros((nt, nx, 2, 2)) if balanced else np.asarray([[cell.value for cell in row] for row in reaction])
    if not all(np.isfinite(array).all() for array in (G, Q, R)):
        result.update(status="invalid_solution", reason="nonfinite solver values")
        return result
    X = (G[:-1] + G[1:]) / 2
    Qsym, Rsym = (Q + Q.swapaxes(-1, -2)) / 2, (R + R.swapaxes(-1, -2)) / 2
    time_term = (G[1:] - G[:-1]) / dt
    divergence_term = (Qsym[:, 1:] - Qsym[:, :-1]) / dx
    ce = time_term + divergence_term - Rsym
    ce_norm = np.linalg.norm(ce, axis=(-2, -1))
    ce_scale = np.maximum.reduce([np.ones_like(ce_norm),
        np.linalg.norm(time_term, axis=(-2, -1)), np.linalg.norm(divergence_term, axis=(-2, -1)),
        np.linalg.norm(Rsym, axis=(-2, -1))])
    initial_error = np.linalg.norm(G[0] - initial, axis=(-2, -1))
    final_error = np.linalg.norm(G[-1] - final, axis=(-2, -1))
    transport = factor * sum(float(np.trace(S.value)) for S in Sq)
    reaction_cost = factor * sum(float(np.trace(S.value)) for S in Sr)
    qblocks = [((X[k, f] + X[k, f + 1]) / 2, Q[k, f + 1]) for k in range(nt) for f in range(nx - 1)]
    rblocks = [] if balanced else [(X[k, i], R[k, i] @ H_inverse) for k in range(nt) for i in range(nx)]
    qcost, qrange = _quadratic_cost(qblocks, factor)
    rcost, rrange = _quadratic_cost(rblocks, factor)
    independent_total = None if qcost is None or rcost is None else qcost + rcost
    cone_min, cone_scaled = _cone_diagnostics([block.value for block in cone_blocks])
    diagnostics = {
        "ce_max_frobenius_residual": float(ce_norm.max()),
        "ce_max_scaled_residual": float((ce_norm / ce_scale).max()),
        "endpoint_max_frobenius_residual": float(max(initial_error.max(), final_error.max())),
        "endpoint_max_scaled_residual": float(max(
            (initial_error / np.maximum(1.0, np.linalg.norm(initial, axis=(-2, -1)))).max(),
            (final_error / np.maximum(1.0, np.linalg.norm(final, axis=(-2, -1)))).max())),
        "rho_min_eigenvalue": float(np.linalg.eigvalsh(G).min()),
        "cone_min_eigenvalue": cone_min,
        "cone_max_scaled_violation": cone_scaled,
        "independent_objective_epigraph_slack": None if independent_total is None else
            transport + reaction_cost - independent_total,
        "max_rho_symmetry_error": float(np.linalg.norm(G - G.swapaxes(-1, -2), axis=(-2, -1)).max()),
        "boundary_flux_max_frobenius": float(np.linalg.norm(Q[:, [0, -1]], axis=(-2, -1)).max()),
        "integrated_mass_balance_frobenius_residual": float(np.linalg.norm(
            dx * (G[-1].sum(axis=0) - G[0].sum(axis=0)) - dt * dx * Rsym.sum(axis=(0, 1)), "fro")),
        **_backend_diagnostics(problem),
    }
    result.update(
        rho=G.tolist(), flux=Q.tolist(), reaction=R.tolist(),
        primal_total=transport + reaction_cost, primal_transport=transport, primal_reaction=reaction_cost,
        independent_quadratic_cost={
            "total": independent_total,
            "transport": qcost, "reaction": rcost,
            "max_range_residual": max(qrange, rrange),
            "range_check_tolerance": 1e-7,
        },
        reaction_tv=float(dt * dx * np.linalg.norm(R, axis=(-2, -1)).sum()),
        diagnostics=diagnostics,
    )
    result["runtime_seconds"] = perf_counter() - started
    return result
