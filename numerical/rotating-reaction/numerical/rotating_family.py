"""Closed form and actual optimal paths, without a numerical optimizer.

Endpoints are uniform I2 and diag(2,1) on a unit-volume spatial domain.
The operator is standard entrywise divergence with no flux through the boundary.
H = U(theta) diag(1, epsilon) U(theta).T, epsilon > 0. The transport
weight can be any fixed PSD matrix: the spatially uniform reaction path is
globally optimal, as proved by the spatially constant dual field in the
manuscript's pure-reaction lemma (sections/bures.tex, Lemma lem:pure) and its
rotating-family proposition (sections/examples.tex, Proposition prop:reactionrotation).
This module does not make a claim about arbitrary endpoints or operators.
"""

from __future__ import annotations

import math
from typing import Any

import numpy as np

SEED = 921  # Project seed label: "0921"; computations here are deterministic.
SQRT2 = math.sqrt(2.0)
G0 = np.eye(2)
G1 = np.diag([2.0, 1.0])
SINGULAR_TARGET_ACTION = 2.0 * (SQRT2 - 1.0) ** 2


def _parameters(epsilon: float, theta: float) -> tuple[float, float]:
    epsilon, theta = float(epsilon), float(theta)
    if not math.isfinite(epsilon) or epsilon <= 0:
        raise ValueError("epsilon must be finite and strictly positive")
    if not math.isfinite(theta):
        raise ValueError("theta must be finite")
    return epsilon, theta


def _trig(epsilon: float, theta: float) -> tuple[float, float, float, float]:
    epsilon, theta = _parameters(epsilon, theta)
    c, s = math.cos(theta), math.sin(theta)
    e2 = epsilon * epsilon
    z = 1.0 + s * s + 2.0 * SQRT2 * e2 + (1.0 + c * c) * e2 * e2
    if not math.isfinite(z):
        raise ValueError("parameters exceed the safe float64 evaluation range")
    return c, s, e2, math.sqrt(z)


def exact_action(epsilon: float, theta: float) -> float:
    """Return 2*Bures^2 using the rationalized expression, not eps^-2 subtraction.

    q=sin(theta)^2. The large nonnegative term is isolated as
    2*(q/epsilon)^2/(sqrt(1+q)+1)^2; all remaining terms stay bounded
    in the vanishing-weight regime. The factor two is the original CE/action
    normalization, where dG/dt = sym(R) and the integrand has a factor 1/2.
    """
    epsilon, theta = _parameters(epsilon, theta)
    _, s, e2, root_z = _trig(epsilon, theta)
    q = s * s
    root_q = math.sqrt(1.0 + q)
    scaled = (q / epsilon) / (root_q + 1.0)
    action = (2.0 * (3.0 - q) + 2.0 * scaled * scaled
              - 4.0 * (2.0 * SQRT2 + (2.0 - q) * e2) / (root_z + root_q))
    if not math.isfinite(action) or action < 0:
        raise ValueError("action is outside the reliable float64 evaluation range")
    return float(action)


def optimal_factor(epsilon: float, theta: float) -> np.ndarray:
    """Return A with A A.T=G1 and A K symmetric PD, K=H^2.

    A=(epsilon^2 G1 K^-1 + sqrt(2) K)/sqrt(z), evaluated entrywise so
    no ill-conditioned matrix inverse or square root is computed.
    """
    c, s, e2, root_z = _trig(epsilon, theta)
    return np.array([
        [2.0 * (e2 * c * c + s * s) + SQRT2 * (c * c + e2 * s * s),
         (SQRT2 - 2.0) * (1.0 - e2) * c * s],
        [(SQRT2 - 1.0) * (1.0 - e2) * c * s,
         e2 * s * s + c * c + SQRT2 * (s * s + e2 * c * c)],
    ]) / root_z


def _optimal_increment(epsilon: float, theta: float) -> np.ndarray:
    """Compute A-I without subtracting one from a nearly unit A22.

    If N22 is the numerator of A22, N22^2-z equals
    -(sqrt(2)-1)^2 sin^2(theta) cos^2(theta) (1-epsilon^2)^2.
    Rationalization retains this O(theta^2) increment before the small
    reaction weight amplifies it in the independent quadratic-cost check.
    """
    c, s, e2, root_z = _trig(epsilon, theta)
    delta = optimal_factor(epsilon, theta) - G0
    n22 = e2 * s * s + c * c + SQRT2 * (s * s + e2 * c * c)
    delta[1, 1] = -(SQRT2 - 1.0) ** 2 * s * s * c * c * (1.0 - e2) ** 2 / (
        root_z * (n22 + root_z))
    return delta


def optimal_path(epsilon: float, theta: float, times: Any = None) -> dict[str, Any]:
    """Evaluate the actual globally optimal uniform G,R path at given times.

    F(t)=I+t(A-I), G(t)=F(t)F(t).T, R(t)=2F(t)(A-I).T, q=0.
    R is retained as a full matrix. Arrays are not JSON-converted here.
    """
    epsilon, theta = _parameters(epsilon, theta)
    t = np.asarray(np.linspace(0.0, 1.0, 201) if times is None else times, dtype=float)
    if t.ndim != 1 or t.size == 0 or not np.isfinite(t).all():
        raise ValueError("times must be a nonempty finite one-dimensional array")
    if np.any(t < 0) or np.any(t > 1) or np.any(np.diff(t) < 0):
        raise ValueError("times must be ordered and lie in [0,1]")
    c, s, e2, root_z = _trig(epsilon, theta)
    rotation = np.array([[c, -s], [s, c]])
    weight = (rotation * np.array([1.0, epsilon])) @ rotation.T
    covariance = (rotation * np.array([1.0, e2])) @ rotation.T
    factor = optimal_factor(epsilon, theta)
    delta = _optimal_increment(epsilon, theta)
    ft = G0 + t[:, None, None] * delta
    mass = ft @ np.swapaxes(ft, -1, -2)
    reaction = 2.0 * ft @ delta.T
    derivative = delta @ np.swapaxes(ft, -1, -2) + ft @ delta.T
    return {
        "epsilon": epsilon, "theta": theta, "times": t,
        "mass": mass, "reaction": reaction,
        "flux": np.zeros_like(reaction), "mass_derivative": derivative,
        "factor": factor, "increment": delta,
        "weight": weight, "covariance": covariance,
        "rotation": rotation, "root_z": root_z,
        "exact_action": exact_action(epsilon, theta),
    }


def quadratic_energy_density(mass: Any, reaction: Any,
                             epsilon: float, theta: float) -> np.ndarray:
    """Independently evaluate 1/2 tr((R H^-1).T G^-1 (R H^-1)).

    Weighting the rotated columns is equivalent to R H^-1 but avoids an
    unnecessary recombination of its potentially large entries. This function
    uses the actual path matrices and a linear solve, not the cost closed form.
    """
    epsilon, theta = _parameters(epsilon, theta)
    g, r = np.asarray(mass, dtype=float), np.asarray(reaction, dtype=float)
    if g.shape != r.shape or g.shape[-2:] != (2, 2):
        raise ValueError("mass and reaction must have matching (...,2,2) shapes")
    if not np.isfinite(g).all() or not np.isfinite(r).all():
        raise ValueError("mass and reaction must be finite")
    if not np.allclose(g, np.swapaxes(g, -1, -2), rtol=1e-12, atol=1e-12):
        raise ValueError("mass must be symmetric")
    if np.any(np.linalg.eigvalsh(g) <= 0):
        raise ValueError("mass must be positive definite for the independent cost")
    c, s = math.cos(theta), math.sin(theta)
    rotation = np.array([[c, -s], [s, c]])
    weighted = r @ rotation
    weighted[..., 1] /= epsilon
    solved = np.linalg.solve(g, weighted)
    return 0.5 * np.sum(weighted * solved, axis=(-2, -1))


def path_diagnostics(path: dict[str, Any]) -> dict[str, float | None]:
    """Floating-point consistency checks; these are not an optimizer certificate."""
    g, r, dg = path["mass"], path["reaction"], path["mass_derivative"]
    factor, k = path["factor"], path["covariance"]
    sym_r = 0.5 * (r + np.swapaxes(r, -1, -2))
    ce = float(np.max(np.linalg.norm(dg - sym_r, axis=(-2, -1))))
    ce_scale = max(1.0, float(np.max(np.linalg.norm(dg, axis=(-2, -1)))),
                   float(np.max(np.linalg.norm(sym_r, axis=(-2, -1)))))
    energy = quadratic_energy_density(g, r, path["epsilon"], path["theta"])
    value = path["exact_action"]
    scale = max(1.0, abs(value))
    ak = factor @ k
    ak_sym = 0.5 * (ak + ak.T)
    t = path["times"]
    endpoints_present = t[0] == 0.0 and t[-1] == 1.0
    endpoint = (max(float(np.linalg.norm(g[0] - G0)), float(np.linalg.norm(g[-1] - G1)))
                if endpoints_present else None)
    integral = float(np.trapezoid(energy, t)) if endpoints_present else None
    return {
        "factor_endpoint_residual": float(np.linalg.norm(factor @ factor.T - G1)),
        "ak_symmetry_error": float(np.linalg.norm(ak - ak.T)),
        "ak_min_eigenvalue": float(np.linalg.eigvalsh(ak_sym).min()),
        "ak_theoretical_eigenvalue_lower_bound": path["epsilon"] ** 2 / path["root_z"],
        "mass_min_eigenvalue": float(np.linalg.eigvalsh(g).min()),
        "mass_symmetry_error": float(np.max(np.linalg.norm(g - np.swapaxes(g, -1, -2),
                                                         axis=(-2, -1)))),
        "endpoint_residual": endpoint,
        "endpoint_scaled_residual": None if endpoint is None else endpoint / np.linalg.norm(G1),
        "ce_residual": ce, "ce_scaled_residual": ce / ce_scale,
        "energy_density_mean": float(np.mean(energy)),
        "energy_density_relative_error": float(np.max(np.abs(energy - value))) / scale,
        "energy_density_constancy_relative_error": float(np.ptp(energy)) / scale,
        "independent_action": integral,
        "independent_action_relative_error": None if integral is None else abs(integral - value) / scale,
        "boundary_flux_norm": 0.0,
    }
