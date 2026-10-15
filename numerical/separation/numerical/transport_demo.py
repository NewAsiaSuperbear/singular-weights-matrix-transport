"""Deterministic illustration of the bump-perturbation transport quantities (not an OT distance computation)."""
from typing import NamedTuple

import numpy as np

SEED = 921
R_DEFAULT = 0.4
EPS_DEFAULT = 0.25


class Grid(NamedTuple):
    R: float
    x: np.ndarray
    y: np.ndarray
    w: np.ndarray
    chi: np.ndarray
    chi_x: np.ndarray


def _is_int(n):
    return isinstance(n, (int, np.integer)) and not isinstance(n, bool)


def _check_R(R):
    if not (np.isfinite(R) and 0 < R < 0.5):
        raise ValueError("R must be finite with 0 < R < 0.5")


def _check_params(R, epsilon, j):
    _check_R(R)
    if not (np.isfinite(epsilon) and 0 < epsilon <= 0.25):
        raise ValueError("epsilon must be finite with 0 < epsilon <= 0.25")
    if not _is_int(j) or j < 2:
        raise ValueError("j must be an integer >= 2")


def bump(x, y, R=R_DEFAULT):
    """chi = exp(1 - 1/(1 - r^2/R^2)) inside r < R, zero elsewhere."""
    _check_R(R)
    x, y = np.asarray(x, float), np.asarray(y, float)
    if not (np.all(np.isfinite(x)) and np.all(np.isfinite(y))):
        raise ValueError("coordinates must be finite")
    s = np.broadcast_to((x * x + y * y) / (R * R), np.broadcast(x, y).shape)
    out = np.zeros(s.shape)
    m = s < 1
    out[m] = np.exp(1.0 - 1.0 / (1.0 - s[m]))
    return out[()]


def bump_dx(x, y, R=R_DEFAULT):
    """x-derivative of the bump; exactly zero on and outside the boundary."""
    _check_R(R)
    x, y = np.asarray(x, float), np.asarray(y, float)
    if not (np.all(np.isfinite(x)) and np.all(np.isfinite(y))):
        raise ValueError("coordinates must be finite")
    shape = np.broadcast(x, y).shape
    s = np.broadcast_to((x * x + y * y) / (R * R), shape)
    xb = np.broadcast_to(x, shape)
    out = np.zeros(shape)
    m = s < 1
    out[m] = -2.0 * xb[m] * np.exp(1.0 - 1.0 / (1.0 - s[m])) / (R * R * (1.0 - s[m]) ** 2)
    return out[()]


def log1p_ratio(z):
    """L(z) = log1p(z)/z with L(0) = 1; requires finite z > -1."""
    z = np.asarray(z, float)
    if not np.all(np.isfinite(z)) or np.any(z <= -1):
        raise ValueError("z must be finite and > -1")
    small = np.abs(z) < 1e-7
    zs = np.where(small, 1.0, z)
    out = np.where(small, 1.0 - z / 2.0 + z * z / 3.0, np.log1p(zs) / zs)
    return out[()]


def disk_grid(R=R_DEFAULT, nr=128, ntheta=1024):
    """Gauss-Legendre in r on [0,R] times periodic trapezoid in theta; weights include r."""
    _check_R(R)
    if not (_is_int(nr) and _is_int(ntheta) and nr >= 1 and ntheta >= 1):
        raise ValueError("nr and ntheta must be positive integers")
    nodes, wts = np.polynomial.legendre.leggauss(nr)
    r, wr = 0.5 * R * (nodes + 1), 0.5 * R * wts
    th = 2 * np.pi * np.arange(ntheta) / ntheta
    rr, tt = np.meshgrid(r, th, indexing="ij")
    w = ((wr * r)[:, None] * np.full(ntheta, 2 * np.pi / ntheta)[None, :]).ravel()
    x, y = (rr * np.cos(tt)).ravel(), (rr * np.sin(tt)).ravel()
    return Grid(float(R), x, y, w, bump(x, y, R), bump_dx(x, y, R))


def analytic_rho_bound(R, epsilon, j):
    """Analytic bound on max|rho| using max|chi_x| <= 8/(e R)."""
    _check_params(R, epsilon, j)
    return epsilon * (1.0 + 8.0 / (np.e * R * 2 * np.pi * j))


def test_function_coefficients(seed=SEED, n=6):
    """Rows (a, b, phase) for cos(a x + b y + phase); a, b ~ U[-2,2], phase ~ U[-pi,pi]."""
    if not _is_int(n) or n < 1:
        raise ValueError("n must be a positive integer")
    rng = np.random.default_rng(seed)
    ab = rng.uniform(-2.0, 2.0, size=(n, 2))
    phase = rng.uniform(-np.pi, np.pi, size=(n, 1))
    return np.hstack([ab, phase])


def wave_fields(x, y, j, R=R_DEFAULT, epsilon=EPS_DEFAULT):
    """Return h and rho for the explicit smooth example; G22 = 1 + rho."""
    _check_params(R, epsilon, j)
    if analytic_rho_bound(R, epsilon, j) > 0.5:
        raise ValueError("unsupported demonstration parameters: analytic |rho| bound must be <= 0.5")
    x = np.asarray(x, float)
    k = 2 * np.pi * j
    chi = bump(x, y, R)
    h = chi * np.sin(k * x) / k
    rho = epsilon * (chi * np.cos(k * x) + bump_dx(x, y, R) * np.sin(k * x) / k)
    return h, rho


def frequency_result(j, grid, epsilon=EPS_DEFAULT, coeffs=None):
    """Scalar diagnostics and illustrative weak-star pairings for frequency j."""
    _check_params(grid.R, epsilon, j)
    if analytic_rho_bound(grid.R, epsilon, j) > 0.5:
        raise ValueError("unsupported demonstration parameters: analytic |rho| bound must be <= 0.5")
    for a in (grid.x, grid.y, grid.w, grid.chi, grid.chi_x):
        if not np.all(np.isfinite(a)):
            raise ValueError("grid contains non-finite values")
    coeffs = test_function_coefficients() if coeffs is None else np.asarray(coeffs, float)
    if coeffs.ndim != 2 or coeffs.shape[1] != 3 or not np.all(np.isfinite(coeffs)):
        raise ValueError("coeffs must be a finite array of shape (n, 3)")

    k = 2 * np.pi * j
    x, w, chi = grid.x, grid.w, grid.chi
    sx, cx = np.sin(k * x), np.cos(k * x)
    h = chi * sx / k
    rho = epsilon * (chi * cx + grid.chi_x * sx / k)
    L = log1p_ratio(rho)

    def integ(v):
        return float(np.sum(w * v))

    beta_ibp = epsilon * integ(chi * sx**2)
    bound = analytic_rho_bound(grid.R, epsilon, j)
    g22 = 1.0 + rho
    res = {
        "j": int(j),
        "full_path_upper": 0.5 * integ(epsilon**2 * h**2 * L),
        "reaction_path_upper": 0.5 * integ(rho**2 * L),
        "beta_direct": integ(rho * cx),
        "beta_ibp": beta_ibp,
        "kb_certificate_lower": beta_ibp**2 / (4 * np.pi),
        "full_generic_upper": epsilon**2 * integ(chi**2) / k**2,
        "mass_perturbation": integ(rho),
        "certificate_s": beta_ibp / (2 * np.pi),
        "positive_eigenvalue_bound": 1.0 - bound,
        "rho_abs_sample_max": float(np.max(np.abs(rho))),
        "g22_sample_min": float(np.min(g22)),
        "g22_sample_max": float(np.max(g22)),
        "bump_mass": integ(chi),
        "bump_squared_mass": integ(chi**2),
        "kb_limit": epsilon**2 * integ(chi) ** 2 / (16 * np.pi),
    }
    for i, (a, b, ph) in enumerate(coeffs):
        res[f"pairing_{i}"] = integ(rho * np.cos(a * x + b * grid.y + ph))
    return res
