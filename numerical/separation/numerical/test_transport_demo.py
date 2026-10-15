import numpy as np
import pytest

from numerical.transport_demo import (
    EPS_DEFAULT, R_DEFAULT, analytic_rho_bound, bump, bump_dx, disk_grid,
    frequency_result, log1p_ratio, wave_fields, test_function_coefficients as make_coeffs,
)

R = R_DEFAULT


def test_bump_center_support_and_derivative():
    assert bump(0.0, 0.0) == 1.0
    assert bump(R, 0.0) == 0.0 and bump(0.0, -R) == 0.0
    assert bump(0.3, 0.3) == 0.0 and bump(2.0, 1.0) == 0.0
    xs, ys = np.meshgrid(np.linspace(-0.45, 0.45, 41), np.linspace(-0.45, 0.45, 41))
    v = bump(xs, ys)
    assert np.all(v >= 0) and np.all(v <= 1)
    for (x0, y0) in [(0.13, 0.07), (-0.21, 0.15), (0.05, -0.3)]:
        d = 1e-6
        fd = (bump(x0 + d, y0) - bump(x0 - d, y0)) / (2 * d)
        assert bump_dx(x0, y0) == pytest.approx(fd, rel=1e-6, abs=1e-9)
    for p in [(R, 0.0), (0.0, R), (0.5, 0.1), (-1.0, 0.0)]:
        g = bump_dx(*p)
        assert np.isfinite(g) and g == 0.0


def test_invalid_parameters_rejected():
    for bad_R in (0.0, -0.1, 0.5, 0.6, np.nan, np.inf):
        with pytest.raises(ValueError):
            disk_grid(bad_R, 8, 8)
    for nr, nt in [(0, 8), (8, 0), (-3, 8), (8.5, 8), (8, 2.0)]:
        with pytest.raises(ValueError):
            disk_grid(R, nr, nt)
    g = disk_grid(R, 8, 16)
    for bad_eps in (0.0, -0.1, 0.26, np.nan, np.inf):
        with pytest.raises(ValueError):
            frequency_result(2, g, bad_eps)
    for bad_j in (1, 0, -2, 2.5, True, "3"):
        with pytest.raises(ValueError):
            frequency_result(bad_j, g)
        with pytest.raises(ValueError):
            analytic_rho_bound(R, EPS_DEFAULT, bad_j)
    with pytest.raises(ValueError):
        frequency_result(2, g._replace(x=np.full_like(g.x, np.nan)))
    with pytest.raises(ValueError):
        frequency_result(2, g, coeffs=np.zeros((6, 2)))
    for func in (bump, bump_dx):
        with pytest.raises(ValueError):
            func(np.nan, 0.0)
        with pytest.raises(ValueError):
            func(0.0, 0.0, R=0.5)


def test_small_radius_requires_supported_positive_endpoint_bound():
    # Small bump radii are valid, but the chosen low frequency may no longer
    # provide the analytic half-to-three-halves guarantee used by this demo.
    assert bump(0.0, 0.0, R=0.01) == 1.0
    small_grid = disk_grid(0.01, 8, 16)
    assert analytic_rho_bound(0.01, EPS_DEFAULT, 2) > 0.5
    with pytest.raises(ValueError, match="analytic.*rho.*bound"):
        wave_fields(0.0, 0.0, 2, R=0.01)
    with pytest.raises(ValueError, match="analytic.*rho.*bound"):
        frequency_result(2, small_grid)


@pytest.mark.parametrize("j", [2, 8, 64])
def test_wave_derivative_and_affine_continuity_equation(j):
    # Independent centered differences of h and of the affine path verify the
    # derivative and flux sign used to construct the feasible full-model path.
    step = 1e-7
    for x, y in [(0.13, 0.07), (-0.21, 0.15), (0.05, -0.3)]:
        hp, _ = wave_fields(x + step, y, j)
        hm, _ = wave_fields(x - step, y, j)
        _, rho = wave_fields(x, y, j)
        h_dx = (hp - hm) / (2 * step)
        assert rho / EPS_DEFAULT == pytest.approx(h_dx, rel=3e-6, abs=1e-8)
        t = 0.37
        g_dt = ((1 + (t + step) * rho) - (1 + (t - step) * rho)) / (2 * step)
        q_dx = -EPS_DEFAULT * h_dx
        assert g_dt + q_dx == pytest.approx(0.0, abs=2e-8)


def test_log1p_ratio_against_time_integral():
    t, wt = np.polynomial.legendre.leggauss(60)
    t, wt = 0.5 * (t + 1), 0.5 * wt

    def ref(z):
        return float(np.sum(wt / (1.0 + t * z)))

    for z in [-0.9, -0.5, -1e-3, -1e-9, 1e-9, 1e-8, 5e-8, 2e-7, 1e-3, 0.3, 2.0]:
        assert log1p_ratio(z) == pytest.approx(ref(z), rel=1e-11)
    assert log1p_ratio(0.0) == 1.0
    assert log1p_ratio(0.99e-7) == pytest.approx(log1p_ratio(1.01e-7), rel=1e-7)
    zs = np.array([[-0.5, 0.0], [1e-9, 0.3]])
    out = log1p_ratio(zs)
    assert out.shape == zs.shape
    assert out[0, 0] == pytest.approx(ref(-0.5), rel=1e-11)
    for bad in (-1.0, -2.0, np.nan, np.inf):
        with pytest.raises(ValueError):
            log1p_ratio(bad)
    with pytest.raises(ValueError):
        log1p_ratio(np.array([0.1, -1.0]))


def test_disk_quadrature_exactness():
    for nr, nt in [(16, 32), (64, 128)]:
        g = disk_grid(R, nr, nt)
        assert g.w.shape == g.x.shape == g.chi.shape == g.chi_x.shape == (nr * nt,)
        assert np.sum(g.w) == pytest.approx(np.pi * R**2, rel=1e-12)
        assert np.sum(g.w * g.x**2) == pytest.approx(np.pi * R**4 / 4, rel=1e-12)
        assert np.sum(g.w * g.x * g.y) == pytest.approx(0.0, abs=1e-14)


@pytest.mark.parametrize("j", [2, 8])
def test_mass_beta_and_bounds(j):
    g = disk_grid(R, 96, 512)
    r = frequency_result(j, g)
    assert abs(r["mass_perturbation"]) < 1e-9
    assert r["beta_direct"] == pytest.approx(r["beta_ibp"], abs=1e-9)
    assert r["full_path_upper"] <= r["full_generic_upper"]
    assert r["kb_certificate_lower"] <= r["reaction_path_upper"]
    bound = analytic_rho_bound(R, EPS_DEFAULT, j)
    assert bound < 0.5
    assert r["rho_abs_sample_max"] <= bound
    assert r["positive_eigenvalue_bound"] == pytest.approx(1 - bound)
    assert r["g22_sample_min"] >= r["positive_eigenvalue_bound"] > 0.5
    assert 0 <= r["certificate_s"] <= EPS_DEFAULT * R**2 / 2 <= 0.125


def test_seed_determinism_and_shapes():
    c1, c2, c3 = make_coeffs(), make_coeffs(), make_coeffs(seed=922)
    assert c1.shape == (6, 3)
    assert np.array_equal(c1, c2)
    assert not np.array_equal(c1, c3)
    assert np.all(np.abs(c1[:, :2]) <= 2) and np.all(np.abs(c1[:, 2]) <= np.pi)
    g = disk_grid(R, 32, 64)
    r1, r2 = frequency_result(3, g), frequency_result(3, g)
    keys = [f"pairing_{i}" for i in range(6)]
    assert all(k in r1 for k in keys) and "pairing_6" not in r1
    assert [r1[k] for k in keys] == [r2[k] for k in keys]
    r3 = frequency_result(3, g, coeffs=c3)
    assert [r1[k] for k in keys] != [r3[k] for k in keys]


def test_high_frequency_reaction_quadrature_convergence():
    # Regression for insufficient coarse-grid resolution in the nonlinear
    # time-integrated reaction action at the largest configured frequency.
    medium = frequency_result(64, disk_grid(R, 256, 2048))
    fine = frequency_result(64, disk_grid(R, 384, 3072))
    assert abs(medium["reaction_path_upper"] - fine["reaction_path_upper"]) <= 1e-9
