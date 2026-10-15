"""Analytic and conservation checks, not a parameter-sweep experiment."""

import json

import numpy as np
import pytest

from numerical import BalancedInfeasibleError, solve_transport


def assert_feasible(result, tolerance=2e-6):
    assert result["status"] in {"optimal", "optimal_inaccurate"}
    diagnostics = result["diagnostics"]
    assert diagnostics["ce_max_frobenius_residual"] < tolerance
    assert diagnostics["endpoint_max_frobenius_residual"] < tolerance
    assert 0 <= diagnostics["ce_max_scaled_residual"] <= diagnostics["ce_max_frobenius_residual"]
    assert 0 <= diagnostics["endpoint_max_scaled_residual"] <= diagnostics["endpoint_max_frobenius_residual"]
    assert 0 <= diagnostics["cone_max_scaled_violation"] < tolerance
    assert diagnostics["rho_min_eigenvalue"] > -tolerance
    if diagnostics["cone_min_eigenvalue"] is not None:
        assert diagnostics["cone_min_eigenvalue"] > -tolerance
    assert diagnostics["max_rho_symmetry_error"] < tolerance
    assert diagnostics["integrated_mass_balance_frobenius_residual"] < tolerance
    assert diagnostics["boundary_flux_max_frobenius"] == 0
    json.dumps(result, allow_nan=False)


@pytest.mark.parametrize("H", [None, np.eye(2)])
def test_identical_spd_endpoints_have_zero_cost(H):
    initial = np.repeat(np.array([[[1.2, 0.15], [0.15, 0.8]]]), 2, axis=0)
    # A quadratic objective controls fields only at the square root of its accuracy.
    # Request tighter accuracy to check a tiny reaction field in this zero-cost case.
    result = solve_transport(initial, initial, H, nt=3, tolerance=1e-12)
    assert_feasible(result)
    assert result["primal_total"] == pytest.approx(0, abs=2e-7)
    assert result["reaction_tv"] == pytest.approx(0, abs=2e-6)


def test_one_cell_reaction_matches_continuous_scalar_benchmark():
    initial, final = np.array([np.diag([1.0, 0.0])]), np.array([np.diag([4.0, 0.0])])
    epsilon = 0.5
    result = solve_transport(initial, final, epsilon * np.eye(2), nt=20)
    assert_feasible(result)
    # Continuous Fisher--Rao reaction action: 2*(sqrt(4)-sqrt(1))**2 / epsilon**2.
    assert result["primal_total"] == pytest.approx(2 / epsilon**2, rel=0.01)
    assert result["primal_transport"] == 0
    assert np.shape(result["flux"]) == (20, 2, 2, 2)
    independent = result["independent_quadratic_cost"]["total"]
    assert independent is not None
    assert independent == pytest.approx(result["primal_total"], rel=2e-5)
    assert abs(result["diagnostics"]["independent_objective_epigraph_slack"]) < 2e-5


def test_one_cell_reaction_energy_scales_as_inverse_weight_squared():
    initial, final = np.array([np.diag([1.0, 0.0])]), np.array([np.diag([4.0, 0.0])])
    unit = solve_transport(initial, final, np.eye(2), nt=8)
    half = solve_transport(initial, final, 0.5 * np.eye(2), nt=8)
    assert_feasible(unit)
    assert_feasible(half)
    assert half["primal_total"] == pytest.approx(4 * unit["primal_total"], rel=2e-5)


def test_balanced_unequal_integrated_matrices_rejected_before_solver(monkeypatch):
    import cvxpy as cp

    def no_solver(*args, **kwargs):
        pytest.fail("structurally infeasible balanced data reached the solver")

    monkeypatch.setattr(cp.Problem, "solve", no_solver)
    # Equal traces are insufficient for this entrywise-divergence model.
    with pytest.raises(BalancedInfeasibleError, match="unequal integrated matrices"):
        solve_transport(np.array([np.diag([1.0, 0.0])]), np.array([np.diag([0.0, 1.0])]), nt=3)


def test_balanced_transport_conserves_full_matrix_and_is_feasible():
    A, B = np.array([[1.3, 0.2], [0.2, 0.4]]), np.array([[0.5, -0.1], [-0.1, 1.1]])
    result = solve_transport(np.array([A, B]), np.array([B, A]), nt=6)
    assert_feasible(result)
    rho = np.asarray(result["rho"])
    np.testing.assert_allclose(rho.sum(axis=1), np.broadcast_to(A + B, (7, 2, 2)), atol=2e-6)
    assert result["primal_transport"] > 0
    assert result["primal_reaction"] == 0
    assert result["reaction_tv"] == 0
    # With two cells, Xface=(A+B)/2 is constant by conservation. Minimizing over
    # Q=S+aJ with sym(Q)=S gives a closed-form benchmark for the unrestricted flux.
    P, S = np.linalg.inv((A + B) / 2), (A - B) / 2
    J = np.array([[0.0, 1.0], [-1.0, 0.0]])
    a = -np.trace(J.T @ P @ S) / np.trace(J.T @ P @ J)
    Q = S + a * J
    expected = 0.25 * np.trace(Q.T @ P @ Q)
    assert result["primal_transport"] == pytest.approx(expected, rel=2e-6)
    assert np.max(np.abs(np.asarray(result["flux"])[:, 1, 0, 1]
                         - np.asarray(result["flux"])[:, 1, 1, 0])) > 1e-3


@pytest.mark.parametrize("initial", [np.zeros((2, 2)), np.array([np.diag([-0.1, 1.0])]),
                                      np.array([[[1.0, 0.3], [0.1, 1.0]]]),
                                      np.array([[[np.nan, 0.0], [0.0, 1.0]]]),
                                      np.array([np.diag([1.0 + 1j, 1.0])])])
def test_invalid_endpoints_are_rejected(initial):
    with pytest.raises(ValueError):
        solve_transport(initial, np.array([np.eye(2)]), np.eye(2), nt=2)


@pytest.mark.parametrize("H", [np.diag([1.0, 0.0]), np.diag([1.0, -1.0]), np.ones((3, 3)),
                                np.array([[1.0, 0.2], [0.0, 1.0]]), np.diag([np.inf, 1.0]),
                                np.diag([1.0 + 1j, 1.0])])
def test_invalid_reaction_weights_are_rejected(H):
    with pytest.raises(ValueError):
        solve_transport(np.array([np.eye(2)]), np.array([np.eye(2)]), H, nt=2)


def test_endpoint_psd_validation_uses_each_cells_scale():
    data = np.array([np.diag([1e12, 1e12]), np.diag([-0.1, 1.0])])
    # A large valid cell must not hide a materially negative eigenvalue in another cell.
    with pytest.raises(ValueError, match="positive semidefinite"):
        solve_transport(data, data, np.eye(2), nt=2)


def test_cone_violation_is_spectral_scale_normalized_and_has_unit_floor():
    from numerical.solver import _cone_diagnostics

    large = np.diag([-2.0, 1.0, 3.0, 1000.0])
    minimum, normalized = _cone_diagnostics([large])
    assert minimum == -2
    assert normalized == pytest.approx(0.002)
    # Scaling a cone beyond the unit floor changes its absolute error but not this diagnostic.
    assert _cone_diagnostics([10 * large]) == pytest.approx((-20.0, normalized))
    small = np.diag([-0.25, 0.1, 0.2, 0.3])
    assert _cone_diagnostics([large, small])[1] == pytest.approx(0.25)
    assert _cone_diagnostics([np.eye(4)])[1] == 0
    assert _cone_diagnostics([]) == (None, 0)
