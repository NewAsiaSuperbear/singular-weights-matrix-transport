import numpy as np
import pytest

from solver import solve_transport


def endpoints():
    A = np.array([[1.3, 0.2], [0.2, 0.4]])
    B = np.array([[0.5, -0.1], [-0.1, 1.1]])
    return np.array([A, B]), np.array([B, A])


def check_result(result):
    assert result['status'] == 'optimal'
    assert result['diagnostics']['ce_max_frobenius_residual'] < 1e-7
    assert result['diagnostics']['cone_max_scaled_violation'] < 1e-7
    assert result['independent_quadratic_cost']['total'] == pytest.approx(
        result['primal_total'], abs=1e-7, rel=1e-6)


def test_balanced_uniform_transport_scaling():
    a, b = endpoints()
    base = solve_transport(a, b, nt=4, tolerance=1e-11)
    scaled = solve_transport(a, b, L=2*np.eye(2), nt=4, tolerance=1e-11)
    check_result(base)
    check_result(scaled)
    assert scaled['primal_total'] == pytest.approx(base['primal_total']/4, rel=1e-6)
    np.testing.assert_allclose(scaled['flux'], base['flux'], atol=2e-6)


def test_identity_transport_matches_original_algorithm():
    a, b = endpoints()
    base = solve_transport(a, b, np.eye(2), nt=3, tolerance=1e-10)
    identity = solve_transport(a, b, np.eye(2), L=np.eye(2), nt=3, tolerance=1e-10)
    check_result(base)
    check_result(identity)
    assert identity['primal_total'] == pytest.approx(base['primal_total'], abs=1e-10)


@pytest.mark.parametrize('L', [np.zeros((2,2)), np.ones((3,3)), [[1,1],[0,1]], [[1,0],[0,-1]]])
def test_invalid_transport_weights_rejected_before_solver(L):
    a, b = endpoints()
    with pytest.raises(ValueError, match='L'):
        solve_transport(a, b, L=L, nt=2)
