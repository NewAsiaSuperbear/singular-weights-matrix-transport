"""Numerical correctness and artifact handling; the scientific sweep is not run."""
import json
from types import SimpleNamespace

import numpy as np
import pytest

import experiments


def valid_result():
    return {
        'status': 'optimal', 'primal_total': 1.0, 'runtime_seconds': 0.0,
        'diagnostics': {'ce_max_scaled_residual': 0.0, 'endpoint_max_scaled_residual': 0.0,
                        'ce_max_frobenius_residual': 0.0, 'endpoint_max_frobenius_residual': 0.0,
                        'cone_max_scaled_violation': 0.0, 'rho_min_eigenvalue': 1.0,
                        'max_rho_symmetry_error': 0.0, 'boundary_flux_max_frobenius': 0.0},
        'independent_quadratic_cost': {'total': 1.0, 'max_range_residual': 0.0},
    }


def test_known_diagonal_weighted_bures_value():
    H = np.diag([2.0, 3.0])
    A0, A1 = np.diag([1.0, 4.0]), np.diag([4.0, 9.0])
    expected = 2 * ((2 - 1)**2 / 4 + (3 - 2)**2 / 9)
    assert experiments.weighted_bures_value(H, A0, A1) == pytest.approx(expected, abs=1e-12)


def test_singular_endpoint_square_root():
    np.testing.assert_array_equal(experiments.sqrt_psd(np.diag([0., 4.])), np.diag([0., 2.]))


@pytest.mark.parametrize('H', [np.zeros((2, 2)), [[1., 1.], [0., 1.]], [[1., 0.], [0., -1.]]])
def test_non_spd_weight_rejected(H):
    with pytest.raises(ValueError, match='positive definite'):
        experiments.weighted_bures_value(H, np.eye(2), np.eye(2))


def test_profiles_have_equal_total_matrix_and_positive_density():
    a, b = experiments.profile_endpoints(4)
    np.testing.assert_allclose(a.mean(axis=0), np.eye(2), atol=1e-15)
    np.testing.assert_allclose(b.mean(axis=0), np.eye(2), atol=1e-15)
    np.testing.assert_allclose(np.trace(a, axis1=1, axis2=2), 2, atol=1e-15)
    np.testing.assert_allclose(np.trace(b, axis1=1, axis2=2), 2, atol=1e-15)
    assert np.linalg.eigvalsh(a).min() >= 0.75
    assert np.linalg.eigvalsh(b).min() >= 0.75
    assert np.linalg.norm(a[0] @ b[0] - b[0] @ a[0]) > 0


def test_optimal_inaccurate_and_range_errors_are_not_accepted():
    result = valid_result()
    assert experiments.solver_quality(result)['passed']
    result['status'] = 'optimal_inaccurate'
    result['independent_quadratic_cost']['max_range_residual'] = 2e-7
    quality = experiments.solver_quality(result)
    assert not quality['passed']
    assert 'optimal_status' in quality['failed_checks']
    assert 'range_residual' in quality['failed_checks']
    assert result['status'] == 'optimal_inaccurate'
    assert result['independent_quadratic_cost']['max_range_residual'] == 2e-7


def mocked_dependencies(monkeypatch, solve):
    monkeypatch.setattr(experiments, 'solve_transport', solve)
    monkeypatch.setattr(experiments, 'analytic_check', lambda eps, theta:
                        {'family': 'mock', 'epsilon': eps, 'theta': theta, 'passed': True})
    monkeypatch.setattr(experiments, 'rotating_formulas', lambda: SimpleNamespace(
        G0=np.eye(2), G1=np.diag([2., 1.]),
        optimal_path=lambda eps, theta, times:
        {'weight': np.diag([1., eps]), 'exact_action': 1.0}))


def test_mocked_design_reuses_solves_and_preserves_artifacts(tmp_path, monkeypatch):
    calls = []
    def fake_solve(a, b, H, **options):
        calls.append((H, options))
        return valid_result()
    mocked_dependencies(monkeypatch, fake_solve)
    data = experiments.run_experiment(tmp_path, meshes=(2,), nx=2, profile_nt=2,
                                      mlflow_run_id='unit-test-no-mlflow-run')
    assert len(calls) == 8
    assert len(data['solves']) == 9
    reused = [s for s in data['solves'] if s['reused_case_id'] is not None]
    assert len(reused) == 1
    assert reused[0]['reused_case_id'] == 'reaction_zero_eps1.0'
    assert data['metadata']['complete'] and data['metadata']['all_quality_passed']
    assert data['metadata']['source_unchanged']
    saved = json.loads((tmp_path / 'results.json').read_text())
    assert saved == data
    for source, digest in data['metadata']['source_sha256'].items():
        snapshot = tmp_path / 'source' / source
        assert snapshot.exists()
        assert experiments.hashlib.sha256(snapshot.read_bytes()).hexdigest() == digest
    assert (tmp_path / 'summary.csv').read_text().startswith('action,')


def test_mocked_exception_is_saved_and_later_cases_continue(tmp_path, monkeypatch):
    calls = []
    def fake_solve(*args, **kwargs):
        calls.append(True)
        if len(calls) == 1:
            raise RuntimeError('synthetic backend failure')
        return valid_result()
    mocked_dependencies(monkeypatch, fake_solve)
    data = experiments.run_experiment(tmp_path, meshes=(2,), nx=2, profile_nt=2)
    assert data['metadata']['complete'] and not data['metadata']['all_quality_passed']
    assert len(calls) == 8
    result = data['solves'][0]['result']
    assert result['status'] == 'exception'
    assert 'synthetic backend failure' in result['reason']
    assert result['traceback']
    assert json.loads((tmp_path / 'results.json').read_text())['solves'][0]['result'] == result


def test_previous_artifacts_are_never_overwritten(tmp_path):
    previous = tmp_path / 'results.json'
    previous.write_text('retained evidence')
    with pytest.raises(FileExistsError):
        experiments.run_experiment(tmp_path)
    assert previous.read_text() == 'retained evidence'


def test_mocked_analytic_failure_is_preserved(tmp_path, monkeypatch):
    mocked_dependencies(monkeypatch, lambda *args, **kwargs: valid_result())
    calls = []
    def failed_once(eps, theta):
        calls.append(True)
        if len(calls) == 1:
            raise ValueError('synthetic spectral error')
        return {'family': 'mock', 'epsilon': eps, 'theta': theta, 'passed': True}
    monkeypatch.setattr(experiments, 'analytic_check', failed_once)
    data = experiments.run_experiment(tmp_path, meshes=(2,), nx=2, profile_nt=2)
    assert len(data['analytic']) == 9
    assert data['analytic'][0]['status'] == 'exception'
    assert 'synthetic spectral error' in data['analytic'][0]['reason']
    assert not data['metadata']['all_quality_passed']
    assert data['metadata']['complete']


def test_high_precision_bures_reference_matches_ill_conditioned_actual_path():
    epsilon, theta = 0.001, np.sqrt(0.001)
    legacy = experiments.rotating_formulas()
    path = legacy.optimal_path(epsilon, theta, np.array([0.0, 0.5, 1.0]))
    reference = experiments.weighted_bures_value_decimal(path['weight'], legacy.G0, legacy.G1)
    actual_energy = legacy.quadratic_energy_density(path['mass'], path['reaction'], epsilon, theta)
    np.testing.assert_allclose(actual_energy, reference, atol=1e-10, rtol=1e-10)
    row = experiments.analytic_check(epsilon, theta)
    assert row['passed']
    assert row['decimal_reference_relative_error'] < 1e-10
    assert row['reference_precision_decimal_digits'] == 60
    assert row['independent_spectral_bures'] == experiments.weighted_bures_value(path['weight'], legacy.G0, legacy.G1)
    assert row['float64_reference_passed'] == (row['spectral_relative_error'] <= 1e-7)


def test_high_precision_bures_known_diagonal_and_singular_endpoints():
    H = np.diag([2.0, 3.0])
    reference = experiments.weighted_bures_value_decimal(H, np.diag([1.0, 4.0]), np.diag([4.0, 9.0]))
    assert reference == pytest.approx(2 * (1 / 4 + 1 / 9), abs=1e-14)
    assert experiments.weighted_bures_value_decimal(np.eye(2), np.diag([0.0, 1.0]),
                                                   np.diag([0.0, 4.0])) == pytest.approx(2.0, abs=1e-14)
