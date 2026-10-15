"""Correctness tests, not the scientific sweep (no MLflow run is created)."""

from decimal import Decimal, localcontext
import json
import math
from pathlib import Path

import numpy as np
import pytest

from numerical import (SEED, SINGULAR_TARGET_ACTION, exact_action, optimal_factor,
                       optimal_path, path_diagnostics, quadratic_energy_density)
from numerical.experiments import (METHOD, evaluate_case, family_definitions,
                                   run_experiment, source_hashes, write_artifacts)


def decimal_reference(epsilon, theta):
    """100-digit evaluation of the cancellation-prone formula, same float q.

    Standard-library Decimal avoids adding mpmath as a project dependency.
    This independently checks rationalization and arithmetic, not trig accuracy.
    """
    with localcontext() as context:
        context.prec = 100
        eps = Decimal.from_float(float(epsilon))
        q = Decimal.from_float(math.sin(float(theta)) ** 2)
        two, one = Decimal(2), Decimal(1)
        e2 = eps * eps
        z = one + q + two * two.sqrt() * e2 + (two - q) * e2 * e2
        return float(two * (Decimal(3) - q + (two + q - two * z.sqrt()) / e2))


@pytest.mark.parametrize("epsilon,theta", [
    (1.0, 0.7), (0.1, 0.4), (1e-6, 1e-6),
    (1e-10, 1e-5), (1e-12, 1e-3), (1e-12, 0.0),
])
def test_rationalized_cost_against_high_precision(epsilon, theta):
    assert exact_action(epsilon, theta) == pytest.approx(decimal_reference(epsilon, theta),
                                                        rel=2e-14, abs=2e-14)


@pytest.mark.parametrize("epsilon", [1.0, 0.01, 1e-10])
def test_no_rotation_has_exact_target_cost(epsilon):
    assert exact_action(epsilon, 0.0) == pytest.approx(SINGULAR_TARGET_ACTION, abs=2e-15)
    np.testing.assert_allclose(optimal_factor(epsilon, 0.0), np.diag([math.sqrt(2), 1]),
                               atol=5e-16, rtol=5e-16)


@pytest.mark.parametrize("epsilon,theta", [
    (0.5, 0.6), (0.01, 0.1), (1e-6, 0.02), (1e-6, 0.001),
    (1e-8, 0.01), (1e-8, 0.0002), (1e-8, 1e-6),
])
def test_actual_optimal_path_invariants_and_independent_energy(epsilon, theta):
    times = np.linspace(0, 1, 17)
    path = optimal_path(epsilon, theta, times)
    a, k = path["factor"], path["covariance"]
    np.testing.assert_allclose(a @ a.T, np.diag([2., 1.]), atol=2e-14, rtol=2e-14)
    np.testing.assert_allclose(a @ k, (a @ k).T, atol=2e-14, rtol=2e-14)
    assert np.linalg.eigvalsh((a @ k + k @ a.T) / 2).min() > 0
    np.testing.assert_allclose(path["mass"][0], np.eye(2), atol=2e-14)
    np.testing.assert_allclose(path["mass"][-1], np.diag([2., 1.]), atol=2e-14)
    assert np.linalg.eigvalsh(path["mass"]).min() > 0
    np.testing.assert_allclose(path["mass"], path["mass"].transpose(0, 2, 1), atol=2e-14)
    assert not np.any(path["flux"])
    np.testing.assert_allclose(path["mass_derivative"],
                               (path["reaction"] + path["reaction"].transpose(0, 2, 1)) / 2,
                               atol=2e-14)
    # Independent finite differences of the evaluated mass, rather than just
    # comparing two expressions written using the same derivative formula.
    h = 1e-5
    plus = optimal_path(epsilon, theta, [0.37 + h])["mass"][0]
    minus = optimal_path(epsilon, theta, [0.37 - h])["mass"][0]
    mid = optimal_path(epsilon, theta, [0.37])["reaction"][0]
    np.testing.assert_allclose((plus - minus) / (2 * h), (mid + mid.T) / 2, atol=3e-11)
    energy = quadratic_energy_density(path["mass"], path["reaction"], epsilon, theta)
    np.testing.assert_allclose(energy, path["exact_action"], rtol=2e-9, atol=2e-10)
    diagnostic = path_diagnostics(path)
    assert diagnostic["energy_density_constancy_relative_error"] < 2e-9
    assert diagnostic["independent_action_relative_error"] < 2e-9


def test_full_nonsymmetric_reaction_is_retained():
    r = optimal_path(0.02, 0.2, [0.0, 0.5, 1.0])["reaction"]
    assert np.max(np.abs(r[:, 0, 1] - r[:, 1, 0])) > 1e-3


def test_congruence_cost_identity_in_a_known_spd_case():
    path = optimal_path(0.3, 0.2, [0.27])
    h, g, r = path["weight"], path["mass"][0], path["reaction"][0]
    hi = np.linalg.inv(h)
    m, s = hi @ g @ hi, hi @ r @ hi
    transformed = np.sum(s * np.linalg.solve(m, s)) / 2
    original = quadratic_energy_density(g, r, 0.3, 0.2)
    assert transformed == pytest.approx(float(original), rel=2e-13)


def test_formula_is_even_in_angle_and_seeded_invariant_checks():
    rng = np.random.default_rng(SEED)
    for epsilon, theta in zip(rng.uniform(0.02, 0.9, 5), rng.uniform(-0.6, 0.6, 5)):
        assert exact_action(epsilon, theta) == exact_action(epsilon, -theta)
        a = optimal_factor(epsilon, theta)
        np.testing.assert_allclose(a @ a.T, np.diag([2., 1.]), atol=1e-13)


@pytest.mark.parametrize("amplitude", [0.5, 1.0, 2.0])
def test_proved_critical_limit_has_the_original_action_normalization(amplitude):
    epsilon = 1e-8
    theta = amplitude * math.sqrt(epsilon)
    expected = SINGULAR_TARGET_ACTION + amplitude ** 4 / 2
    assert exact_action(epsilon, theta) == pytest.approx(expected, rel=1e-7, abs=1e-7)


def test_proved_subcritical_and_supercritical_known_limits():
    epsilon = 1e-8
    assert exact_action(epsilon, epsilon ** 0.75) == pytest.approx(SINGULAR_TARGET_ACTION,
                                                                abs=1e-7)
    # For p=.25 the exact leading growth is 1/(2 epsilon), rather than the
    # weaker coercivity lower bound 1/(2 sqrt(epsilon)).
    assert exact_action(epsilon, epsilon ** 0.25) / (1 / (2 * epsilon)) == pytest.approx(1,
                                                                                   rel=3e-4)


@pytest.mark.parametrize("epsilon,theta", [(0, 0), (-1, 0), (float("nan"), 0),
                                         (float("inf"), 0), (0.1, float("nan"))])
def test_invalid_parameters_are_rejected(epsilon, theta):
    with pytest.raises(ValueError):
        exact_action(epsilon, theta)
    with pytest.raises(ValueError):
        optimal_path(epsilon, theta)


@pytest.mark.parametrize("times", [[], [[0, 1]], [0.5, 0.4], [-0.1, 1], [0, 1.1], [float("nan")]])
def test_invalid_time_samples_are_rejected(times):
    with pytest.raises(ValueError):
        optimal_path(0.1, 0.2, times)


def test_independent_cost_rejects_non_spd_mass():
    with pytest.raises(ValueError):
        quadratic_energy_density(np.diag([1., 0.]), np.eye(2), 0.2, 0.1)


def test_tracking_context_required_before_scientific_run(tmp_path):
    with pytest.raises(ValueError, match="tracking_run_id"):
        run_experiment(tmp_path, tracking_run_id="", experiment_name="")
    assert list(tmp_path.iterdir()) == []


def test_minimal_artifact_export_correctness_only(tmp_path):
    # Two known-case fixtures exercise CSV/JSON/plot export; this does not run
    # the scientific log-grid, create a fake tracking run, or report experiments.
    rows, paths = [], []
    for family in (family_definitions()[1], family_definitions()[4]):
        row, path = evaluate_case(0.04, family, time_samples=5)
        rows.append(row)
        paths.append({"family": family["family"], **path})
    metadata = {"purpose": "pytest correctness smoke test", "method": METHOD, "seed": SEED}
    artifacts = write_artifacts(rows, paths, metadata, tmp_path)
    payload = json.loads((tmp_path / "results.json").read_text())
    assert len(payload["summary"]) == 2
    assert len(payload["paths"][0]["mass"]) == 5
    assert payload["metadata"]["method"] == METHOD
    assert "no SDP" in METHOD
    hashes = json.loads((tmp_path / "source_hashes.json").read_text())
    assert hashes == source_hashes()
    assert set(hashes) >= {"numerical/rotating_family.py", "numerical/experiments.py", "tests/test_numerical.py"}
    assert (tmp_path / "action_thresholds.png").stat().st_size > 1000
    assert (tmp_path / "optimal_paths.png").stat().st_size > 1000
    assert all(Path(path).exists() for path in artifacts.values())
