import MatrixTransport.Paper.KBVariableAmplitude
import MatrixTransport.Paper.NativeSeparationSqrt

/-! # The manuscript's literal proof route for smooth operator separation

The common shifted family uses the sharp cutoff bound, the variable-amplitude
KB certificate, and the nonlinear square-root reaction competitor.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise ContDiff

namespace LiZouTransport.NativeSeparation
open MatrixTransport MatrixTransport.ReactionZero.ClosedDomain

theorem exists_native_smooth_positive_separation_paperRoute :
    ∃ N : ℕ, ∃ c : ℝ, ∃ hb : ∀ j x,
      |(1 / 4 : ℝ) * endpointWave (j + N) x| ≤ (1 / 2 : ℝ),
      0 < c ∧
      (∀ j, ContDiff ℝ ∞ (separatedEndpoint N j)) ∧
      (∀ j x,
        LoewnerLE ((1 / 2 : ℝ) • (1 : Mat2)) (separatedEndpoint N j x) ∧
        LoewnerLE (separatedEndpoint N j x) ((3 / 2 : ℝ) • (1 : Mat2))) ∧
      weakStarConverges (separatedEndpoint N) baseEndpoint ∧
      Tendsto (fun j ↦ smoothValue fullOperator
        (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
        (continuous_const.mul (endpointWave_continuous (j + N))) (hb j)) atTop (𝓝 0) ∧
      (∀ j, ENNReal.ofReal c ≤ smoothValue LiZouTransport.Examples.kbOp
        (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
        (continuous_const.mul (endpointWave_continuous (j + N))) (hb j) ∧
        smoothValue LiZouTransport.Examples.kbOp
        (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
        (continuous_const.mul (endpointWave_continuous (j + N))) (hb j) ≤
          ENNReal.ofReal (Real.pi / 4)) ∧
      ¬ Tendsto (fun j ↦ smoothValue LiZouTransport.Examples.kbOp
        (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
        (continuous_const.mul (endpointWave_continuous (j + N))) (hb j)) atTop (𝓝 0) := by
  obtain ⟨c,hc,hcLower⟩ := exists_positive_KB_lower_variable
  obtain ⟨N2,hN2⟩ := Filter.eventually_atTop.1 hcLower
  obtain ⟨N0,hN0⟩ := exists_uniform_endpointWave_bound
  obtain ⟨N1,hN1⟩ := exists_uniform_waveEndpoint_bounds
  let N := max N0 (max N1 N2)
  have hN0' : N0 ≤ N := le_max_left _ _
  have hN1' : N1 ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN2' : N2 ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hb : ∀ j x, |(1 / 4 : ℝ) * endpointWave (j + N) x| ≤ (1 / 2 : ℝ) := by
    intro j x
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have h := hN0 (j + N) (by omega) x
    linarith
  have hlo : ∀ j, ENNReal.ofReal c ≤ smoothValue LiZouTransport.Examples.kbOp
      (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
      (continuous_const.mul (endpointWave_continuous (j + N))) (hb j) := by
    intro j
    exact (hN2 (j + N) (by omega)).trans
      (kb_concrete_lower_native _ (continuous_const.mul (endpointWave_continuous (j + N))) (hb j))
  refine ⟨N,c,hb,hc,?_,?_,?_,?_,?_,?_⟩
  · intro j; exact waveEndpoint_contDiff (j + N)
  · intro j x; exact hN1 (j + N) (by omega) x
  · intro Φ; exact (waveEndpoint_weakStarConverges Φ).comp (tendsto_add_atTop_nat N)
  · have hL2 : Tendsto (fun j : ℕ ↦ ENNReal.ofReal
        ((∫ x : Spatial, chi x ^ 2) / (16 * waveNumber (j + N) ^ 2))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero,Function.comp_def] using!
        (ENNReal.continuous_ofReal.tendsto 0).comp (tendsto_chi_L2_bound N)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hL2 (Filter.Eventually.of_forall fun _ ↦ bot_le)
    exact Filter.Eventually.of_forall fun j ↦
      (full_native_upper_L2 (j + N) (hb j)).1.trans
        (ENNReal.ofReal_le_ofReal (full_native_upper_L2 (j + N) (hb j)).2)
  · intro j
    exact ⟨hlo j, kb_native_upper_sqrt _
      (continuous_const.mul (endpointWave_continuous (j + N))) (hb j)⟩
  · intro ht
    have hz : ENNReal.ofReal c ≤ 0 := ge_of_tendsto' ht hlo
    exact absurd hz (not_le.mpr (ENNReal.ofReal_pos.mpr hc))

/-- No finite uniform squared-value comparison holds along the genuine native sequence. -/
theorem no_native_eventual_uniform_comparison_paperRoute :
    ∃ N : ℕ, ∃ hb : ∀ j x,
      |(1 / 4 : ℝ) * endpointWave (j + N) x| ≤ (1 / 2 : ℝ),
      ∀ C : ℝ, ¬ (∀ᶠ j : ℕ in atTop,
        smoothValue LiZouTransport.Examples.kbOp
          (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
          (continuous_const.mul (endpointWave_continuous (j + N))) (hb j) ≤
        ENNReal.ofReal C * smoothValue fullOperator
          (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
          (continuous_const.mul (endpointWave_continuous (j + N))) (hb j)) := by
  obtain ⟨N,c,hb,hc,_,_,_,hfull,hkb,_⟩ := exists_native_smooth_positive_separation_paperRoute
  refine ⟨N,hb,?_⟩
  intro C hcompare
  have hmul : Tendsto (fun j ↦ ENNReal.ofReal C * smoothValue fullOperator
      (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
      (continuous_const.mul (endpointWave_continuous (j + N))) (hb j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C)
      hfull (Or.inr ENNReal.ofReal_ne_top)
  have hzero : ENNReal.ofReal c ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hmul (by
    filter_upwards [hcompare] with j hj
    exact (hkb j).1.trans hj)
  exact absurd hzero (not_le.mpr (ENNReal.ofReal_pos.mpr hc))

#print axioms exists_native_smooth_positive_separation_paperRoute
#print axioms no_native_eventual_uniform_comparison_paperRoute
end LiZouTransport.NativeSeparation
