import MatrixTransport.Paper.FluxNoncompactness

/-! Arbitrary divergent transport scales in the existing skew-flux counterexample. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace LiZouTransport.FluxNoncompactness
open MatrixTransport MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.ClosedDomain

theorem example_action_eq_frobenius (t : ℝ) (ht : 0 < t) :
    action (t • (1 : Mat 2)) (1 : Mat 2) (examplePath t) =
      ENNReal.ofReal (frobeniusSq J / (2 * t)) := by
  rw [example_action t ht, frobeniusSq_J]
  congr 1
  field_simp

theorem example_fluxTV_eq_frobenius (t : ℝ) (ht : 0 ≤ t) :
    MatrixTransport.PartialWeights.rightFluxFrobeniusTV (examplePath t) (1 : Mat 2) =
      ENNReal.ofReal (Real.sqrt t * Real.sqrt (frobeniusSq J)) := by
  rw [frobeniusSq_J]
  exact example_fluxTV t ht

theorem example_action_tendsto_of_tendsto (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop) :
    Tendsto (fun j ↦ action (τ j • (1 : Mat 2)) (1 : Mat 2) (examplePath (τ j)))
      atTop (𝓝 0) := by
  have he : (fun j ↦ action (τ j • (1 : Mat 2)) (1 : Mat 2) (examplePath (τ j)))
      =ᶠ[atTop] (fun j ↦ ENNReal.ofReal (1 / τ j)) := by
    filter_upwards [hτ.eventually_gt_atTop (0 : ℝ)] with j hj
    exact example_action _ hj
  have ht : Tendsto (fun j ↦ ENNReal.ofReal (1 / τ j)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hτ)
  exact ht.congr' he.symm

theorem example_gap_tendsto (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop) :
    Tendsto (fun j ↦ action (τ j • (1 : Mat 2)) (1 : Mat 2) (examplePath (τ j)) -
      Limit.minimumValue (problem spatialLebesgue) (τ j • (1 : Mat 2)) (1 : Mat 2))
      atTop (𝓝 0) := by
  apply (example_action_tendsto_of_tendsto τ hτ).congr'
  filter_upwards [hτ.eventually_gt_atTop (0 : ℝ)] with j hj
  rw [example_minimum _ hj, tsub_zero]

theorem example_fluxTV_tendsto_of_tendsto (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop) :
    Tendsto (fun j ↦ (MatrixTransport.PartialWeights.rightFluxFrobeniusTV
      (examplePath (τ j)) (1 : Mat 2)).toReal) atTop atTop := by
  have he : (fun j ↦ (MatrixTransport.PartialWeights.rightFluxFrobeniusTV
      (examplePath (τ j)) (1 : Mat 2)).toReal) =ᶠ[atTop]
      (fun j ↦ Real.sqrt (τ j) * Real.sqrt 2) := by
    filter_upwards [hτ.eventually_gt_atTop (0 : ℝ)] with j hj
    rw [example_fluxTV _ hj.le, ENNReal.toReal_ofReal (by positivity)]
  have ht := (Real.tendsto_sqrt_atTop.comp hτ).atTop_mul_const
    (by positivity : (0 : ℝ) < Real.sqrt 2)
  exact ht.congr' he.symm

/-- Every increasing subsequence of every divergent scale fails original weak-star convergence. -/
theorem no_unscaled_weakStar_subsequence_of_tendsto (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop atTop) (u : ℕ → ℕ) (hu : StrictMono u)
    (ν : Limit.Path unitInterval 2 2) :
    ¬SignedWeakStarTendsto (fun j ↦ examplePath (τ (u j))) ν := by
  intro h
  let c : Coord 2 2 := Sum.inr (Sum.inl (0, 1))
  let f : C(Q unitInterval, ℝ) := ContinuousMap.const _ 1
  have hn := h c f
  have he : (fun j ↦ signedPair (examplePath (τ (u j)) c) f) =
      fun j ↦ Real.sqrt (τ (u j)) := by
    funext j
    exact example_flux_coordinate_pair _
  rw [he] at hn
  have ht := Real.tendsto_sqrt_atTop.comp (hτ.comp hu.tendsto_atTop)
  exact not_tendsto_nhds_of_tendsto_atTop ht _ hn

#print axioms example_action_eq_frobenius
#print axioms example_fluxTV_eq_frobenius
#print axioms example_action_tendsto_of_tendsto
#print axioms example_gap_tendsto
#print axioms example_fluxTV_tendsto_of_tendsto
#print axioms no_unscaled_weakStar_subsequence_of_tendsto

end LiZouTransport.FluxNoncompactness
