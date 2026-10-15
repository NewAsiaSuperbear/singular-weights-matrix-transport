import MatrixTransport.EntrywiseBures.HubRecovery
import MatrixTransport.Paper.HubOptimization
import MatrixTransport.PartialWeights.WeightComparison

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace LiZouTransport.HubLimit
open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain
open MatrixTransport.ReactionZero.Limit MatrixTransport.EntrywiseBures
open LiZouTransport.Hub LiZouTransport.HubScalar LiZouTransport.Reaction

variable {d n : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

def endpointEnergy (R : PSDSqrt n) (P : Problem Ω n (d * n)) (H : RMat n) : ℝ :=
  buresValue R H (totalMatrix P.initial) (totalMatrix P.terminal)

def hubConstant (G : HubGeometry d Ω) (P : Problem Ω n (d * n)) : ℝ :=
  (Real.sqrt (hubMoment P.initial G.hub) +
    Real.sqrt (hubMoment P.terminal G.hub)) / Real.sqrt 2

theorem sqrt_transport_cost {M t : ℝ} (hM : 0 ≤ M) (ht : 0 < t) :
    Real.sqrt (M / (2 * t ^ 2)) = Real.sqrt M / (Real.sqrt 2 * t) := by
  rw [Real.sqrt_div, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_sq_eq_abs, abs_of_pos ht]
  exact hM

theorem sqrt_segment_sum (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) (H : RMat n) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (hubMoment P.initial G.hub / (2 * t ^ 2)) +
      Real.sqrt (endpointEnergy R P H) +
      Real.sqrt (hubMoment P.terminal G.hub / (2 * t ^ 2)) =
        Real.sqrt (endpointEnergy R P H) + hubConstant G P / t := by
  rw [sqrt_transport_cost (hubMoment_nonneg P.initial_positive G.hub) ht,
    sqrt_transport_cost (hubMoment_nonneg P.terminal_positive G.hub) ht]
  unfold hubConstant
  ring

/-- The optimized original three-piece hub recovery bound. -/
theorem minimumValue_le_hub_bound (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) (hD : P.operator = entrywiseDivergence d n)
    {H : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det) {t : ℝ} (ht : 0 < t) :
    minimumValue P (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H ≤
      ENNReal.ofReal ((Real.sqrt (endpointEnergy R P H) + hubConstant G P / t) ^ 2) := by
  apply constrainedInfimum_le_square_of_approximants
  intro η hη
  have h0 : 0 ≤ hubMoment P.initial G.hub / (2 * t ^ 2) :=
    div_nonneg (hubMoment_nonneg P.initial_positive G.hub) (by positivity)
  have h1 : 0 ≤ endpointEnergy R P H :=
    buresValue_nonneg R hH hHu (totalMatrix_posSemidef P.initial_positive)
      (totalMatrix_posSemidef P.terminal_positive)
  have h2 : 0 ≤ hubMoment P.terminal G.hub / (2 * t ^ 2) :=
    div_nonneg (hubMoment_nonneg P.terminal_positive G.hub) (by positivity)
  obtain ⟨r0, r1, r2, hr0, hr1, hr2, hrs, hcost⟩ := exists_three_durations h0 h1 h2 hη
  obtain ⟨μ, hμ, hE⟩ := exists_hub_competitor R G P hD hH hHu hr0 hr1 hr2 hrs ht
  refine ⟨μ, hμ, hE.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [sqrt_segment_sum R G P H ht] at hcost
  simpa only [endpointEnergy, div_div] using hcost

/-- The time-only Bures certificate gives the matching lower bound. -/
theorem endpointEnergy_le_minimumValue (R : PSDSqrt n)
    (P : Problem Ω n (d * n)) (hD : P.operator = entrywiseDivergence d n)
    {H : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    (L : Matrix (Fin (d * n)) (Fin (d * n)) ℝ) :
    ENNReal.ofReal (endpointEnergy R P H) ≤ minimumValue P L H := by
  exact buresValue_le_minimumValue R P (by intro A _; rw [hD]; rfl) hH hHu L

/-- The finite-baseline free-transport target equals the endpoint Bures energy. -/
theorem freeTransportValue_eq_endpointEnergy (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) (hD : P.operator = entrywiseDivergence d n)
    {H : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det) :
    MatrixTransport.TransportInfinity.freeTransportValue P
      (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ) H =
        ENNReal.ofReal (endpointEnergy R P H) := by
  apply freeTransportValue_eq_of_ray_sandwich
      P (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ) H
      (B := hubConstant G P)
  · exact buresValue_nonneg R hH hHu (totalMatrix_posSemidef P.initial_positive)
      (totalMatrix_posSemidef P.terminal_positive)
  · intro t _
    exact endpointEnergy_le_minimumValue R P hD hH hHu _
  · intro t ht
    exact minimumValue_le_hub_bound R G P hD hH hHu ht


/-- Transport Gram domination decreases the original action, with reaction weight fixed. -/
theorem action_le_of_transport_gram (L : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)
    (H : RMat n) {m : ℝ}
    (hGram : (gram L - m ^ 2 • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)).PosSemidef)
    (μ : Path Ω n (d * n)) :
    action L H μ ≤ action (m • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H μ := by
  have hL : (gram L - (1 : ℝ) • gram
      (m • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ))).PosSemidef := by
    rw [one_smul, gram_smul]
    simpa only [gram, Matrix.transpose_one, Matrix.one_mul] using hGram
  have hH : (gram H - (1 : ℝ) • gram H).PosSemidef := by
    simpa only [one_smul, sub_self] using (Matrix.PosSemidef.zero :
      (0 : RMat n).PosSemidef)
  simpa using MatrixTransport.PartialWeights.action_le_inv_mul_of_relative_grams
    L (m • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H H 1 (by norm_num) hL hH μ

/-- The hub bound for a transport weight with a positive lower Gram bound. -/
theorem minimumValue_le_hub_bound_of_gram (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) (hD : P.operator = entrywiseDivergence d n)
    {H : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    (L : Matrix (Fin (d * n)) (Fin (d * n)) ℝ) {m : ℝ} (hm : 0 < m)
    (hGram : (gram L - m ^ 2 • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)).PosSemidef) :
    minimumValue P L H ≤
      ENNReal.ofReal ((Real.sqrt (endpointEnergy R P H) + hubConstant G P / m) ^ 2) := by
  have hmin : minimumValue P L H ≤
      minimumValue P (m • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H := by
    unfold minimumValue constrainedInfimum
    exact iInf_mono fun μ ↦ iInf_mono fun _ ↦ action_le_of_transport_gram L H hGram μ
  exact hmin.trans (minimumValue_le_hub_bound R G P hD hH hHu hm)


/-- The manuscript's positive-definite weight corollary, with `L² ≽ m² I`. -/
theorem hub_value_bounds_posDef (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) (hD : P.operator = entrywiseDivergence d n)
    {L : Matrix (Fin (d * n)) (Fin (d * n)) ℝ} {H : RMat n}
    (hL : L.PosDef) (hH : H.PosDef) {m : ℝ} (hm : 0 < m)
    (hSquare : (L * L - m ^ 2 • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)).PosSemidef) :
    ENNReal.ofReal (endpointEnergy R P H) ≤ minimumValue P L H ∧
    minimumValue P L H ≤
      ENNReal.ofReal ((Real.sqrt (endpointEnergy R P H) + hubConstant G P / m) ^ 2) := by
  have hHt : Hᵀ = H := transpose_eq_of_posSemidef hH.posSemidef
  have hHu : IsUnit H.det := isUnit_iff_ne_zero.mpr hH.det_pos.ne'
  have hLt : Lᵀ = L := transpose_eq_of_posSemidef hL.posSemidef
  have hGram : (gram L - m ^ 2 • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)).PosSemidef := by
    simpa only [gram, hLt] using hSquare
  exact ⟨endpointEnergy_le_minimumValue R P hD hHt hHu L,
    minimumValue_le_hub_bound_of_gram R G P hD hHt hHu L hm hGram⟩

#print axioms hub_value_bounds_posDef
#print axioms action_le_of_transport_gram
#print axioms minimumValue_le_hub_bound_of_gram
#print axioms minimumValue_le_hub_bound
#print axioms endpointEnergy_le_minimumValue
#print axioms freeTransportValue_eq_endpointEnergy
end LiZouTransport.HubLimit
