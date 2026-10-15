import MatrixTransport.Paper.HubLimit

/-! Exact optimization of the three positive hub durations, including vanishing costs. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace LiZouTransport.HubScalar

/-- The strictly positive three-duration simplex. -/
structure PositiveSimplex3 where
  value : Fin 3 → ℝ
  positive : ∀ i, 0 < value i
  sum_eq_one : ∑ i, value i = 1

def rootSum (c : Fin 3 → ℝ) : ℝ := ∑ i, Real.sqrt (c i)

def durationBound (c : Fin 3 → ℝ) (r : PositiveSimplex3) : ℝ :=
  ∑ i, c i / r.value i

theorem rootSum_nonneg (c : Fin 3 → ℝ) : 0 ≤ rootSum c :=
  Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _

/-- Cauchy--Schwarz lower bound for every strictly positive allocation. -/
theorem rootSum_sq_le_durationBound {c : Fin 3 → ℝ} (hc : ∀ i, 0 ≤ c i)
    (r : PositiveSimplex3) : rootSum c ^ 2 ≤ durationBound c r := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ
    (fun i ↦ Real.sqrt (c i)) (fun i _ ↦ r.positive i)
  simpa only [rootSum, durationBound, r.sum_eq_one, div_one, Real.sq_sqrt (hc _)] using h

theorem exists_simplex_approximant {c : Fin 3 → ℝ} (hc : ∀ i, 0 ≤ c i)
    {η : ℝ} (hη : 0 < η) :
    ∃ r : PositiveSimplex3, durationBound c r ≤ (rootSum c + η) ^ 2 := by
  obtain ⟨r0, r1, r2, hr0, hr1, hr2, hrs, hcost⟩ :=
    exists_three_durations (hc 0) (hc 1) (hc 2) hη
  let r : PositiveSimplex3 := ⟨![r0, r1, r2], by
    intro i
    fin_cases i <;> simp_all, by simpa [Fin.sum_univ_three] using hrs⟩
  refine ⟨r, ?_⟩
  simpa [durationBound, rootSum, r, Fin.sum_univ_three] using hcost

/-- The exact real infimum of the three-piece cost. -/
theorem durationBound_isGLB {c : Fin 3 → ℝ} (hc : ∀ i, 0 ≤ c i) :
    IsGLB (Set.range (durationBound c)) (rootSum c ^ 2) := by
  constructor
  · rintro _ ⟨r, rfl⟩
    exact rootSum_sq_le_durationBound hc r
  · intro b hb
    let δ : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
    have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun j ↦ (rootSum c + δ j) ^ 2) atTop (𝓝 (rootSum c ^ 2)) := by
      simpa only [add_zero] using (tendsto_const_nhds.add hδ).pow 2
    apply ge_of_tendsto' ht
    intro j
    obtain ⟨r, hr⟩ := exists_simplex_approximant hc (η := δ j) (by dsimp [δ]; positivity)
    exact (hb (Set.mem_range_self r)).trans hr

theorem durationBound_sInf_eq {c : Fin 3 → ℝ} (hc : ∀ i, 0 ≤ c i) :
    sInf (Set.range (durationBound c)) = rootSum c ^ 2 :=
  (durationBound_isGLB hc).csInf_eq (by
    obtain ⟨r, _⟩ := exists_simplex_approximant hc (η := 1) (by norm_num)
    exact ⟨durationBound c r, Set.mem_range_self r⟩)

/-- Exact extended-real infimum, without assuming positive segment costs. -/
theorem iInf_durationBound_eq {c : Fin 3 → ℝ} (hc : ∀ i, 0 ≤ c i) :
    (⨅ r : PositiveSimplex3, ENNReal.ofReal (durationBound c r)) =
      ENNReal.ofReal (rootSum c ^ 2) := by
  apply le_antisymm
  · apply le_of_forall_positive_square
    intro η hη
    obtain ⟨r, hr⟩ := exists_simplex_approximant hc hη
    exact (iInf_le _ r).trans (ENNReal.ofReal_le_ofReal hr)
  · exact le_iInf fun r ↦ ENNReal.ofReal_le_ofReal (rootSum_sq_le_durationBound hc r)

theorem rootSum_pos {c : Fin 3 → ℝ} (hc : ∀ i, 0 < c i) : 0 < rootSum c := by
  exact Finset.sum_pos (fun i _ ↦ Real.sqrt_pos.2 (hc i)) (by simp)

/-- With three positive costs, the square-root proportional allocation attains the infimum. -/
theorem proportional_durations_attain {c : Fin 3 → ℝ} (hc : ∀ i, 0 < c i) :
    ∃ r : PositiveSimplex3, (∀ i, r.value i = Real.sqrt (c i) / rootSum c) ∧
      durationBound c r = rootSum c ^ 2 := by
  have hS := rootSum_pos hc
  let r : PositiveSimplex3 := ⟨fun i ↦ Real.sqrt (c i) / rootSum c,
    fun i ↦ div_pos (Real.sqrt_pos.2 (hc i)) hS, by
      rw [← Finset.sum_div]
      exact div_self hS.ne'⟩
  refine ⟨r, fun _ ↦ rfl, ?_⟩
  have he (i : Fin 3) : c i / r.value i = Real.sqrt (c i) * rootSum c := by
    change c i / (Real.sqrt (c i) / rootSum c) = _
    rw [div_div_eq_mul_div, div_eq_iff (Real.sqrt_pos.2 (hc i)).ne']
    have hs := Real.sq_sqrt (hc i).le
    nlinarith
  simp_rw [durationBound, he]
  rw [← Finset.sum_mul]
  change rootSum c * rootSum c = _
  ring

/-- The positive-tolerance allocation converges to the proportional one when its sum is nonzero. -/
theorem duration_tendsto_proportional {c S : ℝ} (hS : 0 < S) :
    Tendsto (duration c S) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt c / S)) := by
  have hi : Tendsto (fun η : ℝ ↦ η) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hn := (tendsto_const_nhds (x := Real.sqrt c)).add (hi.div_const 3)
  have hd := (tendsto_const_nhds (x := S)).add hi
  change Tendsto (fun η ↦ (Real.sqrt c + η / 3) / (S + η)) _ _
  have h := hn.div hd (by simpa using hS.ne')
  simp only [zero_div, add_zero] at h
  convert h using 1
  ext η
  rfl

theorem duration_zero_tendsto_zero {S : ℝ} (hS : 0 < S) :
    Tendsto (duration 0 S) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa using duration_tendsto_proportional (c := 0) hS

theorem duration_allZero {η : ℝ} (hη : 0 < η) : duration 0 0 η = 1 / 3 := by
  simp only [duration, Real.sqrt_zero, zero_add]
  field_simp

theorem durationBound_allZero (r : PositiveSimplex3) : durationBound (fun _ ↦ 0) r = 0 := by
  simp [durationBound]

/-- The explicit positive allocation used when a segment has zero cost. -/
def allocatedSimplex (c : Fin 3 → ℝ) (η : ℝ) (hη : 0 < η) : PositiveSimplex3 where
  value i := duration (c i) (rootSum c) η
  positive _ := duration_pos (rootSum_nonneg c) hη
  sum_eq_one := by
    simp only [Fin.sum_univ_three, duration]
    have hden : rootSum c + η ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (rootSum_nonneg c) hη)
    field_simp
    simp only [rootSum, Fin.sum_univ_three]
    ring

theorem three_duration_bound_tendsto {c : Fin 3 → ℝ} (hc : ∀ i, 0 ≤ c i) :
    Tendsto (fun η : ℝ ↦ ∑ i, c i / duration (c i) (rootSum c) η)
      (𝓝[>] (0 : ℝ)) (𝓝 (rootSum c ^ 2)) := by
  have hi : Tendsto (fun η : ℝ ↦ η) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun η : ℝ ↦ (rootSum c + η) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (rootSum c ^ 2)) := by
    simpa only [add_zero] using ((tendsto_const_nhds (x := rootSum c)).add hi).pow 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact rootSum_sq_le_durationBound hc (allocatedSimplex c η hη)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    calc
      (∑ i, c i / duration (c i) (rootSum c) η) ≤
          ∑ i, Real.sqrt (c i) * (rootSum c + η) :=
        Finset.sum_le_sum fun i _ ↦ duration_cost_le (hc i) (rootSum_nonneg c) hη
      _ = rootSum c * (rootSum c + η) := by rw [← Finset.sum_mul]; rfl
      _ ≤ (rootSum c + η) ^ 2 := by
        have hS := rootSum_nonneg c
        have hη' : 0 < η := hη
        nlinarith

end LiZouTransport.HubScalar

namespace LiZouTransport.HubLimit
open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain
open MatrixTransport.ReactionZero.Limit MatrixTransport.EntrywiseBures
open LiZouTransport.Hub LiZouTransport.HubScalar LiZouTransport.Reaction

variable {d n : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

def segmentCosts (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) (H : RMat n) (t : ℝ) : Fin 3 → ℝ :=
  ![hubMoment P.initial G.hub / (2 * t ^ 2), endpointEnergy R P H,
    hubMoment P.terminal G.hub / (2 * t ^ 2)]

theorem segmentCosts_nonneg (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) {H : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    (t : ℝ) : ∀ i, 0 ≤ segmentCosts R G P H t i := by
  intro i
  fin_cases i
  · exact div_nonneg (hubMoment_nonneg P.initial_positive G.hub) (by positivity)
  · exact buresValue_nonneg R hH hHu (totalMatrix_posSemidef P.initial_positive)
      (totalMatrix_posSemidef P.terminal_positive)
  · exact div_nonneg (hubMoment_nonneg P.terminal_positive G.hub) (by positivity)

/-- Every positive duration allocation gives the original signed-Radon hub upper bound. -/
theorem minimumValue_le_iInf_hub_bound (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) (hD : P.operator = entrywiseDivergence d n)
    {H : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det) {t : ℝ} (ht : 0 < t) :
    minimumValue P (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H ≤
      ⨅ r : PositiveSimplex3, ENNReal.ofReal (durationBound (segmentCosts R G P H t) r) := by
  apply le_iInf
  intro r
  have hrs : r.value 0 + r.value 1 + r.value 2 = 1 := by
    simpa [Fin.sum_univ_three] using r.sum_eq_one
  obtain ⟨μ, hμ, hE⟩ := exists_hub_competitor R G P hD hH hHu
    (r.positive 0) (r.positive 1) (r.positive 2) hrs ht
  have hm : minimumValue P (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H ≤
      action (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H μ := by
    unfold minimumValue constrainedInfimum
    exact iInf_le_of_le μ (iInf_le_of_le hμ le_rfl)
  refine hm.trans ?_
  simpa [durationBound, segmentCosts, Fin.sum_univ_three, endpointEnergy, div_div] using hE

/-- The exact extended-real infimum appearing in the hub construction. -/
theorem iInf_hub_bound_eq (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) {H : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    {t : ℝ} (ht : 0 < t) :
    (⨅ r : PositiveSimplex3, ENNReal.ofReal (durationBound (segmentCosts R G P H t) r)) =
      ENNReal.ofReal ((Real.sqrt (endpointEnergy R P H) + hubConstant G P / t) ^ 2) := by
  rw [iInf_durationBound_eq (segmentCosts_nonneg R G P hH hHu t)]
  congr 2
  simpa [rootSum, segmentCosts, Fin.sum_univ_three] using sqrt_segment_sum R G P H ht

/-- The hub bounds squeeze the full real transport parameter, not only natural-number rays. -/
theorem hub_value_tendsto_real_atTop (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) (hD : P.operator = entrywiseDivergence d n)
    {H : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det) :
    Tendsto (fun t : ℝ ↦ minimumValue P
      (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H) atTop
      (𝓝 (ENNReal.ofReal (endpointEnergy R P H))) := by
  have hE : 0 ≤ endpointEnergy R P H :=
    buresValue_nonneg R hH hHu (totalMatrix_posSemidef P.initial_positive)
      (totalMatrix_posSemidef P.terminal_positive)
  have hB : Tendsto (fun t : ℝ ↦ hubConstant G P / t) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_id
  have hu : Tendsto (fun t : ℝ ↦ ENNReal.ofReal
      ((Real.sqrt (endpointEnergy R P H) + hubConstant G P / t) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (endpointEnergy R P H))) := by
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero, Real.sq_sqrt hE] using
      ((tendsto_const_nhds (x := Real.sqrt (endpointEnergy R P H))).add hB).pow 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Filter.Eventually.of_forall fun t ↦ endpointEnergy_le_minimumValue R P hD hH hHu _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact minimumValue_le_hub_bound R G P hD hH hHu ht

end LiZouTransport.HubLimit

#print axioms LiZouTransport.HubScalar.rootSum_sq_le_durationBound
#print axioms LiZouTransport.HubScalar.durationBound_isGLB
#print axioms LiZouTransport.HubScalar.durationBound_sInf_eq
#print axioms LiZouTransport.HubScalar.iInf_durationBound_eq
#print axioms LiZouTransport.HubScalar.proportional_durations_attain
#print axioms LiZouTransport.HubScalar.duration_tendsto_proportional
#print axioms LiZouTransport.HubScalar.duration_zero_tendsto_zero
#print axioms LiZouTransport.HubScalar.duration_allZero
#print axioms LiZouTransport.HubScalar.durationBound_allZero
#print axioms LiZouTransport.HubScalar.three_duration_bound_tendsto
#print axioms LiZouTransport.HubLimit.minimumValue_le_iInf_hub_bound
#print axioms LiZouTransport.HubLimit.iInf_hub_bound_eq
#print axioms LiZouTransport.HubLimit.hub_value_tendsto_real_atTop
