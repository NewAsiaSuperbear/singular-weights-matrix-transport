import MatrixTransport.EntrywiseBures.ReactionPiece
import MatrixTransport.EntrywiseBures.UniformBures

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Matrix
namespace LiZouTransport.Hub
open MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures
open MatrixTransport.ReactionZero.Limit LiZouTransport.Reaction
variable {d n : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

theorem hubMoment_nonneg {g : (Fin n × Fin n) → SignedMeasure ↥Ω}
    (hg : EndpointPositiveSemidefinite g) (xstar : Space d) : 0 ≤ hubMoment g xstar := by
  rw [hubMoment_eq_integral]
  exact integral_nonneg_of_ae (by
    filter_upwards [ae_endpointDensity_posSemidef hg] with x hx
    exact mul_nonneg (sq_nonneg _) hx.trace_nonneg)

def hubMeasure (G : HubGeometry d Ω) : Measure ↥Ω :=
  Measure.dirac ⟨G.hub, interior_subset G.hub_mem⟩

instance hubMeasure_finite (G : HubGeometry d Ω) : IsFiniteMeasure (hubMeasure G) := by
  unfold hubMeasure
  infer_instance

theorem hubMeasure_univ (G : HubGeometry d Ω) : hubMeasure G univ = 1 := by
  simp [hubMeasure]

theorem endpointPair_hub (G : HubGeometry d Ω) (A : RMat n)
    (φ : ClosedC1Jet Ω n) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    endpointPair (uniformEndpoint (hubMeasure G) A) φ a ha =
      MatrixTransport.ReactionZero.frob (zeroExtend φ.value (a, G.hub)) A := by
  rw [endpointPair_uniformEndpoint]
  rw [hubMeasure, integral_dirac]
  rw [zeroExtend_of_mem φ.value ⟨ha, interior_subset G.hub_mem⟩]
  rfl

/-- The original three-piece contraction, reaction, expansion path. -/
theorem exists_hub_competitor (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) (hD : P.operator = entrywiseDivergence d n)
    {H : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    {r0 r1 r2 : ℝ} (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) {t : ℝ} (ht : 0 < t) :
    ∃ μ : Path Ω n (d * n), Good P μ ∧
      MatrixTransport.ReactionZero.action (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H μ ≤
        ENNReal.ofReal (hubMoment P.initial G.hub / (2 * t ^ 2 * r0) +
          buresValue R H (totalMatrix P.initial) (totalMatrix P.terminal) / r1 +
          hubMoment P.terminal G.hub / (2 * t ^ 2 * r2)) := by
  obtain ⟨W,Δ,hW0,hW1,hE⟩ := exists_bures_reaction_factor R hH hHu
    (totalMatrix_posSemidef P.initial_positive) (totalMatrix_posSemidef P.terminal_positive)
  have ha0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have ha1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hb0 : 0 + 1 * r0 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
  have har : r0 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
  have hbr : r0 + r1 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
  have hb2 : 1 + (-1) * r2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
  let μ0 := lagPath G P.initial 0 1 r0 ha0 hb0
  let μ1 : Path Ω n (d*n) := reactionPath (hubMeasure G) H W Δ r0 r1 har hbr hr1
  let μ2 := lagPath G P.terminal 1 (-1) r2 ha1 hb2
  refine ⟨(μ0 + μ1) + μ2, ⟨?_, ?_⟩, ?_⟩
  · have h0 := lagPath_massSymmetric G P.initial_positive 0 1 r0 ha0 hb0
    have h1 := reactionPath_massSymmetric (k := d*n) (hubMeasure G) H W Δ r0 r1 har hbr hr1
    have h2 := lagPath_massSymmetric G P.terminal_positive 1 (-1) r2 ha1 hb2
    change MatrixTransport.ReactionZero.MassSymmetric μ0 at h0
    change MatrixTransport.ReactionZero.MassSymmetric μ1 at h1
    change MatrixTransport.ReactionZero.MassSymmetric μ2 at h2
    intro i j
    simp only [Pi.add_apply]
    change (μ0 (Sum.inl (i,j)) + μ1 (Sum.inl (i,j))) + μ2 (Sum.inl (i,j)) = _
    rw [h0 i j, h1 i j, h2 i j]
  · intro φ
    change MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1)
      ((μ0 + μ1) + μ2) (testField P.operator φ) =
      endpointPair P.terminal φ 1 ha1 - endpointPair P.initial φ 0 ha0
    rw [hD, coordinatePair_add, coordinatePair_add]
    have hc0 := lagPiece_coordinatePair G P.initial_positive ha0 hb0 (Or.inl rfl) hr0 φ
    have hc2 := lagPiece_coordinatePair G P.terminal_positive ha1 hb2 (Or.inr rfl) hr2 φ
    have hc1 := reactionPath_coordinatePair G (entrywiseDivergence d n) (hubMeasure G)
      hH W Δ r0 r1 har hbr hr1 φ
    rw [factorMass_zero, factorMass_one, hW0, hW1,
      endpointPair_hub, endpointPair_hub] at hc1
    change MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1) μ0 _ = _ at hc0
    change MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1) μ1 _ = _ at hc1
    change MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1) μ2 _ = _ at hc2
    rw [hc0, hc1, hc2]
    have htime : r0 + r1 = 1 + (-1) * r2 := by linarith
    simp only [zero_add, one_mul, neg_one_mul] at ⊢ htime
    rw [htime]
    ring
  · have hc0 := lagPiece_action_le R G P.initial_positive ha0 hb0 (by norm_num) hr0 ht H
    have hc2 := lagPiece_action_le R G P.terminal_positive ha1 hb2 (by norm_num) hr2 ht H
    have hc1 := reactionPath_action_le (hubMeasure G)
      (t • (1 : Matrix (Fin (d*n)) (Fin (d*n)) ℝ)) hH W Δ r0 r1 har hbr hr1
    rw [hubMeasure_univ, mul_one] at hc1
    have he : 2 / r1 * MatrixTransport.ReactionZero.frobeniusSq Δ =
      buresValue R H (totalMatrix P.initial) (totalMatrix P.terminal) / r1 := by
      rw [← hE]
      ring
    rw [he] at hc1
    have ha := action_add_le (t • (1 : Matrix (Fin (d*n)) (Fin (d*n)) ℝ)) H (μ0+μ1) μ2
    have hb := action_add_le (t • (1 : Matrix (Fin (d*n)) (Fin (d*n)) ℝ)) H μ0 μ1
    change MatrixTransport.ReactionZero.action
      (t • (1 : Matrix (Fin (d*n)) (Fin (d*n)) ℝ)) H μ0 ≤ _ at hc0
    change MatrixTransport.ReactionZero.action
      (t • (1 : Matrix (Fin (d*n)) (Fin (d*n)) ℝ)) H μ1 ≤ _ at hc1
    change MatrixTransport.ReactionZero.action
      (t • (1 : Matrix (Fin (d*n)) (Fin (d*n)) ℝ)) H μ2 ≤ _ at hc2
    have hsame : MatrixTransport.ReactionZero.action
      (t • (1 : Matrix (Fin (d*n)) (Fin (d*n)) ℝ)) H μ2 ≤
      MatrixTransport.ReactionZero.action
      (t • (1 : Matrix (Fin (d*n)) (Fin (d*n)) ℝ)) H μ2 := le_rfl
    have habound := add_le_add hb hsame
    have hfull := le_trans ha habound
    apply le_trans hfull
    refine (add_le_add (add_le_add hc0 hc1) hc2).trans ?_
    have hn0 : 0 ≤ hubMoment P.initial G.hub / (2 * t ^ 2 * r0) :=
      div_nonneg (hubMoment_nonneg P.initial_positive G.hub) (by positivity)
    have hn1 : 0 ≤ buresValue R H (totalMatrix P.initial) (totalMatrix P.terminal) / r1 :=
      div_nonneg (buresValue_nonneg R hH hHu
        (totalMatrix_posSemidef P.initial_positive)
        (totalMatrix_posSemidef P.terminal_positive)) hr1.le
    have hn2 : 0 ≤ hubMoment P.terminal G.hub / (2 * t ^ 2 * r2) :=
      div_nonneg (hubMoment_nonneg P.terminal_positive G.hub) (by positivity)
    rw [← ENNReal.ofReal_add hn0 hn1, ← ENNReal.ofReal_add (add_nonneg hn0 hn1) hn2]


#print axioms exists_hub_competitor
end LiZouTransport.Hub
