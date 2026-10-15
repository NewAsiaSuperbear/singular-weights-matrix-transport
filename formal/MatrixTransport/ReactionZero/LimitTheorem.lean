import MatrixTransport.ReactionZero.WeightedSet
import MatrixTransport.ReactionZero.MatrixSymmetry
import MatrixTransport.ReactionZero.MatrixBounds
import MatrixTransport.ReactionZero.MinimumLimit
import MatrixTransport.ReactionZero.PathCoercivity
import MatrixTransport.ReactionZero.ClosedDomainTests
import MatrixTransport.ReactionZero.MatrixPositivity
import MatrixTransport.ReactionZero.MatrixVariation

/-!
# The actual reaction-weight-zero limit

This file connects the concrete signed Radon action, coordinate weak convergence and the
original closed-domain continuity equation. Its final certificates must be derived from actual
path bounds; abstract compactness and lower semicontinuity are not premises of the final result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.ReactionZero.Limit

variable {Q : Type*} [MetricSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]

omit [BorelSpace Q] in
/-- The Jordan pairing is bounded by the genuine signed total variation. -/
theorem abs_signedPair_le_totalVariation (s : SignedMeasure Q) (f : C(Q, ℝ)) :
    |MatrixTransport.signedPair s f| ≤ ‖f‖ * (s.totalVariation univ).toReal := by
  have hp := norm_integral_le_of_norm_le_const
    (μ := s.toJordanDecomposition.posPart) (f := fun x ↦ f x)
    (ae_of_all _ fun x ↦ f.norm_coe_le_norm x)
  have hn := norm_integral_le_of_norm_le_const
    (μ := s.toJordanDecomposition.negPart) (f := fun x ↦ f x)
    (ae_of_all _ fun x ↦ f.norm_coe_le_norm x)
  have htv : (s.totalVariation univ).toReal =
      s.toJordanDecomposition.posPart.real univ +
        s.toJordanDecomposition.negPart.real univ := by
    change (s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart).real univ = _
    rw [measureReal_add_apply]
  simp only [Real.norm_eq_abs] at hp hn
  calc |MatrixTransport.signedPair s f|
      ≤ |∫ x, f x ∂s.toJordanDecomposition.posPart| +
        |∫ x, f x ∂s.toJordanDecomposition.negPart| := abs_sub _ _
    _ ≤ ‖f‖ * s.toJordanDecomposition.posPart.real univ +
        ‖f‖ * s.toJordanDecomposition.negPart.real univ := add_le_add hp hn
    _ = ‖f‖ * (s.totalVariation univ).toReal := by rw [htv]; ring

omit [BorelSpace Q] in
/-- Vanishing total variation implies vanishing against every continuous test. -/
theorem signedPair_tendsto_zero_of_totalVariation (s : ℕ → SignedMeasure Q)
    (hTV : Tendsto (fun j ↦ (s j).totalVariation univ |>.toReal) atTop (𝓝 0))
    (f : C(Q, ℝ)) : Tendsto (fun j ↦ MatrixTransport.signedPair (s j) f) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun j ↦ by
    simpa only [Real.norm_eq_abs] using abs_signedPair_le_totalVariation (s j) f)
  simpa using (tendsto_const_nhds.mul hTV :
    Tendsto (fun j ↦ ‖f‖ * ((s j).totalVariation univ).toReal) atTop (𝓝 (‖f‖ * 0)))

variable {ι : Type*}

/-- An actual weakly convergent coordinate with vanishing variation has zero signed limit. -/
theorem coordinate_zero_of_signedWeakStar_totalVariation
    (μ : ℕ → ι → SignedMeasure Q) (ν : ι → SignedMeasure Q)
    (hμ : SignedWeakStarTendsto μ ν) (c : ι)
    (hTV : Tendsto (fun j ↦ ((μ j c).totalVariation univ).toReal) atTop (𝓝 0)) :
    ν c = 0 := by
  apply signedMeasure_eq_of_continuousPair_eq
  intro f
  have hz := signedPair_tendsto_zero_of_totalVariation (fun j ↦ μ j c) hTV f
  have heq := tendsto_nhds_unique (hμ c f) hz
  simpa [MatrixTransport.signedPair, SignedMeasure.toJordanDecomposition_zero] using heq

omit [CompactSpace Q] [BorelSpace Q] in
/-- Every further increasing subsequence retains the same concrete weak-star limit. -/
theorem signedWeakStarTendsto_subsequence (μ : ℕ → ι → SignedMeasure Q)
    (ν : ι → SignedMeasure Q) (hμ : SignedWeakStarTendsto μ ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν :=
  fun c f ↦ (hμ c f).comp hφ.tendsto_atTop

variable {n k : ℕ}

/-- A sufficiently small Frobenius weight is dominated by the identity in Loewner order. -/
theorem posSemidef_one_sub_gram (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : frobeniusSq H ≤ 1) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) - gram H).PosSemidef := by
  have hp : ((1 - frobeniusSq H) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (sub_nonneg.mpr hH)
  have hid : (1 - frobeniusSq H) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      (frobeniusSq H • (1 : Matrix (Fin n) (Fin n) ℝ) - gram H) = 1 - gram H := by
    module
  rw [← hid]
  exact hp.add (posSemidef_frobeniusSq_sub_gram H)

omit [MetricSpace Q] [CompactSpace Q] [BorelSpace Q] in
/-- Comparison uses the full triple and its own joint RN reference, so no reference-change
assumption is required. -/
theorem action_identity_le_of_frobeniusSq_le_one
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : frobeniusSq H ≤ 1) (μ : Coord n k → SignedMeasure Q) :
    action L 1 μ ≤ action L H μ := by
  apply action_mono_reaction L
  simpa only [Matrix.transpose_one, Matrix.one_mul, gram] using
    posSemidef_one_sub_gram H hH

/-- Fixed-weight lower semicontinuity gives the varying-weight lower bound on actual measures. -/
theorem action_identity_le_varying_liminf (L : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0))
    (μ : ℕ → Coord n k → SignedMeasure Q) (ν : Coord n k → SignedMeasure Q)
    (hμ : SignedWeakStarTendsto μ ν) :
    action L 1 ν ≤ atTop.liminf (fun j ↦ action L (H j) (μ j)) := by
  have he : ∀ᶠ j in atTop, action L 1 (μ j) ≤ action L (H j) (μ j) := by
    filter_upwards [hH.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hj
    exact action_identity_le_of_frobeniusSq_le_one L (H j) hj.le (μ j)
  exact (WeightedSet.action_le_liminf L 1 μ ν hμ).trans (liminf_le_liminf he)

/-- Convergence to zero gives a bound on the whole real sequence, including its finite prefix. -/
theorem exists_nonneg_bound_of_tendsto_zero (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (ht : Tendsto a atTop (𝓝 0)) : ∃ K : ℝ, 0 ≤ K ∧ ∀ j, a j ≤ K := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  have hs : 0 ≤ ∑ j ∈ Finset.range N, a j := Finset.sum_nonneg fun j _ ↦ ha j
  refine ⟨1 + ∑ j ∈ Finset.range N, a j, by positivity, ?_⟩
  intro j
  by_cases hj : j < N
  · have hb := Finset.single_le_sum (fun i (_ : i ∈ Finset.range N) ↦ ha i)
      (Finset.mem_range.mpr hj)
    linarith
  · have hb := hN j (le_of_not_gt hj)
    linarith

/-- A finite constrained infimum admits an actual admissible minimizing sequence. -/
theorem minimizing_sequence {P : Type*} (good : P → Prop) (energy : P → ℝ≥0∞)
    (hf : constrainedInfimum good energy ≠ ⊤) :
    ∃ u : ℕ → P, (∀ j, good (u j)) ∧
      Tendsto (fun j ↦ energy (u j)) atTop (𝓝 (constrainedInfimum good energy)) := by
  classical
  have he : ∃ p, good p := by
    have h := lt_top_iff_ne_top.mpr hf
    simp only [constrainedInfimum, iInf_lt_iff] at h
    obtain ⟨p, hp, _⟩ := h
    exact ⟨p, hp⟩
  obtain ⟨p, hp⟩ := he
  have hS : (energy '' {p | good p}).Nonempty := ⟨energy p, mem_image_of_mem _ hp⟩
  obtain ⟨v, _, hv, hvin⟩ := exists_seq_tendsto_sInf hS (OrderBot.bddBelow _)
  have hm : ∀ j, ∃ p, good p ∧ energy p = v j := fun j ↦ hvin j
  choose u hu heq using hm
  refine ⟨u, hu, ?_⟩
  have hid : sInf (energy '' {p | good p}) = constrainedInfimum good energy := by
    simp only [sInf_image, constrainedInfimum, mem_ofPred_eq]
  simpa only [heq, hid] using hv


section PaperProblem

variable {d : ℕ} {Ω : Set (ClosedDomain.Space d)}

/-- A concrete original problem, with arbitrary PSD signed Radon endpoints and operator. -/
structure Problem (Ω : Set (ClosedDomain.Space d)) (n k : ℕ) where
  operator : ClosedDomain.AdjointOperator d n k
  initial : (Fin n × Fin n) → SignedMeasure ↥Ω
  terminal : (Fin n × Fin n) → SignedMeasure ↥Ω
  initial_positive : ClosedDomain.EndpointPositiveSemidefinite initial
  terminal_positive : ClosedDomain.EndpointPositiveSemidefinite terminal

abbrev Path (Ω : Set (ClosedDomain.Space d)) (n k : ℕ) :=
  Coord n k → SignedMeasure (ClosedDomain.Q Ω)

/-- Definition 3.4's original symmetric measure ambient and complete closed-domain CE. -/
def Good (P : Problem Ω n k) (μ : Path Ω n k) : Prop :=
  MassSymmetric μ ∧ ClosedDomain.PaperContinuityEquation P.operator P.initial P.terminal μ

/-- The balanced problem requires the reaction coordinate measures themselves to vanish. -/
def Balanced (P : Problem Ω n k) (μ : Path Ω n k) : Prop :=
  Good P μ ∧ ∀ i j, μ (Sum.inr (Sum.inr (i, j))) = 0

def minimumValue (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  constrainedInfimum (Good P) (action L H)

def balancedValue (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ) : ℝ≥0∞ :=
  constrainedInfimum (Balanced P) (action L 1)

variable [Fact (IsCompact Ω)]

omit [Fact (IsCompact Ω)] in
/-- The actual RN trace identity is derived by testing the paper CE with (1−t)I. -/
theorem time_identity (P : Problem Ω n k) (μ : Path Ω n k) (hμ : Good P μ) :
    PathCoercivity.pathTrace μ = ClosedDomain.endpointMass P.initial +
      ∑ i, MatrixTransport.signedPair (μ (Sum.inr (Sum.inr (i, i)))) ClosedDomain.timeWeight := by
  have ht : PathCoercivity.pathTrace μ = ClosedDomain.massTracePair μ := by
    exact (ClosedDomain.massTracePair_eq_integral μ).symm
  exact ht.trans (ClosedDomain.massTracePair_eq_endpoint_add_reaction
    P.operator P.initial P.terminal μ hμ.2)

/-- Actual finite sublevels admit balanced weak-star limits: every ingredient comes from
proved RN coercivity, Jordan compactness, closed C¹ CE and the fixed weighted action. -/
theorem bounded_subsequence (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hgood : ∀ j, Good P (μ j)) (hE : ∀ j, action L (H j) (μ j) ≤ C) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Balanced P ν ∧ action L 1 ν ≤ C := by
  obtain ⟨K, hK, hHK⟩ := exists_nonneg_bound_of_tendsto_zero
    (fun j ↦ frobeniusSq (H j)) (fun j ↦ frobeniusSq_nonneg (H j)) hH
  let m0 := ClosedDomain.endpointMass P.initial
  have hm0 : 0 ≤ m0 := ClosedDomain.endpointMass_nonneg _ P.initial_positive
  have hwM : Measurable (ClosedDomain.timeWeight : ClosedDomain.Q Ω → ℝ) :=
    ClosedDomain.timeWeight.continuous.measurable
  have hw : ∀ x : ClosedDomain.Q Ω, 0 ≤ ClosedDomain.timeWeight x ∧
      ClosedDomain.timeWeight x ≤ 1 :=
    fun x ↦ ⟨ClosedDomain.timeWeight_nonneg x, ClosedDomain.timeWeight_le_one x⟩
  have hfin : ∀ j, action L (H j) (μ j) ≠ ⊤ :=
    fun j ↦ ne_top_of_le_ne_top hC (hE j)
  have hEreal : ∀ j, (action L (H j) (μ j)).toReal ≤ C.toReal :=
    fun j ↦ ENNReal.toReal_mono hC (hE j)
  have hEof : ∀ j, action L (H j) (μ j) ≤ ENNReal.ofReal C.toReal := by
    intro j
    simpa only [ENNReal.ofReal_toReal hC] using hE j
  have hT : ∀ j, PathCoercivity.pathTrace (μ j) ≤ 2 * m0 + 2 * K * C.toReal := by
    intro j
    exact PathCoercivity.pathTrace_bound_on_sublevel L (H j) (μ j) (hgood j).1
      C.toReal K ENNReal.toReal_nonneg (hEof j) (hHK j)
      ClosedDomain.timeWeight hwM hw m0 hm0 (time_identity P (μ j) (hgood j))
  let B := Real.toNNReal (PathCoercivity.coordinateTVBound C.toReal
    (2 * m0 + 2 * K * C.toReal) (frobeniusSq L) K)
  have hTV : ∀ j c, ((μ j c).totalVariation univ) ≤ (B : ℝ≥0∞) := by
    intro j c
    exact PathCoercivity.coordinateTV_le_on_sublevel L (H j) (μ j) (hgood j).1
      C.toReal K ENNReal.toReal_nonneg (hEof j) (hHK j)
      ClosedDomain.timeWeight hwM hw m0 hm0 (time_identity P (μ j) (hgood j)) c
  obtain ⟨ν, φ, hφ, hweak⟩ := signedMeasureFamily_subsequence B μ hTV
  have hνgood : Good P ν :=
    ⟨massSymmetric_of_signedWeakStar _ _ hweak (fun j ↦ (hgood (φ j)).1),
      ClosedDomain.paperContinuityEquation_of_signedWeakStar P.operator P.initial P.terminal
        _ ν hweak (fun j ↦ (hgood (φ j)).2)⟩
  have hzero : ∀ i j, ν (Sum.inr (Sum.inr (i, j))) = 0 := by
    intro i j
    have hz := PathCoercivity.reactionTV_toReal_tendsto_zero L H μ
      (fun a ↦ (hgood a).1) hfin C.toReal (2 * m0 + 2 * K * C.toReal)
      hEreal hT hH i j
    exact coordinate_zero_of_signedWeakStar_totalVariation _ ν hweak _
      (hz.comp hφ.tendsto_atTop)
  have he := action_identity_le_varying_liminf L (fun j ↦ H (φ j))
    (hH.comp hφ.tendsto_atTop) _ ν hweak
  have hb : atTop.liminf (fun j ↦ action L (H (φ j)) (μ (φ j))) ≤ C :=
    liminf_le_of_frequently_le' (Filter.Eventually.of_forall (fun j ↦ hE (φ j))).frequently
  exact ⟨ν, φ, hφ, hweak, ⟨hνgood, hzero⟩, he.trans hb⟩

/-- The abstract minimum certificate is instantiated by actual signed Radon paths. -/
theorem bounded_sequence_certificate (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (μ : ℕ → Path Ω n k) (hgood : ∀ j, Good P (μ j))
    (hE : ∀ j, action L (H (φ j)) (μ j) ≤ C) :
    ∃ ν, Balanced P ν ∧ action L 1 ν ≤ C := by
  obtain ⟨ν, ψ, hψ, hw, hb, he⟩ := bounded_subsequence P L (fun j ↦ H (φ j))
    (hH.comp hφ.tendsto_atTop) C hC μ hgood hE
  exact ⟨ν, hb, he⟩

omit [Fact (IsCompact Ω)] in
/-- Constant recovery is exact for every actual zero-reaction path, including infinite costs. -/
theorem balanced_recovery (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Path Ω n k) (hμ : Balanced P μ) :
    action L H μ = action L 1 μ :=
  action_eq_of_reaction_measures_zero L H 1 μ hμ.2

/-- The full original shrinking-reaction-weight minimum regime, including infinite limits.
Compactness, coercivity and lower semicontinuity are proved ingredients, not assumptions. -/
theorem minimumValue_tendsto (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0)) :
    Tendsto (fun j ↦ minimumValue P L (H j)) atTop (𝓝 (balancedValue P L)) := by
  exact constrainedInfimum_tendsto (Good P) (Balanced P)
    (fun j ↦ action L (H j)) (action L 1)
    (fun μ hμ ↦ hμ.1) (fun j μ hμ ↦ (balanced_recovery P L (H j) μ hμ).le)
    (bounded_sequence_certificate P L H hH)

/-- Finite-prefix exceptions do not prevent the actual balanced subsequence conclusion. -/
theorem eventually_bounded_subsequence (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hgood : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, action L (H j) (μ j) ≤ C) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Balanced P ν ∧ action L 1 ν ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hE
  let σ : ℕ → ℕ := fun j ↦ j + N
  have hσ : StrictMono σ := fun a b hab ↦ Nat.add_lt_add_right hab N
  obtain ⟨ν, φ, hφ, hw, hb, he⟩ := bounded_subsequence P L (fun j ↦ H (σ j))
    (hH.comp hσ.tendsto_atTop) C hC (fun j ↦ μ (σ j))
    (fun j ↦ hgood (σ j)) (fun j ↦ hN (σ j) (by dsimp [σ]; omega))
  exact ⟨ν, σ ∘ φ, hσ.comp hφ, hw, hb, he⟩

omit [Fact (IsCompact Ω)] in
/-- Vanishing reaction TV is derived on eventual finite original CE action sublevels. -/
theorem reactionTV_tendsto_zero_of_eventually_bounded (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hgood : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, action L (H j) (μ j) ≤ C) (i j : Fin n) :
    Tendsto (fun a ↦ (μ a (Sum.inr (Sum.inr (i, j)))).totalVariation univ)
      atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hE
  let σ : ℕ → ℕ := fun a ↦ a + N
  have hσ : StrictMono σ := fun a b hab ↦ Nat.add_lt_add_right hab N
  have hbound : ∀ a, action L (H (σ a)) (μ (σ a)) ≤ ENNReal.ofReal C.toReal := by
    intro a
    simpa only [ENNReal.ofReal_toReal hC] using hN (σ a) (by dsimp [σ]; omega)
  have hwM : Measurable (ClosedDomain.timeWeight : ClosedDomain.Q Ω → ℝ) :=
    ClosedDomain.timeWeight.continuous.measurable
  have hw : ∀ x : ClosedDomain.Q Ω, 0 ≤ ClosedDomain.timeWeight x ∧
      ClosedDomain.timeWeight x ≤ 1 :=
    fun x ↦ ⟨ClosedDomain.timeWeight_nonneg x, ClosedDomain.timeWeight_le_one x⟩
  have hc := PathCoercivity.sublevel_coercivity_and_reaction_vanishing L (fun a ↦ H (σ a))
    (fun a ↦ μ (σ a)) (fun a ↦ (hgood (σ a)).1) C.toReal ENNReal.toReal_nonneg
    hbound ClosedDomain.timeWeight hwM hw (ClosedDomain.endpointMass P.initial)
    (ClosedDomain.endpointMass_nonneg _ P.initial_positive)
    (fun a ↦ time_identity P (μ (σ a)) (hgood (σ a))) (hH.comp hσ.tendsto_atTop)
  exact (tendsto_add_atTop_iff_nat N).1 (hc.2 i j)

omit [Fact (IsCompact Ω)] in
/-- The balanced infimum is an upper bound for each weighted minimum, even when infinite. -/
theorem minimumValue_le_balanced (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) : minimumValue P L H ≤ balancedValue P L :=
  constrainedInfimum_le_balanced (Good P) (Balanced P) (fun _ : ℕ ↦ action L H)
    (action L 1) (fun _μ hμ ↦ hμ.1) (fun _ μ hμ ↦ (balanced_recovery P L H μ hμ).le) 0

/-- Actual near-minimizer energies converge to the balanced value. The errors may be
extended-valued in a finite prefix; only their convergence to zero is required. -/
theorem nearMinimizer_energy_tendsto (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0))
    (μ : ℕ → Path Ω n k) (hgood : ∀ j, Good P (μ j))
    (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (𝓝 0))
    (hnear : ∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + ε j) :
    Tendsto (fun j ↦ action L (H j) (μ j)) atTop (𝓝 (balancedValue P L)) := by
  have hv := minimumValue_tendsto P L H hH
  have hupper : Tendsto (fun j ↦ minimumValue P L (H j) + ε j)
      atTop (𝓝 (balancedValue P L)) := by simpa only [add_zero] using hv.add hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hv hupper
  · intro j
    exact iInf_le_of_le (μ j) (iInf_le_of_le (hgood j) le_rfl)
  · exact hnear

/-- Every convergent increasing subsequence of finite-limit near-minimizers has an actual
balanced optimal limit, with no assumed compactness or lower-semicontinuity certificate. -/
theorem nearMinimizer_cluster (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0))
    (hb : balancedValue P L ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hgood : ∀ j, Good P (μ j)) (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (𝓝 0))
    (hnear : ∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + ε j)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (ν : Path Ω n k)
    (hweak : SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν) :
    Balanced P ν ∧ action L 1 ν = balancedValue P L := by
  have henergy := nearMinimizer_energy_tendsto P L H hH μ hgood ε hε hnear
  obtain ⟨C, hbC, hCtop⟩ := exists_between (lt_top_iff_ne_top.mpr hb)
  have hbound : ∀ᶠ j in atTop, action L (H j) (μ j) ≤ C :=
    (henergy.eventually (gt_mem_nhds hbC)).mono fun _ h ↦ h.le
  have hνgood : Good P ν :=
    ⟨massSymmetric_of_signedWeakStar _ _ hweak (fun j ↦ (hgood (φ j)).1),
      ClosedDomain.paperContinuityEquation_of_signedWeakStar P.operator P.initial P.terminal
        _ ν hweak (fun j ↦ (hgood (φ j)).2)⟩
  have hzero : ∀ i j, ν (Sum.inr (Sum.inr (i, j))) = 0 := by
    intro i j
    have hTV := reactionTV_tendsto_zero_of_eventually_bounded P L H hH C hCtop.ne
      μ hgood hbound i j
    have hTVreal := (ENNReal.tendsto_toReal_zero_iff (fun _ ↦ measure_ne_top _ _)).2 hTV
    exact coordinate_zero_of_signedWeakStar_totalVariation _ ν hweak _
      (hTVreal.comp hφ.tendsto_atTop)
  have hνbal : Balanced P ν := ⟨hνgood, hzero⟩
  have he := action_identity_le_varying_liminf L (fun j ↦ H (φ j))
    (hH.comp hφ.tendsto_atTop) _ ν hweak
  have hlim : atTop.liminf (fun j ↦ action L (H (φ j)) (μ (φ j))) = balancedValue P L := by
    simpa only [Function.comp_def] using (henergy.comp hφ.tendsto_atTop).liminf_eq
  rw [hlim] at he
  exact ⟨hνbal, le_antisymm he (iInf_le_of_le ν (iInf_le_of_le hνbal le_rfl))⟩

/-- Finite-limit near-minimizers have a weak-star convergent balanced minimizing subsequence,
and every original reaction coordinate tends to zero in total variation. -/
theorem nearMinimizer_subsequence (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0))
    (hb : balancedValue P L ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hgood : ∀ j, Good P (μ j)) (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (𝓝 0))
    (hnear : ∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + ε j) :
    (∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Balanced P ν ∧
        action L 1 ν = balancedValue P L) ∧
    ∀ i j, Tendsto (fun a ↦ (μ a (Sum.inr (Sum.inr (i, j)))).totalVariation univ)
      atTop (𝓝 0) := by
  have henergy := nearMinimizer_energy_tendsto P L H hH μ hgood ε hε hnear
  obtain ⟨C, hbC, hCtop⟩ := exists_between (lt_top_iff_ne_top.mpr hb)
  have hbound : ∀ᶠ j in atTop, action L (H j) (μ j) ≤ C :=
    (henergy.eventually (gt_mem_nhds hbC)).mono fun _ h ↦ h.le
  obtain ⟨ν, φ, hφ, hw, _, _⟩ := eventually_bounded_subsequence P L H hH
    C hCtop.ne μ hgood hbound
  have hc := nearMinimizer_cluster P L H hH hb μ hgood ε hε hnear φ hφ ν hw
  exact ⟨⟨ν, φ, hφ, hw, hc.1, hc.2⟩,
    reactionTV_tendsto_zero_of_eventually_bounded P L H hH C hCtop.ne μ hgood hbound⟩

/-- Every finite balanced infimum is attained by an actual signed Radon path satisfying the
full original CE. Balanced compactness is obtained using zero reaction weight and exact recovery. -/
theorem balanced_attainment (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (hb : balancedValue P L ≠ ⊤) :
    ∃ ν : Path Ω n k, Balanced P ν ∧ action L 1 ν = balancedValue P L := by
  obtain ⟨μ, hbal, ht⟩ := minimizing_sequence (Balanced P) (action L 1) hb
  have hgood : ∀ j, Good P (μ j) := fun j ↦ (hbal j).1
  have hzero : Tendsto (fun _ : ℕ ↦ frobeniusSq (0 : Matrix (Fin n) (Fin n) ℝ))
      atTop (𝓝 0) := by simp [frobeniusSq]
  have heq : (fun j ↦ action L (0 : Matrix (Fin n) (Fin n) ℝ) (μ j)) =
      fun j ↦ action L 1 (μ j) :=
    funext fun j ↦ balanced_recovery P L 0 (μ j) (hbal j)
  have ht0 : Tendsto (fun j ↦ action L (0 : Matrix (Fin n) (Fin n) ℝ) (μ j))
      atTop (𝓝 (balancedValue P L)) := by rw [heq]; exact ht
  obtain ⟨C, hbC, hCtop⟩ := exists_between (lt_top_iff_ne_top.mpr hb)
  have hbound : ∀ᶠ j in atTop, action L (0 : Matrix (Fin n) (Fin n) ℝ) (μ j) ≤ C :=
    (ht0.eventually (gt_mem_nhds hbC)).mono fun _ h ↦ h.le
  obtain ⟨ν, φ, hφ, hw, hνbal, _⟩ := eventually_bounded_subsequence P L
    (fun _ ↦ (0 : Matrix (Fin n) (Fin n) ℝ)) hzero C hCtop.ne μ hgood hbound
  have he := action_identity_le_varying_liminf L (fun _ ↦ (0 : Matrix (Fin n) (Fin n) ℝ))
    hzero _ ν hw
  have hlim : atTop.liminf (fun j ↦ action L (0 : Matrix (Fin n) (Fin n) ℝ) (μ (φ j))) =
      balancedValue P L := by
    simpa only [Function.comp_def] using (ht0.comp hφ.tendsto_atTop).liminf_eq
  rw [hlim] at he
  exact ⟨ν, hνbal, le_antisymm he (iInf_le_of_le ν (iInf_le_of_le hνbal le_rfl))⟩

/-- The complete variational answer to the paper's reaction-weight-zero regime: extended
minimum convergence, finite balanced attainment, and vanishing-gap minimizer compactness with
vanishing reaction coordinate variation. The hypotheses are the concrete original data and
weight convergence; no analytic conclusion is postulated as a certificate. -/
theorem reaction_zero_regime (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0)) :
    Tendsto (fun j ↦ minimumValue P L (H j)) atTop (𝓝 (balancedValue P L)) ∧
    (balancedValue P L ≠ ⊤ →
      ∃ ν : Path Ω n k, Balanced P ν ∧ action L 1 ν = balancedValue P L) ∧
    (∀ (_hb : balancedValue P L ≠ ⊤) (μ : ℕ → Path Ω n k),
      (∀ j, Good P (μ j)) → ∀ (ε : ℕ → ℝ≥0∞), Tendsto ε atTop (𝓝 0) →
      (∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + ε j) →
        (∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
          SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Balanced P ν ∧
            action L 1 ν = balancedValue P L) ∧
        ∀ i j, Tendsto (fun a ↦ (μ a (Sum.inr (Sum.inr (i, j)))).totalVariation univ)
          atTop (𝓝 0)) :=
  ⟨minimumValue_tendsto P L H hH, balanced_attainment P L,
    fun hb μ hgood ε hε hnear ↦ nearMinimizer_subsequence P L H hH hb μ hgood ε hε hnear⟩

/-- The paper's explicit Frobenius norm, without choosing an ambient matrix norm instance. -/
def frobeniusNorm (H : Matrix (Fin n) (Fin n) ℝ) : ℝ := Real.sqrt (frobeniusSq H)

/-- Squared Frobenius convergence and the paper's Frobenius-norm convergence are equivalent. -/
theorem frobeniusNorm_tendsto_zero_iff (H : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun j ↦ frobeniusNorm (H j)) atTop (𝓝 0) ↔
      Tendsto (fun j ↦ frobeniusSq (H j)) atTop (𝓝 0) := by
  constructor
  · intro h
    have hid : (fun j ↦ frobeniusSq (H j)) = fun j ↦ frobeniusNorm (H j) ^ 2 :=
      funext fun j ↦ (Real.sq_sqrt (frobeniusSq_nonneg (H j))).symm
    rw [hid]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using h.pow 2
  · intro h
    simpa only [frobeniusNorm, Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h

/-- Direct original-norm statement of the full extended minimum-value limit. -/
theorem minimumValue_tendsto_frobeniusNorm (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusNorm (H j)) atTop (𝓝 0)) :
    Tendsto (fun j ↦ minimumValue P L (H j)) atTop (𝓝 (balancedValue P L)) :=
  minimumValue_tendsto P L H ((frobeniusNorm_tendsto_zero_iff H).1 hH)

/-- The finite balanced optimum has positive semidefinite matrix measure values on every
measurable set, as in the original matrix Radon class. -/
theorem balanced_attainment_posSemidef (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (hb : balancedValue P L ≠ ⊤) :
    ∃ ν : Path Ω n k, Balanced P ν ∧ action L 1 ν = balancedValue P L ∧
      ∀ B : Set (ClosedDomain.Q Ω), MeasurableSet B →
        (MatrixPositivity.massMeasureValue ν B).PosSemidef := by
  obtain ⟨ν, hν, he⟩ := balanced_attainment P L hb
  have hfinite : action L (1 : Matrix (Fin n) (Fin n) ℝ) ν ≠ ⊤ := by
    rw [he]
    exact hb
  exact ⟨ν, hν, he, fun B hB ↦
    MatrixPositivity.massMeasureValue_posSemidef L 1 ν hν.1.1 hfinite B hB⟩

/-- The original reaction Frobenius total variation vanishes for the entire sequence of
finite-limit near-minimizers, rather than only for an extracted subsequence. -/
theorem nearMinimizer_frobeniusTV_tendsto_zero (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusNorm (H j)) atTop (𝓝 0))
    (hb : balancedValue P L ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hgood : ∀ j, Good P (μ j)) (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (𝓝 0))
    (hnear : ∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + ε j) :
    Tendsto (fun j ↦ MatrixVariation.reactionFrobeniusTV (μ j)) atTop (𝓝 0) :=
  MatrixVariation.reactionFrobeniusTV_tendsto_zero μ
    (nearMinimizer_subsequence P L H ((frobeniusNorm_tendsto_zero_iff H).1 hH)
      hb μ hgood ε hε hnear).2

/-- A direct Frobenius-norm formulation of the complete original reaction-zero regime:
extended optimal-value convergence, finite balanced attainment in the PSD Radon class,
near-minimizer energy and weak-star subsequences, vanishing reaction Frobenius TV, and
optimality of every increasing-subsequence cluster point. -/
theorem reaction_zero_regime_frobeniusNorm (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto (fun j ↦ frobeniusNorm (H j)) atTop (𝓝 0)) :
    Tendsto (fun j ↦ minimumValue P L (H j)) atTop (𝓝 (balancedValue P L)) ∧
    (balancedValue P L ≠ ⊤ →
      ∃ ν : Path Ω n k, Balanced P ν ∧ action L 1 ν = balancedValue P L ∧
        ∀ B : Set (ClosedDomain.Q Ω), MeasurableSet B →
          (MatrixPositivity.massMeasureValue ν B).PosSemidef) ∧
    (∀ (_hb : balancedValue P L ≠ ⊤) (μ : ℕ → Path Ω n k),
      (∀ j, Good P (μ j)) → ∀ (ε : ℕ → ℝ≥0∞), Tendsto ε atTop (𝓝 0) →
      (∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + ε j) →
        Tendsto (fun j ↦ action L (H j) (μ j)) atTop (𝓝 (balancedValue P L)) ∧
        (∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
          SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Balanced P ν ∧
            action L 1 ν = balancedValue P L) ∧
        Tendsto (fun j ↦ MatrixVariation.reactionFrobeniusTV (μ j)) atTop (𝓝 0) ∧
        ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (ν : Path Ω n k),
          SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν →
            Balanced P ν ∧ action L 1 ν = balancedValue P L) := by
  have hsq := (frobeniusNorm_tendsto_zero_iff H).1 hH
  refine ⟨minimumValue_tendsto_frobeniusNorm P L H hH,
    balanced_attainment_posSemidef P L, ?_⟩
  intro hb μ hgood ε hε hnear
  exact ⟨nearMinimizer_energy_tendsto P L H hsq μ hgood ε hε hnear,
    (nearMinimizer_subsequence P L H hsq hb μ hgood ε hε hnear).1,
    nearMinimizer_frobeniusTV_tendsto_zero P L H hH hb μ hgood ε hε hnear,
    fun φ hφ ν hw ↦ nearMinimizer_cluster P L H hsq hb μ hgood ε hε hnear φ hφ ν hw⟩

end PaperProblem

#print axioms coordinate_zero_of_signedWeakStar_totalVariation
#print axioms action_identity_le_varying_liminf
#print axioms bounded_subsequence
#print axioms minimumValue_tendsto
#print axioms nearMinimizer_cluster
#print axioms nearMinimizer_subsequence
#print axioms balanced_attainment
#print axioms reaction_zero_regime
#print axioms minimumValue_tendsto_frobeniusNorm
#print axioms balanced_attainment_posSemidef
#print axioms nearMinimizer_frobeniusTV_tendsto_zero
#print axioms reaction_zero_regime_frobeniusNorm

end MatrixTransport.ReactionZero.Limit
