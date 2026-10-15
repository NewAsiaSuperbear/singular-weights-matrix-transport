import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import MatrixTransport.Pairing

/-!
# Weak compactness of finite families of signed Radon measures

The positive and negative Jordan parts have uniformly bounded mass. We obtain a common
subsequence by compactness of bounded masses and probability measures, then reconstruct
the signed limits. Every continuous real test converges along the same subsequence.

No compactness assumption on a space of signed measures is used.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatrixTransport.ReactionZero

variable {Q : Type*} [MetricSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]
variable {ι : Type*} [Fintype ι]

/-- Continuous real tests are integrable against every finite positive measure on `Q`. -/
theorem continuousTest_integrable (f : C(Q, ℝ)) (μ : Measure Q) [IsFiniteMeasure μ] :
    Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- A finite positive family admits a common weakly convergent subsequence. -/
theorem finiteMeasureFamily_subsequence [Nonempty Q] (C : ℝ≥0)
    (μ : ℕ → ι → FiniteMeasure Q) (hμ : ∀ n i, (μ n i).mass ≤ C) :
    ∃ (ν : ι → FiniteMeasure Q) (φ : ℕ → ℕ),
      StrictMono φ ∧ ∀ i, Tendsto (fun n ↦ μ (φ n) i) atTop (𝓝 (ν i)) := by
  let K := {r : ℝ≥0 // r ∈ Icc 0 C}
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) C))
  let lift : ℕ → ι → K × ProbabilityMeasure Q :=
    fun n i ↦ (⟨(μ n i).mass, ⟨bot_le, hμ n i⟩⟩, (μ n i).normalize)
  obtain ⟨p, φ, hφ, hp⟩ := CompactSpace.tendsto_subseq lift
  refine ⟨fun i ↦ (p i).1.val • (p i).2.toFiniteMeasure, φ, hφ, ?_⟩
  intro i
  have hi := (continuous_apply i).tendsto p |>.comp hp
  have hm := (continuous_subtype_val.tendsto (p i).1).comp
    ((continuous_fst.tendsto (p i)).comp hi)
  have hn := ProbabilityMeasure.toFiniteMeasure_continuous.tendsto (p i).2 |>.comp
    ((continuous_snd.tendsto (p i)).comp hi)
  have hh := hm.smul hn
  change Tendsto (fun n ↦ (μ (φ n) i).mass • (μ (φ n) i).normalize.toFiniteMeasure)
    atTop (𝓝 ((p i).1.val • (p i).2.toFiniteMeasure)) at hh
  have hrepr : (fun n ↦ μ (φ n) i) =
      fun n ↦ (μ (φ n) i).mass • (μ (φ n) i).normalize.toFiniteMeasure :=
    funext fun n ↦ (μ (φ n) i).self_eq_mass_smul_normalize
  rw [hrepr]
  exact hh

/-- The original Jordan pairing agrees with the scalar vector-measure integral. -/
theorem signedPair_eq_vectorIntegral (s : SignedMeasure Q) (f : C(Q, ℝ)) :
    MatrixTransport.signedPair s f = ∫ᵛ x, f x ∂<•s := by
  have hp : s.toJordanDecomposition.posPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      continuousTest_integrable f s.toJordanDecomposition.posPart
  have hn : s.toJordanDecomposition.negPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      continuousTest_integrable f s.toJordanDecomposition.negPart
  calc
    MatrixTransport.signedPair s f =
        (∫ x, f x ∂s.toJordanDecomposition.posPart) -
          (∫ x, f x ∂s.toJordanDecomposition.negPart) := rfl
    _ = (∫ᵛ x, f x ∂<•s.toJordanDecomposition.posPart.toSignedMeasure) -
          (∫ᵛ x, f x ∂<•s.toJordanDecomposition.negPart.toSignedMeasure) := by simp
    _ = ∫ᵛ x, f x ∂<•(s.toJordanDecomposition.posPart.toSignedMeasure -
          s.toJordanDecomposition.negPart.toSignedMeasure) :=
      (VectorMeasure.integral_sub_vectorMeasure hp hn).symm
    _ = ∫ᵛ x, f x ∂<•s := by
      rw [← JordanDecomposition.toSignedMeasure,
        SignedMeasure.toSignedMeasure_toJordanDecomposition]

/-- Jordan pairing of a difference of finite positive measures, without a mutual-singularity
assumption on those measures. Weak limits of Jordan parts need not remain mutually singular. -/
theorem signedPair_difference (a b : FiniteMeasure Q) (f : C(Q, ℝ)) :
    MatrixTransport.signedPair
      ((a : Measure Q).toSignedMeasure - (b : Measure Q).toSignedMeasure) f =
        (∫ x, f x ∂(a : Measure Q)) - (∫ x, f x ∂(b : Measure Q)) := by
  have ha : (a : Measure Q).toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      continuousTest_integrable f (a : Measure Q)
  have hb : (b : Measure Q).toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      continuousTest_integrable f (b : Measure Q)
  rw [signedPair_eq_vectorIntegral,
    VectorMeasure.integral_sub_vectorMeasure ha hb]
  simp

/-- The finite positive or negative Jordan part. `true` selects the positive part. -/
def jordanFinite (s : SignedMeasure Q) (positive : Bool) : FiniteMeasure Q :=
  if positive then ⟨s.toJordanDecomposition.posPart, inferInstance⟩
  else ⟨s.toJordanDecomposition.negPart, inferInstance⟩

omit [MetricSpace Q] [CompactSpace Q] [BorelSpace Q] in
/-- Each Jordan part has mass at most the total variation mass. -/
theorem jordanFinite_mass_le (s : SignedMeasure Q) (positive : Bool) (C : ℝ≥0)
    (hs : s.totalVariation univ ≤ (C : ℝ≥0∞)) :
    (jordanFinite s positive).mass ≤ C := by
  have hp : s.toJordanDecomposition.posPart univ ≤ (C : ℝ≥0∞) :=
    (le_add_right le_rfl).trans (by simpa [SignedMeasure.totalVariation] using hs)
  have hn : s.toJordanDecomposition.negPart univ ≤ (C : ℝ≥0∞) :=
    (le_add_left le_rfl).trans (by simpa [SignedMeasure.totalVariation] using hs)
  cases positive <;>
    simpa [jordanFinite, FiniteMeasure.mass] using
      ENNReal.toNNReal_mono ENNReal.coe_ne_top (by assumption)

/-- Weak-star convergence means convergence against every continuous coordinate test. -/
def SignedWeakStarTendsto (μ : ℕ → ι → SignedMeasure Q) (ν : ι → SignedMeasure Q) : Prop :=
  ∀ i (f : C(Q, ℝ)),
    Tendsto (fun n ↦ MatrixTransport.signedPair (μ n i) f) atTop
      (𝓝 (MatrixTransport.signedPair (ν i) f))

/-- Uniformly TV-bounded finite signed-measure families have a weak-star convergent
subsequence. The signed limit is constructed from weak limits of the Jordan parts. -/
theorem signedMeasureFamily_subsequence (C : ℝ≥0) (μ : ℕ → ι → SignedMeasure Q)
    (hμ : ∀ n i, (μ n i).totalVariation univ ≤ (C : ℝ≥0∞)) :
    ∃ (ν : ι → SignedMeasure Q) (φ : ℕ → ℕ),
      StrictMono φ ∧ SignedWeakStarTendsto (fun n ↦ μ (φ n)) ν := by
  classical
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · refine ⟨fun _ ↦ 0, id, strictMono_id, ?_⟩
    intro i f
    simpa only [MatrixTransport.signedPair, integral_of_isEmpty, sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  · let parts : ℕ → (ι × Bool) → FiniteMeasure Q :=
      fun n i ↦ jordanFinite (μ n i.1) i.2
    have hb : ∀ n i, (parts n i).mass ≤ C :=
      fun n i ↦ jordanFinite_mass_le (μ n i.1) i.2 C (hμ n i.1)
    obtain ⟨p, φ, hφ, hp⟩ := finiteMeasureFamily_subsequence C parts hb
    refine ⟨fun i ↦ (p (i, true) : Measure Q).toSignedMeasure -
      (p (i, false) : Measure Q).toSignedMeasure, φ, hφ, ?_⟩
    intro i f
    rw [signedPair_difference]
    have hpos := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hp (i, true)))
      (BoundedContinuousFunction.mkOfCompact f)
    have hneg := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hp (i, false)))
      (BoundedContinuousFunction.mkOfCompact f)
    simpa only [MatrixTransport.signedPair, Function.comp_apply, parts, jordanFinite,
      Bool.false_eq_true, ↓reduceIte, FiniteMeasure.toMeasure_mk,
      BoundedContinuousFunction.mkOfCompact_apply] using hpos.sub hneg

/-- A bound on the total mass of the concrete joint RN reference implies the same
subsequence result. This is a verified bridge from the existing finite-coordinate model. -/
theorem signedMeasureFamily_subsequence_of_jointReference (C : ℝ≥0)
    (μ : ℕ → ι → SignedMeasure Q)
    (hμ : ∀ n, MatrixTransport.jointReference (μ n) univ ≤ (C : ℝ≥0∞)) :
    ∃ (ν : ι → SignedMeasure Q) (φ : ℕ → ℕ),
      StrictMono φ ∧ SignedWeakStarTendsto (fun n ↦ μ (φ n)) ν := by
  apply signedMeasureFamily_subsequence C μ
  intro n i
  exact ((MatrixTransport.totalVariation_le_jointReference (μ n) i) univ).trans (hμ n)

#print axioms finiteMeasureFamily_subsequence
#print axioms signedPair_eq_vectorIntegral
#print axioms signedPair_difference
#print axioms jordanFinite_mass_le
#print axioms signedMeasureFamily_subsequence
#print axioms signedMeasureFamily_subsequence_of_jointReference

end MatrixTransport.ReactionZero
