import MatrixTransport.ReactionZero.WeightedSet
import MatrixTransport.ReactionZero.MatrixBounds

/-!
# Joint lower semicontinuity for the original weighted Radon action

The reaction weight may converge to any real matrix, including a singular matrix. Uniform
mass-dual shifts make every continuous test for the limiting weight admissible for the
varying weights. The conclusion concerns the actual RN action and signed-measure weak-star
convergence; no lower-semicontinuity or dual-representation conclusion is assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialReaction

open MatrixTransport.ReactionZero

variable {n k : ℕ}

/-- An explicit continuous finite-dimensional gauge; it bounds every quadratic form. -/
def entryAbsSum {m p : ℕ} (S : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j, |S i j|

theorem entryAbsSum_nonneg {m p : ℕ} (S : Matrix (Fin m) (Fin p) ℝ) :
    0 ≤ entryAbsSum S :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

@[simp] theorem entryAbsSum_zero {m p : ℕ} :
    entryAbsSum (0 : Matrix (Fin m) (Fin p) ℝ) = 0 := by
  simp [entryAbsSum]

theorem continuous_entryAbsSum {m p : ℕ} :
    Continuous (entryAbsSum : Matrix (Fin m) (Fin p) ℝ → ℝ) := by
  unfold entryAbsSum
  exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
    ((continuous_apply j).comp (continuous_apply i)).abs

theorem abs_mul_le_sum_sq (u : Fin n → ℝ) (p q : Fin n) :
    |u p * u q| ≤ ∑ i, u i ^ 2 := by
  have hp : u p ^ 2 ≤ ∑ i, u i ^ 2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg (u i)) (Finset.mem_univ p)
  have hq : u q ^ 2 ≤ ∑ i, u i ^ 2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg (u i)) (Finset.mem_univ q)
  rw [abs_mul]
  nlinarith [sq_nonneg (|u p| - |u q|), sq_abs (u p), sq_abs (u q)]

theorem quadraticForm_le_entryAbsSum (S : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ (S *ᵥ u) ≤ entryAbsSum S * ∑ i, u i ^ 2 := by
  calc u ⬝ᵥ (S *ᵥ u) = ∑ p, ∑ q, u p * S p q * u q := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ p, ∑ q, |S p q| * ∑ i, u i ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      calc u p * S p q * u q ≤ |u p * S p q * u q| := le_abs_self _
        _ = |S p q| * |u p * u q| := by rw [abs_mul, abs_mul, abs_mul]; ring
        _ ≤ |S p q| * ∑ i, u i ^ 2 :=
          mul_le_mul_of_nonneg_left (abs_mul_le_sum_sq u p q) (abs_nonneg _)
    _ = entryAbsSum S * ∑ i, u i ^ 2 := by
      simp only [entryAbsSum, Finset.sum_mul]

theorem posSemidef_entryAbsSum_sub (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.IsHermitian) :
    (entryAbsSum S • (1 : Matrix (Fin n) (Fin n) ℝ) - S).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact ((Matrix.isHermitian_one).smul (by rfl : IsSelfAdjoint (entryAbsSum S))).sub hS
  · intro u
    have h := quadraticForm_le_entryAbsSum S u
    have he : u ⬝ᵥ ((entryAbsSum S • (1 : Matrix (Fin n) (Fin n) ℝ) - S) *ᵥ u) =
        entryAbsSum S * (∑ i, u i ^ 2) - u ⬝ᵥ (S *ᵥ u) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul]
      simp only [dotProduct, pow_two, smul_eq_mul]
    simpa only [star_trivial, he] using sub_nonneg.mpr h

/-- Uniform matrix domination without inverses or spectral decomposition. -/
theorem posSemidef_uniform_congruence_defect (S C : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.IsHermitian) (M : ℝ) (hM : frobeniusSq C ≤ M) :
    ((entryAbsSum S * M) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      C * S * C.transpose).PosSemidef := by
  have hs := (posSemidef_entryAbsSum_sub S hS).mul_mul_conjTranspose_same C
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hs
  have hg := (posSemidef_frobeniusSq_sub_gram C).smul (entryAbsSum_nonneg S)
  have hplus := hs.add hg
  have he : (C * (entryAbsSum S • (1 : Matrix (Fin n) (Fin n) ℝ) - S) * C.transpose) +
      entryAbsSum S • (frobeniusSq C • (1 : Matrix (Fin n) (Fin n) ℝ) - gram C) =
      (entryAbsSum S * frobeniusSq C) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        C * S * C.transpose := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, gram, smul_sub, smul_smul]
    module
  rw [he] at hplus
  have hnonneg : 0 ≤ entryAbsSum S * (M - frobeniusSq C) :=
    mul_nonneg (entryAbsSum_nonneg S) (sub_nonneg.mpr hM)
  have hpad := (Matrix.PosSemidef.one :
    (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef).smul hnonneg
  have := hplus.add hpad
  convert this using 1
  module

/-- Subtracting a scalar identity only in the dual mass coordinate. -/
def massShift (δ : ℝ) (a : Coord n k → ℝ) : Coord n k → ℝ :=
  a - δ • pack (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin k) ℝ) 0

@[simp] theorem mass_massShift (δ : ℝ) (a : Coord n k → ℝ) :
    ReactionZero.mass (massShift δ a) =
      ReactionZero.mass a - δ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  rfl

@[simp] theorem flux_massShift (δ : ℝ) (a : Coord n k → ℝ) :
    ReactionZero.flux (massShift δ a) = ReactionZero.flux a := by
  ext i j
  simp [massShift, ReactionZero.flux, pack]

@[simp] theorem reaction_massShift (δ : ℝ) (a : Coord n k → ℝ) :
    ReactionZero.reaction (massShift δ a) = ReactionZero.reaction a := by
  ext i j
  simp [massShift, ReactionZero.reaction, pack]

/-- Every limiting dual test becomes admissible after an explicit, vanishing mass shift. -/
theorem massShift_mem_dualSet (L : Matrix (Fin k) (Fin k) ℝ)
    (H Hstar : Matrix (Fin n) (Fin n) ℝ) (a : Coord n k → ℝ)
    (ha : a ∈ ReactionZero.dualSet L Hstar) (M : ℝ)
    (hM : frobeniusSq (ReactionZero.reaction a) ≤ M) :
    massShift (entryAbsSum (gram H - gram Hstar) * M / 2) a ∈
      ReactionZero.dualSet L H := by
  have hS : (gram H - gram Hstar).IsHermitian :=
    (posSemidef_gram H).isHermitian.sub (posSemidef_gram Hstar).isHermitian
  have hd := (posSemidef_uniform_congruence_defect (gram H - gram Hstar)
    (ReactionZero.reaction a) hS M hM).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have heq : ReactionZero.reaction a * (gram H - gram Hstar) *
      (ReactionZero.reaction a).transpose =
      gram (ReactionZero.reaction a * H) - gram (ReactionZero.reaction a * Hstar) :=
    (gram_mul_sub (ReactionZero.reaction a) H Hstar).symm
  rw [heq] at hd
  obtain ⟨hA, hP⟩ := ha
  refine ⟨?_, ?_⟩
  · rw [mass_massShift]
    exact hA.sub ((Matrix.isHermitian_one).smul
      (by rfl : IsSelfAdjoint (entryAbsSum (gram H - gram Hstar) * M / 2)))
  · rw [mass_massShift, flux_massShift, reaction_massShift]
    have hp := hP.add hd
    convert hp using 1
    module

section ContinuousFields

variable {Q : Type*} [TopologicalSpace Q]

/-- The mass shift preserves continuity of the entire finite coordinate field. -/
def massShiftField (δ : ℝ) (a : C(Q, Coord n k → ℝ)) : C(Q, Coord n k → ℝ) :=
  a - ContinuousMap.const Q
    (δ • pack (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin k) ℝ) 0)

@[simp] theorem massShiftField_apply (δ : ℝ) (a : C(Q, Coord n k → ℝ)) (x : Q) :
    massShiftField δ a x = massShift δ (a x) := rfl

variable [CompactSpace Q]

theorem continuousField_reaction_bounded (a : C(Q, Coord n k → ℝ)) :
    ∃ M : ℝ, ∀ x, frobeniusSq (ReactionZero.reaction (a x)) ≤ M := by
  let f : C(Q, ℝ) := ⟨fun x ↦ frobeniusSq (ReactionZero.reaction (a x)),
    continuous_frobeniusSq.comp (WeightedSet.continuous_reaction.comp a.continuous)⟩
  refine ⟨‖f‖, fun x ↦ ?_⟩
  exact (le_abs_self (f x)).trans (by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)

end ContinuousFields

section MeasurePairing

variable {Q : Type*} [MeasurableSpace Q] [MetricSpace Q] [CompactSpace Q] [BorelSpace Q]

theorem signedPair_sub_continuous (s : SignedMeasure Q) (f g : C(Q, ℝ)) :
    signedPair s (f - g) = signedPair s f - signedPair s g := by
  unfold signedPair
  change (∫ x, f x - g x ∂s.toJordanDecomposition.posPart) -
      (∫ x, f x - g x ∂s.toJordanDecomposition.negPart) = _
  rw [integral_sub (continuousTest_integrable f s.toJordanDecomposition.posPart)
      (continuousTest_integrable g s.toJordanDecomposition.posPart),
    integral_sub (continuousTest_integrable f s.toJordanDecomposition.negPart)
      (continuousTest_integrable g s.toJordanDecomposition.negPart)]
  ring

omit [CompactSpace Q] [BorelSpace Q] in
theorem signedPair_smul_continuous (s : SignedMeasure Q) (δ : ℝ) (f : C(Q, ℝ)) :
    signedPair s (δ • f) = δ * signedPair s f := by
  unfold signedPair
  change (∫ x, δ * f x ∂s.toJordanDecomposition.posPart) -
      (∫ x, δ * f x ∂s.toJordanDecomposition.negPart) = _
  rw [integral_const_mul, integral_const_mul]
  ring

theorem coordinatePair_sub_smul {ι : Type*} [Fintype ι]
    (μ : ι → SignedMeasure Q) (a b : C(Q, ι → ℝ)) (δ : ℝ) :
    Duality.coordinatePair (fun _ ↦ 1) μ (a - δ • b) =
      Duality.coordinatePair (fun _ ↦ 1) μ a -
        δ * Duality.coordinatePair (fun _ ↦ 1) μ b := by
  have ht : ∀ i : ι, signedPair (μ i) (fun x ↦ (a - δ • b) x i) =
      signedPair (μ i) (fun x ↦ a x i) - δ * signedPair (μ i) (fun x ↦ b x i) := by
    intro i
    calc signedPair (μ i) (fun x ↦ (a - δ • b) x i) =
        signedPair (μ i) (Duality.coordinateTest a i) -
          signedPair (μ i) (δ • Duality.coordinateTest b i) :=
        signedPair_sub_continuous (μ i) (Duality.coordinateTest a i)
          (δ • Duality.coordinateTest b i)
      _ = _ := by
        rw [signedPair_smul_continuous]
        rfl
  unfold Duality.coordinatePair
  simp only [one_mul]
  change (∑ i, signedPair (μ i) (fun x ↦ (a - δ • b) x i)) =
    (∑ i, signedPair (μ i) (fun x ↦ a x i)) -
      δ * ∑ i, signedPair (μ i) (fun x ↦ b x i)
  calc _ = ∑ i, (signedPair (μ i) (fun x ↦ a x i) -
      δ * signedPair (μ i) (fun x ↦ b x i)) :=
        Finset.sum_congr rfl fun i _ ↦ ht i
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- The identity field is supported exactly on diagonal dual mass coordinates. -/
def massIdentityField : C(Q, Coord n k → ℝ) :=
  ContinuousMap.const Q (pack (1 : Matrix (Fin n) (Fin n) ℝ)
    (0 : Matrix (Fin n) (Fin k) ℝ) 0)

theorem coordinatePair_massShiftField (μ : Coord n k → SignedMeasure Q)
    (a : C(Q, Coord n k → ℝ)) (δ : ℝ) :
    Duality.coordinatePair (fun _ ↦ 1) μ (massShiftField δ a) =
      Duality.coordinatePair (fun _ ↦ 1) μ a -
        δ * Duality.coordinatePair (fun _ ↦ 1) μ (massIdentityField (Q := Q)) := by
  have he : massShiftField δ a = a - δ • (massIdentityField (Q := Q)) := by
    ext x c
    rfl
  rw [he]
  exact coordinatePair_sub_smul μ a massIdentityField δ

omit [CompactSpace Q] [BorelSpace Q] in
theorem coordinatePair_tendsto {ι : Type*} [Fintype ι]
    (μ : ℕ → ι → SignedMeasure Q) (ν : ι → SignedMeasure Q)
    (hμ : SignedWeakStarTendsto μ ν) (a : C(Q, ι → ℝ)) :
    Tendsto (fun j ↦ Duality.coordinatePair (fun _ ↦ 1) (μ j) a) atTop
      (𝓝 (Duality.coordinatePair (fun _ ↦ 1) ν a)) := by
  simp only [Duality.coordinatePair, one_mul]
  exact tendsto_finsetSum _ fun i _ ↦ hμ i (Duality.coordinateTest a i)

end MeasurePairing

section JointLimit

variable {Q : Type*} [MeasurableSpace Q] [MetricSpace Q] [CompactSpace Q] [BorelSpace Q]

/-- Joint lower semicontinuity of the actual RN weighted action under matrix convergence
and true coordinate signed-measure weak-star convergence. The weights and limiting weight
may be singular, and no Loewner ordering is required for this lower bound.
-/
theorem action_le_varying_weight_liminf (L : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (μ : ℕ → Coord n k → SignedMeasure Q) (ν : Coord n k → SignedMeasure Q)
    (hμ : SignedWeakStarTendsto μ ν) :
    ReactionZero.action L Hstar ν ≤
      atTop.liminf (fun j ↦ ReactionZero.action L (H j) (μ j)) := by
  rw [WeightedSet.action_eq_continuousDual]
  unfold Duality.continuousDual
  refine iSup_le fun a ↦ iSup_le fun ha ↦ ?_
  obtain ⟨M, hM⟩ := continuousField_reaction_bounded a
  let δ : ℕ → ℝ := fun j ↦ entryAbsSum (gram (H j) - gram Hstar) * M / 2
  have hg : Tendsto (fun j ↦ gram (H j) - gram Hstar) atTop
      (𝓝 (0 : Matrix (Fin n) (Fin n) ℝ)) := by
    have hc : Tendsto (fun _ : ℕ ↦ gram Hstar) atTop (𝓝 (gram Hstar)) :=
      tendsto_const_nhds
    simpa only [Function.comp_def, sub_self] using
      ((WeightedSet.continuous_gram.tendsto Hstar).comp hH).sub hc
  have hb : Tendsto (fun j ↦ entryAbsSum (gram (H j) - gram Hstar)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, entryAbsSum_zero] using
      (continuous_entryAbsSum.tendsto 0).comp hg
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, zero_mul, zero_div] using (hb.mul_const M).div_const (2 : ℝ)
  have hpair : Tendsto
      (fun j ↦ Duality.coordinatePair (fun _ ↦ 1) (μ j) (massShiftField (δ j) a)) atTop
      (𝓝 (Duality.coordinatePair (fun _ ↦ 1) ν a)) := by
    have ht := (coordinatePair_tendsto μ ν hμ a).sub
      (hδ.mul (coordinatePair_tendsto μ ν hμ (massIdentityField (Q := Q))))
    simpa only [coordinatePair_massShiftField, zero_mul, sub_zero] using ht
  have ht : Tendsto
      (fun j ↦ ENNReal.ofReal
        (Duality.coordinatePair (fun _ ↦ 1) (μ j) (massShiftField (δ j) a))) atTop
      (𝓝 (ENNReal.ofReal (Duality.coordinatePair (fun _ ↦ 1) ν a))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpair
  have hbound : ∀ j, ENNReal.ofReal
      (Duality.coordinatePair (fun _ ↦ 1) (μ j) (massShiftField (δ j) a)) ≤
        ReactionZero.action L (H j) (μ j) := by
    intro j
    have hadm : ∀ x, massShiftField (δ j) a x ∈ ReactionZero.dualSet L (H j) := by
      intro x
      exact massShift_mem_dualSet L (H j) Hstar (a x) (ha x) M (hM x)
    rw [WeightedSet.action_eq_continuousDual]
    exact le_iSup₂ (f := fun (b : C(Q, Coord n k → ℝ))
      (_ : ∀ x, b x ∈ ReactionZero.dualSet L (H j)) ↦
        ENNReal.ofReal (Duality.coordinatePair (fun _ ↦ 1) (μ j) b))
      (massShiftField (δ j) a) hadm
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Filter.Eventually.of_forall hbound)

end JointLimit

#print axioms posSemidef_uniform_congruence_defect
#print axioms massShift_mem_dualSet
#print axioms coordinatePair_massShiftField
#print axioms action_le_varying_weight_liminf

end MatrixTransport.PartialReaction
