import MatrixTransport.ReactionZero.WeightedSet

/-!
# Relative Gram domination and recovery comparison

Scaling every coordinate of a current-weight dual test by a number in the interval (0, 1]
makes it admissible for the target weight when the current reaction Gram matrix dominates
that multiple of the target Gram matrix. The resulting inverse-factor comparison holds
for the actual extended support cost and RN integrated action, including infinite values.
No finite-action, mass-symmetry, invertibility, or compact-domain hypothesis is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialReaction

open MatrixTransport.ReactionZero

variable {n k : ℕ}

theorem gram_smul {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℝ) (α : ℝ) :
    gram (α • X) = (α * α) • gram X := by
  simp only [gram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem gram_mul_sub_smul {m p : ℕ} (C : Matrix (Fin m) (Fin p) ℝ)
    (H Hstar : Matrix (Fin p) (Fin p) ℝ) (α : ℝ) :
    gram (C * H) - α • gram (C * Hstar) =
      C * (gram H - α • gram Hstar) * C.transpose := by
  simp only [gram, Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem posSemidef_gram_mul_sub_smul {m p : ℕ} (C : Matrix (Fin m) (Fin p) ℝ)
    (H Hstar : Matrix (Fin p) (Fin p) ℝ) (α : ℝ)
    (hGram : (gram H - α • gram Hstar).PosSemidef) :
    (gram (C * H) - α • gram (C * Hstar)).PosSemidef := by
  rw [gram_mul_sub_smul]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hGram.mul_mul_conjTranspose_same C

/-- The exact PSD slack decomposition behind the scaled dual inclusion. -/
theorem slack_smul_relative (L : Matrix (Fin k) (Fin k) ℝ)
    (H Hstar : Matrix (Fin n) (Fin n) ℝ) (a : Coord n k → ℝ) (α : ℝ) :
    WeightedSet.slack L Hstar (α • a) =
      α • WeightedSet.slack L H a +
        (α * (1 - α) / 2) • gram (ReactionZero.flux a * L) +
        (α / 2) • (gram (ReactionZero.reaction a * H) -
          α • gram (ReactionZero.reaction a * Hstar)) := by
  have hm : ReactionZero.mass (α • a) = α • ReactionZero.mass a := rfl
  have hf : ReactionZero.flux (α • a) = α • ReactionZero.flux a := rfl
  have hr : ReactionZero.reaction (α • a) = α • ReactionZero.reaction a := rfl
  unfold WeightedSet.slack
  rw [hm, hf, hr]
  simp only [Matrix.smul_mul, gram_smul]
  module

/-- Relative reaction Gram domination rescales the genuine quadratic admissible set. -/
theorem smul_mem_dualSet_of_relative_gram (L : Matrix (Fin k) (Fin k) ℝ)
    (H Hstar : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hα : 0 ≤ α) (hαone : α ≤ 1)
    (hGram : (gram H - α • gram Hstar).PosSemidef)
    (a : Coord n k → ℝ) (ha : a ∈ ReactionZero.dualSet L H) :
    α • a ∈ ReactionZero.dualSet L Hstar := by
  obtain ⟨haH, haP⟩ := ha
  refine ⟨?_, ?_⟩
  · change (α • ReactionZero.mass a).IsHermitian
    exact haH.smul (by rfl : IsSelfAdjoint α)
  · change (WeightedSet.slack L Hstar (α • a)).PosSemidef
    rw [slack_smul_relative]
    have hflux : 0 ≤ α * (1 - α) / 2 :=
      div_nonneg (mul_nonneg hα (sub_nonneg.mpr hαone)) (by norm_num)
    have hreaction : 0 ≤ α / 2 := div_nonneg hα (by norm_num)
    exact ((haP.smul hα).add
      ((posSemidef_gram (ReactionZero.flux a * L)).smul hflux)).add
        ((posSemidef_gram_mul_sub_smul (ReactionZero.reaction a) H Hstar α hGram).smul hreaction)

theorem weightedPair_smul_left {ι : Type*} [Fintype ι]
    (coeff : ι → ℝ) (a v : ι → ℝ) (α : ℝ) :
    weightedPair coeff (α • a) v = α * weightedPair coeff a v := by
  unfold weightedPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The extended-valued pointwise cost comparison, without any finiteness assumption. -/
theorem cost_le_inv_mul_of_relative_gram (L : Matrix (Fin k) (Fin k) ℝ)
    (H Hstar : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hα : 0 < α) (hαone : α ≤ 1)
    (hGram : (gram H - α • gram Hstar).PosSemidef) (v : Coord n k → ℝ) :
    ReactionZero.cost L H v ≤ ENNReal.ofReal (1 / α) * ReactionZero.cost L Hstar v := by
  apply iSup₂_le
  intro a ha
  have hs := cost_fenchel L Hstar v (α • a)
    (smul_mem_dualSet_of_relative_gram L H Hstar α hα.le hαone hGram a ha)
  rw [weightedPair_smul_left, ENNReal.ofReal_mul hα.le] at hs
  have hcancel : (1 / α) * α = (1 : ℝ) := by
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hα)]
  calc
    ENNReal.ofReal (weightedPair (fun _ ↦ 1) a v) =
        (ENNReal.ofReal (1 / α) * ENNReal.ofReal α) *
          ENNReal.ofReal (weightedPair (fun _ ↦ 1) a v) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / α), hcancel]
      simp
    _ = ENNReal.ofReal (1 / α) *
        (ENNReal.ofReal α * ENNReal.ofReal (weightedPair (fun _ ↦ 1) a v)) := by
      rw [mul_assoc]
    _ ≤ ENNReal.ofReal (1 / α) * ReactionZero.cost L Hstar v :=
      mul_le_mul_right hs _

section Integrated

variable {Q : Type*} [MeasurableSpace Q]

/-- Relative Gram domination yields inverse-factor recovery for the actual signed Radon action. -/
theorem action_le_inv_mul_of_relative_gram (L : Matrix (Fin k) (Fin k) ℝ)
    (H Hstar : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hα : 0 < α) (hαone : α ≤ 1)
    (hGram : (gram H - α • gram Hstar).PosSemidef)
    (μ : Coord n k → SignedMeasure Q) :
    ReactionZero.action L H μ ≤ ENNReal.ofReal (1 / α) * ReactionZero.action L Hstar μ := by
  unfold ReactionZero.action
  calc
    (∫⁻ x, ReactionZero.cost L H (ReactionZero.density μ x) ∂jointReference μ) ≤
        ∫⁻ x, ENNReal.ofReal (1 / α) *
          ReactionZero.cost L Hstar (ReactionZero.density μ x) ∂jointReference μ :=
      lintegral_mono fun x ↦
        cost_le_inv_mul_of_relative_gram L H Hstar α hα hαone hGram (ReactionZero.density μ x)
    _ = _ := lintegral_const_mul _ (measurable_cost_density L Hstar μ)

end Integrated

#print axioms smul_mem_dualSet_of_relative_gram
#print axioms cost_le_inv_mul_of_relative_gram
#print axioms action_le_inv_mul_of_relative_gram

end MatrixTransport.PartialReaction
