import MatrixTransport.PartialReaction.WeightScaling

/-!
# Relative Gram comparison when both matrix weights vary

Transport and reaction weights have independent dimensions. Two genuine PSD Gram deficits
rescale every current dual test into a target dual test, giving inverse-factor comparison
for the actual extended support cost and RN action. The scaling factor need only be positive;
no upper bound, density invertibility, finite-action, or compactness premise is required.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialWeights

open MatrixTransport.ReactionZero

variable {n k : ℕ}

/-- The exact two-deficit slack identity; the flux and reaction sizes need not agree. -/
theorem slack_smul_relative_two_weights
    (L Lstar : Matrix (Fin k) (Fin k) ℝ)
    (H Hstar : Matrix (Fin n) (Fin n) ℝ)
    (a : Coord n k → ℝ) (α : ℝ) :
    WeightedSet.slack Lstar Hstar (α • a) =
      α • WeightedSet.slack L H a +
        (α / 2) • (gram (ReactionZero.flux a * L) -
          α • gram (ReactionZero.flux a * Lstar)) +
        (α / 2) • (gram (ReactionZero.reaction a * H) -
          α • gram (ReactionZero.reaction a * Hstar)) := by
  have hm : ReactionZero.mass (α • a) = α • ReactionZero.mass a := rfl
  have hf : ReactionZero.flux (α • a) = α • ReactionZero.flux a := rfl
  have hr : ReactionZero.reaction (α • a) = α • ReactionZero.reaction a := rfl
  unfold WeightedSet.slack
  rw [hm, hf, hr]
  simp only [Matrix.smul_mul, PartialReaction.gram_smul]
  module

/-- Relative domination in both Gram matrices gives a genuine scaled dual inclusion. -/
theorem smul_mem_dualSet_of_relative_grams
    (L Lstar : Matrix (Fin k) (Fin k) ℝ)
    (H Hstar : Matrix (Fin n) (Fin n) ℝ)
    (α : ℝ) (hα : 0 ≤ α)
    (hL : (gram L - α • gram Lstar).PosSemidef)
    (hH : (gram H - α • gram Hstar).PosSemidef)
    (a : Coord n k → ℝ) (ha : a ∈ ReactionZero.dualSet L H) :
    α • a ∈ ReactionZero.dualSet Lstar Hstar := by
  obtain ⟨haH, haP⟩ := ha
  refine ⟨?_, ?_⟩
  · change (α • ReactionZero.mass a).IsHermitian
    exact haH.smul (by rfl : IsSelfAdjoint α)
  · change (WeightedSet.slack Lstar Hstar (α • a)).PosSemidef
    rw [slack_smul_relative_two_weights]
    have hhalf : 0 ≤ α / 2 := div_nonneg hα (by norm_num)
    exact ((haP.smul hα).add
      ((PartialReaction.posSemidef_gram_mul_sub_smul
        (ReactionZero.flux a) L Lstar α hL).smul hhalf)).add
      ((PartialReaction.posSemidef_gram_mul_sub_smul
        (ReactionZero.reaction a) H Hstar α hH).smul hhalf)

/-- The comparison for the actual extended support costs, including infinite values. -/
theorem cost_le_inv_mul_of_relative_grams
    (L Lstar : Matrix (Fin k) (Fin k) ℝ)
    (H Hstar : Matrix (Fin n) (Fin n) ℝ)
    (α : ℝ) (hα : 0 < α)
    (hL : (gram L - α • gram Lstar).PosSemidef)
    (hH : (gram H - α • gram Hstar).PosSemidef)
    (v : Coord n k → ℝ) :
    ReactionZero.cost L H v ≤
      ENNReal.ofReal (1 / α) * ReactionZero.cost Lstar Hstar v := by
  apply iSup₂_le
  intro a ha
  have hs := cost_fenchel Lstar Hstar v (α • a)
    (smul_mem_dualSet_of_relative_grams L Lstar H Hstar α hα.le hL hH a ha)
  rw [PartialReaction.weightedPair_smul_left, ENNReal.ofReal_mul hα.le] at hs
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
    _ ≤ ENNReal.ofReal (1 / α) * ReactionZero.cost Lstar Hstar v :=
      mul_le_mul_right hs _

section Integrated

variable {Q : Type*} [MeasurableSpace Q]

/-- Relative comparison for actual finite signed-coordinate Radon actions in all dimensions. -/
theorem action_le_inv_mul_of_relative_grams
    (L Lstar : Matrix (Fin k) (Fin k) ℝ)
    (H Hstar : Matrix (Fin n) (Fin n) ℝ)
    (α : ℝ) (hα : 0 < α)
    (hL : (gram L - α • gram Lstar).PosSemidef)
    (hH : (gram H - α • gram Hstar).PosSemidef)
    (μ : Coord n k → SignedMeasure Q) :
    ReactionZero.action L H μ ≤
      ENNReal.ofReal (1 / α) * ReactionZero.action Lstar Hstar μ := by
  unfold ReactionZero.action
  calc
    (∫⁻ x, ReactionZero.cost L H (ReactionZero.density μ x) ∂jointReference μ) ≤
        ∫⁻ x, ENNReal.ofReal (1 / α) *
          ReactionZero.cost Lstar Hstar (ReactionZero.density μ x) ∂jointReference μ :=
      lintegral_mono fun x ↦
        cost_le_inv_mul_of_relative_grams L Lstar H Hstar α hα hL hH
          (ReactionZero.density μ x)
    _ = _ := lintegral_const_mul _ (measurable_cost_density Lstar Hstar μ)

end Integrated

#print axioms slack_smul_relative_two_weights
#print axioms smul_mem_dualSet_of_relative_grams
#print axioms cost_le_inv_mul_of_relative_grams
#print axioms action_le_inv_mul_of_relative_grams

end MatrixTransport.PartialWeights
