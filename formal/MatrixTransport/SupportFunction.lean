import Mathlib

/-!
# Finite-coordinate support functions

This module proves elementary properties of an arbitrary support supremum with a weighted
finite-coordinate pairing. The concrete matrix dual set and the measure transport distance
must still be constructed separately; none of their analytic bounds are assumed here.
-/

set_option autoImplicit false

open scoped ENNReal

namespace MatrixTransport

variable {ι : Type*} [Fintype ι]

noncomputable def weightedPair (coeff : ι → ℝ) (a v : ι → ℝ) : ℝ :=
  ∑ i, coeff i * a i * v i

noncomputable def supportFunction (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (v : ι → ℝ) : ℝ≥0∞ :=
  ⨆ (a : ι → ℝ) (_ : a ∈ S), ENNReal.ofReal (weightedPair coeff a v)

theorem supportFunction_zero (coeff : ι → ℝ) (S : Set (ι → ℝ)) :
    supportFunction coeff S (0 : ι → ℝ) = 0 := by
  refine le_antisymm ?_ zero_le
  refine iSup_le fun a => iSup_le fun _ => ?_
  simp [weightedPair]

theorem supportFunction_fenchel (coeff : ι → ℝ) (S : Set (ι → ℝ)) (v a : ι → ℝ)
    (ha : a ∈ S) :
    ENNReal.ofReal (weightedPair coeff a v) ≤ supportFunction coeff S v :=
  le_iSup₂ (f := fun (a : ι → ℝ) (_ : a ∈ S) => ENNReal.ofReal (weightedPair coeff a v)) a ha

theorem weightedPair_smul_right (coeff : ι → ℝ) (a v : ι → ℝ) (t : ℝ) :
    weightedPair coeff a (t • v) = t * weightedPair coeff a v := by
  unfold weightedPair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem supportFunction_smul_nonneg (coeff : ι → ℝ) (S : Set (ι → ℝ)) (v : ι → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    supportFunction coeff S (t • v) = ENNReal.ofReal t * supportFunction coeff S v := by
  simp only [supportFunction, ENNReal.mul_iSup, weightedPair_smul_right,
    ENNReal.ofReal_mul ht]

theorem continuous_weightedPair_right (coeff : ι → ℝ) (a : ι → ℝ) :
    Continuous (fun v : ι → ℝ => weightedPair coeff a v) := by
  unfold weightedPair
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

theorem lowerSemicontinuous_supportFunction (coeff : ι → ℝ) (S : Set (ι → ℝ)) :
    LowerSemicontinuous (supportFunction coeff S) := by
  unfold supportFunction
  refine lowerSemicontinuous_iSup fun a => ?_
  exact lowerSemicontinuous_iSup fun _ =>
    (ENNReal.continuous_ofReal.comp (continuous_weightedPair_right coeff a)).lowerSemicontinuous

theorem measurable_supportFunction (coeff : ι → ℝ) (S : Set (ι → ℝ)) :
    Measurable (supportFunction coeff S) :=
  (lowerSemicontinuous_supportFunction coeff S).measurable

#print axioms supportFunction_smul_nonneg
#print axioms measurable_supportFunction

end MatrixTransport
