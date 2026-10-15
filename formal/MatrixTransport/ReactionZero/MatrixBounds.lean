import MatrixTransport.ReactionZero.WeightedAction

/-!
# Frobenius bounds for arbitrary reaction weights

The squared Frobenius bound is defined explicitly by a finite sum, so no ambient matrix
norm instance can silently change its meaning. The Loewner estimate applies to arbitrary
real matrices, hence also to every symmetric positive definite reaction weight in the paper.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace MatrixTransport.ReactionZero

variable {n p : ℕ}

def frobeniusSq (A : Matrix (Fin n) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

theorem frobeniusSq_nonneg (A : Matrix (Fin n) (Fin p) ℝ) : 0 ≤ frobeniusSq A := by
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (A i j)

theorem transpose_mulVec_sq_le (A : Matrix (Fin n) (Fin p) ℝ) (x : Fin n → ℝ) :
    (∑ j, (A.transpose *ᵥ x) j ^ 2) ≤ frobeniusSq A * ∑ i, x i ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ A i j) x
  rw [← Finset.sum_mul] at h
  have hid : (∑ j, ∑ i, A i j ^ 2) = frobeniusSq A := by
    unfold frobeniusSq
    rw [Finset.sum_comm]
  rw [hid] at h
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using h

theorem dotProduct_gram (A : Matrix (Fin n) (Fin p) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (gram A *ᵥ x) = ∑ j, (A.transpose *ᵥ x) j ^ 2 := by
  rw [gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose]
  simp only [dotProduct, pow_two]

/-- The explicit squared Frobenius coefficient dominates the Gram matrix in Loewner order. -/
theorem posSemidef_frobeniusSq_sub_gram (A : Matrix (Fin n) (Fin p) ℝ) :
    (frobeniusSq A • (1 : Matrix (Fin n) (Fin n) ℝ) - gram A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact ((Matrix.isHermitian_one).smul (by rfl : IsSelfAdjoint (frobeniusSq A))).sub
      (posSemidef_gram A).isHermitian
  · intro x
    have hb := transpose_mulVec_sq_le A x
    have hid : x ⬝ᵥ ((frobeniusSq A • (1 : Matrix (Fin n) (Fin n) ℝ) - gram A) *ᵥ x) =
        frobeniusSq A * (∑ i, x i ^ 2) - ∑ j, (A.transpose *ᵥ x) j ^ 2 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul, dotProduct_gram]
      simp only [dotProduct, pow_two, smul_eq_mul]
    simpa only [star_trivial, hid] using sub_nonneg.mpr hb

/-- The squared Frobenius coefficient is continuous in all matrix entries. -/
theorem continuous_frobeniusSq :
    Continuous (frobeniusSq : Matrix (Fin n) (Fin p) ℝ → ℝ) := by
  unfold frobeniusSq
  exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
    ((continuous_apply j).comp (continuous_apply i)).pow 2

#print axioms posSemidef_frobeniusSq_sub_gram

end MatrixTransport.ReactionZero
