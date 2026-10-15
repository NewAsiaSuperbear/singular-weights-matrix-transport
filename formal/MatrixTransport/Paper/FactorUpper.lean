import MatrixTransport.ReactionZero.LimitTheorem

set_option autoImplicit false

noncomputable section

open scoped ENNReal Matrix BigOperators

namespace LiZouTransport.Factor

open MatrixTransport.ReactionZero

variable {m p : ℕ}

theorem frob_comm (A B : Matrix (Fin m) (Fin p) ℝ) : frob A B = frob B A := by
  unfold frob
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem frob_self (A : Matrix (Fin m) (Fin p) ℝ) : frob A A = frobeniusSq A := by
  simp only [frob, frobeniusSq, pow_two]

theorem frob_sub_right (A B C : Matrix (Fin m) (Fin p) ℝ) :
    frob A (B - C) = frob A B - frob A C := by
  simp [frob, mul_sub, Finset.sum_sub_distrib]

theorem frobeniusSq_sub_two (A B : Matrix (Fin m) (Fin p) ℝ) :
    frobeniusSq (A - (2 : ℝ) • B) = frobeniusSq A - 4 * frob A B + 4 * frobeniusSq B := by
  have hentry : ∀ i j, (A i j - 2 * B i j)^2 = A i j ^ 2 - 4 * (A i j * B i j) +
      4 * B i j ^ 2 := by intro i j; ring
  simp only [frobeniusSq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hentry,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [frob, Finset.mul_sum]

theorem completion_bound (A B : Matrix (Fin m) (Fin p) ℝ) :
    -(1 / 2 : ℝ) * frobeniusSq A + 2 * frob A B ≤ 2 * frobeniusSq B := by
  have h := frobeniusSq_nonneg (A - (2 : ℝ) • B)
  rw [frobeniusSq_sub_two] at h
  linarith

variable {n k : ℕ}

theorem frob_gram_gram (P : Matrix (Fin n) (Fin p) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    frob (gram P) (gram C) = frobeniusSq (C.transpose * P) := by
  rw [frob_gram_eq_trace, ← frob_self, frob_eq_trace]
  simp [gram, Matrix.transpose_mul, Matrix.mul_assoc]

theorem frob_factor_reaction (C H : Matrix (Fin n) (Fin n) ℝ)
    (P Δ : Matrix (Fin n) (Fin p) ℝ) :
    frob C ((2 : ℝ) • ((H * P) * Δ.transpose * H.transpose)) =
      2 * frob ((C * H).transpose * (H * P)) Δ := by
  rw [frob_smul_right, frob_eq_trace, frob_comm _ Δ, frob_eq_trace]
  congr 1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    (C.transpose * (H * P * Δ.transpose * H.transpose)).trace =
        ((C.transpose * (H * P) * Δ.transpose) * H.transpose).trace := by
          simp only [Matrix.mul_assoc]
    _ = (H.transpose * (C.transpose * (H * P) * Δ.transpose)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (Δ.transpose * (H.transpose * C.transpose * (H * P))).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]

/-- The original local support cost of a matrix-factor reaction is bounded without inverses. -/
theorem cost_factor_reaction_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (P Δ : Matrix (Fin n) (Fin p) ℝ) :
    MatrixTransport.ReactionZero.cost L H (pack (gram (H * P)) 0
      ((2 : ℝ) • ((H * P) * Δ.transpose * H.transpose))) ≤ ENNReal.ofReal (2 * frobeniusSq Δ) := by
  apply iSup₂_le
  intro a ha
  apply ENNReal.ofReal_le_ofReal
  rw [weightedPair_pack]
  have hslack := frob_gram_nonneg ha.2 (H * P)
  have hflux := frob_gram_nonneg (posSemidef_gram (flux a * L)) (H * P)
  rw [frob_sub_right, frob_sub_right, frob_smul_right, frob_smul_right] at hslack
  have hneg : frob (gram (H * P)) (-mass a) = -frob (gram (H * P)) (mass a) := by
    rw [frob_comm, frob_neg_left, frob_comm]
  rw [hneg, frob_gram_gram] at hslack
  have hmass : frob (mass a) (gram (H * P)) ≤
      -(1 / 2 : ℝ) * frobeniusSq ((reaction a * H).transpose * (H * P)) := by
    rw [frob_comm]
    linarith
  rw [frob_factor_reaction]
  have hzero : frob (flux a) (0 : Matrix (Fin n) (Fin k) ℝ) = 0 := by simp [frob]
  rw [hzero, add_zero]
  exact (add_le_add_left hmass _).trans (completion_bound _ Δ)

#print axioms cost_factor_reaction_le

end LiZouTransport.Factor
