import MatrixTransport.ReactionZero.LocalEstimates
import MatrixTransport.ReactionZero.Coercivity
import MatrixTransport.ReactionZero.MatrixBounds

/-!
# Pointwise bounds for reaction and flux coordinates

Real finite-dimensional estimates with arbitrary `n k : ℕ` and arbitrary real weights.
No inverse or invertibility hypothesis is used. Finite cost is always an explicit hypothesis;
a Hermitian mass is assumed only where the trace bound needs positive semidefiniteness.
-/

set_option autoImplicit false

open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.ReactionZero

noncomputable section

variable {n k : ℕ}

/-! ### General quadratic bounds from Fenchel -/

theorem reaction_pairing_sq_le (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (v : Coord n k → ℝ) (hfin : cost L1 L2 v ≠ ⊤) (W : Matrix (Fin n) (Fin n) ℝ) :
    frob W (reaction v) ^ 2 ≤ 2 * (cost L1 L2 v).toReal * frob (gram (W * L2)) (mass v) :=
  quadratic_dual_bound (reaction_coefficient_nonneg L1 L2 v hfin W) ENNReal.toReal_nonneg
    (fun s ↦ reaction_fenchel_le_toReal L1 L2 v hfin s W)

theorem flux_pairing_sq_le (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (v : Coord n k → ℝ) (hfin : cost L1 L2 v ≠ ⊤) (W : Matrix (Fin n) (Fin k) ℝ) :
    frob W (flux v) ^ 2 ≤ 2 * (cost L1 L2 v).toReal * frob (gram (W * L1)) (mass v) :=
  quadratic_dual_bound (flux_coefficient_nonneg L1 L2 v hfin W) ENNReal.toReal_nonneg
    (fun s ↦ flux_fenchel_le_toReal L1 L2 v hfin s W)


/-! ### Single-entry test matrices -/

theorem frob_single_left {m p : ℕ} (i : Fin m) (j : Fin p) (R : Matrix (Fin m) (Fin p) ℝ) :
    frob (Matrix.single i j (1 : ℝ)) R = R i j := by
  unfold frob
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [Ne.symm ha]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem frob_gram_single_mul {m q p : ℕ} (i : Fin m) (j : Fin q)
    (L : Matrix (Fin q) (Fin p) ℝ) (G : Matrix (Fin m) (Fin m) ℝ) :
    frob (gram (Matrix.single i j (1 : ℝ) * L)) G = G i i * ∑ b, L j b ^ 2 := by
  have hX : ∀ a b, (Matrix.single i j (1 : ℝ) * L) a b = if a = i then L j b else 0 := by
    intro a b
    by_cases h : a = i
    · rw [ite_eq_left h, h]
      simp
    · rw [ite_eq_right h]
      simp [h]
  have key : ∀ (X : Matrix (Fin m) (Fin p) ℝ) (a c : Fin m),
      gram X a c = ∑ b, X a b * X c b := by
    intro X a c
    simp [gram, Matrix.mul_apply]
  have hg : ∀ a c, gram (Matrix.single i j (1 : ℝ) * L) a c =
      if a = i ∧ c = i then ∑ b, L j b ^ 2 else 0 := by
    intro a c
    rw [key]
    simp only [hX]
    by_cases ha : a = i <;> by_cases hc : c = i <;> simp [ha, hc, pow_two]
  unfold frob
  simp only [hg]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · rw [ite_eq_left ⟨rfl, rfl⟩]
      ring
    · intro c _ hc
      simp [hc]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro c _
    simp [ha]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### Entrywise reaction and flux bounds -/

theorem reaction_entry_sq_le (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (v : Coord n k → ℝ) (hfin : cost L1 L2 v ≠ ⊤) (i j : Fin n) :
    reaction v i j ^ 2 ≤
      2 * (cost L1 L2 v).toReal * (mass v i i * ∑ a, L2 j a ^ 2) := by
  have h := reaction_pairing_sq_le L1 L2 v hfin (Matrix.single i j (1 : ℝ))
  rw [frob_single_left, frob_gram_single_mul] at h
  exact h

theorem flux_entry_sq_le (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (v : Coord n k → ℝ) (hfin : cost L1 L2 v ≠ ⊤) (i : Fin n) (j : Fin k) :
    flux v i j ^ 2 ≤
      2 * (cost L1 L2 v).toReal * (mass v i i * ∑ a, L1 j a ^ 2) := by
  have h := flux_pairing_sq_le L1 L2 v hfin (Matrix.single i j (1 : ℝ))
  rw [frob_single_left, frob_gram_single_mul] at h
  exact h

/-! ### Positive semidefinite diagonal and trace bounds -/

theorem dotProduct_mulVec_nonneg_of_posSemidef {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosSemidef) (x : Fin n → ℝ) : 0 ≤ dotProduct x (G.mulVec x) := by
  have h := frob_gram_nonneg hG (Matrix.of fun a (_ : Fin 1) ↦ x a)
  have hg : gram (Matrix.of fun a (_ : Fin 1) ↦ x a) = Matrix.vecMulVec x x := by
    ext a c
    simp [gram, Matrix.mul_apply, Matrix.vecMulVec_apply]
  rwa [hg, frob_vecMulVec_self] at h

theorem diag_le_trace {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef) (i : Fin n) :
    G i i ≤ G.trace :=
  Finset.single_le_sum (f := fun a ↦ G a a) (fun _ _ ↦ hG.diag_nonneg) (Finset.mem_univ i)

theorem trace_nonneg_of_posSemidef {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef) :
    0 ≤ G.trace :=
  Finset.sum_nonneg fun _ _ ↦ hG.diag_nonneg

def twoPoint (i j : Fin n) (c : ℝ) : Fin n → ℝ :=
  fun a ↦ (if a = i then (1 : ℝ) else 0) + c * (if a = j then (1 : ℝ) else 0)

theorem dotProduct_twoPoint (G : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (c : ℝ) :
    dotProduct (twoPoint i j c) (G.mulVec (twoPoint i j c)) =
      G i i + c * (G i j + G j i) + c ^ 2 * G j j := by
  have hin : ∀ a, G.mulVec (twoPoint i j c) a = G a i + c * G a j := by
    intro a
    simp only [Matrix.mulVec, dotProduct, twoPoint, mul_add, Finset.sum_add_distrib]
    simp
    try ring
  simp only [dotProduct, hin]
  simp only [twoPoint, add_mul, mul_add, Finset.sum_add_distrib]
  simp
  try ring

theorem abs_apply_le_trace_of_posSemidef {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef)
    (i j : Fin n) : |G i j| ≤ G.trace := by
  have hT : G.transpose = G := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.eq
  have hs : G j i = G i j := by
    have h := congrFun (congrFun hT i) j
    simpa [Matrix.transpose_apply] using h
  have h1 := dotProduct_mulVec_nonneg_of_posSemidef hG (twoPoint i j 1)
  have h2 := dotProduct_mulVec_nonneg_of_posSemidef hG (twoPoint i j (-1))
  rw [dotProduct_twoPoint, hs] at h1 h2
  have hi := diag_le_trace hG i
  have hj := diag_le_trace hG j
  rw [abs_le]
  constructor <;> nlinarith

/-- The symmetric mass restriction and finite action density give nonnegative diagonals. -/
theorem mass_diag_nonneg (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hsym : (mass v).IsHermitian)
    (hfin : cost L1 L2 v ≠ ⊤) (i : Fin n) : 0 ≤ mass v i i :=
  (mass_posSemidef_of_cost_ne_top L1 L2 v hsym hfin).diag_nonneg

/-- Each mass diagonal is bounded by the trace, with the paper's symmetry explicit. -/
theorem mass_diag_le_trace (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hsym : (mass v).IsHermitian)
    (hfin : cost L1 L2 v ≠ ⊤) (i : Fin n) : mass v i i ≤ (mass v).trace :=
  diag_le_trace (mass_posSemidef_of_cost_ne_top L1 L2 v hsym hfin) i

/-- Every real mass coordinate, including off-diagonal entries, is controlled by the trace. -/
theorem mass_entry_abs_le_trace (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hsym : (mass v).IsHermitian)
    (hfin : cost L1 L2 v ≠ ⊤) (i j : Fin n) : |mass v i j| ≤ (mass v).trace :=
  abs_apply_le_trace_of_posSemidef (mass_posSemidef_of_cost_ne_top L1 L2 v hsym hfin) i j

/-! ### Row squares and coordinate bounds with explicit trace and Frobenius coefficients -/

theorem rowSquares_le_frobeniusSq {m p : ℕ} (L : Matrix (Fin m) (Fin p) ℝ) (j : Fin m) :
    ∑ a, L j a ^ 2 ≤ frobeniusSq L :=
  Finset.single_le_sum (f := fun r ↦ ∑ a, L r a ^ 2)
    (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)

theorem reaction_entry_sq_le_trace (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hsym : (mass v).IsHermitian)
    (hfin : cost L1 L2 v ≠ ⊤) (i j : Fin n) :
    reaction v i j ^ 2 ≤
      2 * (cost L1 L2 v).toReal * ((mass v).trace * frobeniusSq L2) := by
  have hG := mass_posSemidef_of_cost_ne_top L1 L2 v hsym hfin
  have h := reaction_entry_sq_le L1 L2 v hfin i j
  have hE : 0 ≤ (cost L1 L2 v).toReal := ENNReal.toReal_nonneg
  have h1 : mass v i i * ∑ a, L2 j a ^ 2 ≤ (mass v).trace * frobeniusSq L2 :=
    mul_le_mul (diag_le_trace hG i) (rowSquares_le_frobeniusSq L2 j)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      (le_trans hG.diag_nonneg (diag_le_trace hG i))
  exact le_trans h (mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hE))

theorem flux_entry_sq_le_trace (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hsym : (mass v).IsHermitian)
    (hfin : cost L1 L2 v ≠ ⊤) (i : Fin n) (j : Fin k) :
    flux v i j ^ 2 ≤
      2 * (cost L1 L2 v).toReal * ((mass v).trace * frobeniusSq L1) := by
  have hG := mass_posSemidef_of_cost_ne_top L1 L2 v hsym hfin
  have h := flux_entry_sq_le L1 L2 v hfin i j
  have hE : 0 ≤ (cost L1 L2 v).toReal := ENNReal.toReal_nonneg
  have h1 : mass v i i * ∑ a, L1 j a ^ 2 ≤ (mass v).trace * frobeniusSq L1 :=
    mul_le_mul (diag_le_trace hG i) (rowSquares_le_frobeniusSq L1 j)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      (le_trans hG.diag_nonneg (diag_le_trace hG i))
  exact le_trans h (mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hE))

/-! ### Time scalar test `W = w • 1` -/

theorem pw_frob_sub_left {m p : ℕ} (X X' Y : Matrix (Fin m) (Fin p) ℝ) :
    frob (X - X') Y = frob X Y - frob X' Y := by
  simp only [frob, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem pw_frob_one_left (G : Matrix (Fin n) (Fin n) ℝ) :
    frob (1 : Matrix (Fin n) (Fin n) ℝ) G = G.trace := by
  rw [frob_eq_trace, Matrix.transpose_one, Matrix.one_mul]

theorem frob_gram_le_frobeniusSq_mul_trace (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hfin : cost L1 L2 v ≠ ⊤)
    {p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) :
    frob (gram X) (mass v) ≤ frobeniusSq X * (mass v).trace := by
  have h := frob_nonneg_of_cost_ne_top L1 L2 v hfin (posSemidef_frobeniusSq_sub_gram X)
  rw [pw_frob_sub_left, frob_smul_left, pw_frob_one_left] at h
  linarith

theorem frob_gram_scalar_mul_le (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hfin : cost L1 L2 v ≠ ⊤) (w : ℝ) :
    frob (gram ((w • (1 : Matrix (Fin n) (Fin n) ℝ)) * L2)) (mass v) ≤
      w ^ 2 * frobeniusSq L2 * (mass v).trace := by
  rw [Matrix.smul_mul, Matrix.one_mul, gram_smul, frob_smul_left]
  have h := frob_gram_le_frobeniusSq_mul_trace L1 L2 v hfin L2
  calc w ^ 2 * frob (gram L2) (mass v)
      ≤ w ^ 2 * (frobeniusSq L2 * (mass v).trace) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg w)
    _ = w ^ 2 * frobeniusSq L2 * (mass v).trace := by ring

#print axioms reaction_pairing_sq_le
#print axioms flux_pairing_sq_le
#print axioms frob_gram_single_mul
#print axioms reaction_entry_sq_le
#print axioms flux_entry_sq_le
#print axioms abs_apply_le_trace_of_posSemidef
#print axioms mass_entry_abs_le_trace
#print axioms reaction_entry_sq_le_trace
#print axioms flux_entry_sq_le_trace
#print axioms frob_gram_scalar_mul_le

end

end MatrixTransport.ReactionZero
