import MatrixTransport.ReactionZero.WeightedAction

/-!
# Local action estimates for the weighted matrix cost

Real finite-dimensional estimates for `cost L1 L2` with arbitrary `n k : ℕ` and arbitrary weights.
It contains Gram scaling, exact quadratic dual test points in the reaction and flux directions,
the resulting Fenchel lower bounds (no inverse and no positivity assumption on the mass), and the
fact that finite cost plus an explicitly assumed Hermitian mass forces a positive semidefinite mass.
There is no convergence, compactness, or continuity-equation statement here.
-/

set_option autoImplicit false

open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.ReactionZero

noncomputable section

variable {n k : ℕ}

/-! ### Gram and Frobenius algebra -/

theorem gram_smul {m p : ℕ} (s : ℝ) (X : Matrix (Fin m) (Fin p) ℝ) :
    gram (s • X) = s ^ 2 • gram X := by
  simp only [gram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]

theorem gram_zero {m p : ℕ} : gram (0 : Matrix (Fin m) (Fin p) ℝ) = 0 := by
  simp [gram]

theorem frob_smul_left {m p : ℕ} (s : ℝ) (X Y : Matrix (Fin m) (Fin p) ℝ) :
    frob (s • X) Y = s * frob X Y := by
  unfold frob
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem frob_smul_right {m p : ℕ} (s : ℝ) (X Y : Matrix (Fin m) (Fin p) ℝ) :
    frob X (s • Y) = s * frob X Y := by
  unfold frob
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem frob_neg_left {m p : ℕ} (X Y : Matrix (Fin m) (Fin p) ℝ) :
    frob (-X) Y = -frob X Y := by
  simp [frob, Finset.sum_neg_distrib]

theorem frob_zero_left {m p : ℕ} (Y : Matrix (Fin m) (Fin p) ℝ) : frob 0 Y = 0 := by
  simp [frob]

theorem weightedPair_pack_left (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) :
    weightedPair (fun _ ↦ 1) (pack A B C) v =
      frob A (mass v) + frob B (flux v) + frob C (reaction v) := by
  rw [weightedPair_expand]
  simp only [mass_pack, flux_pack, reaction_pack, frob]

theorem frob_vecMulVec_self (x : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) :
    frob (Matrix.vecMulVec x x) G = dotProduct x (G.mulVec x) := by
  simp only [frob, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The full Frobenius pairing is the trace of the transpose product. -/
theorem frob_eq_trace {m p : ℕ} (A B : Matrix (Fin m) (Fin p) ℝ) :
    frob A B = (A.transpose * B).trace := by
  simp only [frob, Matrix.trace]
  exact Finset.sum_comm

/-- The actual Gram coefficient is a congruence trace, in arbitrary dimensions. -/
theorem frob_gram_eq_trace {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) :
    frob (gram X) G = (X.transpose * G * X).trace := by
  rw [frob_eq_trace]
  simp only [gram, Matrix.transpose_mul, Matrix.transpose_transpose]
  exact (Matrix.trace_mul_cycle X.transpose G X).symm

/-- Positive semidefinite matrix mass gives a nonnegative genuine Gram coefficient. -/
theorem frob_gram_nonneg {m p : ℕ} {G : Matrix (Fin m) (Fin m) ℝ}
    (hG : G.PosSemidef) (X : Matrix (Fin m) (Fin p) ℝ) : 0 ≤ frob (gram X) G := by
  rw [frob_gram_eq_trace]
  have h := (hG.conjTranspose_mul_mul_same X).trace_nonneg
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-! ### Exact quadratic dual test points -/

theorem isHermitian_smul_gram {m p : ℕ} (c : ℝ) (X : Matrix (Fin m) (Fin p) ℝ) :
    (c • gram X).IsHermitian := by
  refine (posSemidef_gram X).isHermitian.smul ?_
  unfold IsSelfAdjoint
  exact star_trivial _

theorem pack_reaction_mem_dualSet (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    pack (-(s ^ 2 / 2 : ℝ) • gram (W * L2)) (0 : Matrix (Fin n) (Fin k) ℝ) (s • W)
      ∈ dualSet L1 L2 := by
  refine ⟨?_, ?_⟩
  · exact isHermitian_smul_gram _ _
  · have h0 := (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
    convert h0 using 1
    simp only [mass_pack, flux_pack, reaction_pack, Matrix.zero_mul, Matrix.smul_mul, gram_zero,
      gram_smul]
    module

theorem pack_flux_mem_dualSet (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (W : Matrix (Fin n) (Fin k) ℝ) :
    pack (-(s ^ 2 / 2 : ℝ) • gram (W * L1)) (s • W) (0 : Matrix (Fin n) (Fin n) ℝ)
      ∈ dualSet L1 L2 := by
  refine ⟨?_, ?_⟩
  · exact isHermitian_smul_gram _ _
  · have h0 := (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
    convert h0 using 1
    simp only [mass_pack, flux_pack, reaction_pack, Matrix.zero_mul, Matrix.smul_mul, gram_zero,
      gram_smul]
    module

theorem pack_neg_psd_mem_dualSet (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    pack (-(t • P)) (0 : Matrix (Fin n) (Fin k) ℝ) (0 : Matrix (Fin n) (Fin n) ℝ)
      ∈ dualSet L1 L2 := by
  refine ⟨?_, ?_⟩
  · exact (hP.smul ht).isHermitian.neg
  · convert hP.smul ht using 1
    simp [gram_zero]

/-! ### Fenchel estimates -/

theorem reaction_fenchel (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (v : Coord n k → ℝ) (s : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    ENNReal.ofReal (s * frob W (reaction v) - (s ^ 2 / 2) * frob (gram (W * L2)) (mass v))
      ≤ cost L1 L2 v := by
  have h := cost_fenchel L1 L2 v _ (pack_reaction_mem_dualSet L1 L2 s W)
  rw [weightedPair_pack_left, frob_smul_left, frob_smul_left, frob_zero_left] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ring

theorem flux_fenchel (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (v : Coord n k → ℝ) (s : ℝ) (W : Matrix (Fin n) (Fin k) ℝ) :
    ENNReal.ofReal (s * frob W (flux v) - (s ^ 2 / 2) * frob (gram (W * L1)) (mass v))
      ≤ cost L1 L2 v := by
  have h := cost_fenchel L1 L2 v _ (pack_flux_mem_dualSet L1 L2 s W)
  rw [weightedPair_pack_left, frob_smul_left, frob_smul_left, frob_zero_left] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ring

theorem reaction_fenchel_le_toReal (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hfin : cost L1 L2 v ≠ ⊤) (s : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    s * frob W (reaction v) - (s ^ 2 / 2) * frob (gram (W * L2)) (mass v)
      ≤ (cost L1 L2 v).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hfin).1 (reaction_fenchel L1 L2 v s W)

theorem flux_fenchel_le_toReal (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hfin : cost L1 L2 v ≠ ⊤) (s : ℝ)
    (W : Matrix (Fin n) (Fin k) ℝ) :
    s * frob W (flux v) - (s ^ 2 / 2) * frob (gram (W * L1)) (mass v)
      ≤ (cost L1 L2 v).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hfin).1 (flux_fenchel L1 L2 v s W)

/-! ### Finite cost and a Hermitian mass force positive semidefiniteness -/

theorem frob_nonneg_of_cost_ne_top (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hfinite : cost L1 L2 v ≠ ⊤)
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef) : 0 ≤ frob P (mass v) := by
  by_contra hneg
  push Not at hneg
  have hc : 0 < -frob P (mass v) := neg_pos.2 hneg
  have hE : 0 ≤ (cost L1 L2 v).toReal := ENNReal.toReal_nonneg
  have ht : 0 ≤ ((cost L1 L2 v).toReal + 1) / (-frob P (mass v)) :=
    div_nonneg (by linarith) hc.le
  have h := cost_fenchel L1 L2 v _ (pack_neg_psd_mem_dualSet L1 L2 hP ht)
  rw [weightedPair_pack_left, frob_neg_left, frob_smul_left, frob_zero_left,
    frob_zero_left] at h
  have h2 := (ENNReal.ofReal_le_iff_le_toReal hfinite).1 h
  have h3 : ((cost L1 L2 v).toReal + 1) / (-frob P (mass v)) * (-frob P (mass v))
      = (cost L1 L2 v).toReal + 1 := div_mul_cancel₀ _ hc.ne'
  nlinarith [h2, h3]

theorem reaction_coefficient_nonneg (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hfinite : cost L1 L2 v ≠ ⊤)
    (W : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frob (gram (W * L2)) (mass v) :=
  frob_nonneg_of_cost_ne_top L1 L2 v hfinite (posSemidef_gram _)

theorem flux_coefficient_nonneg (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hfinite : cost L1 L2 v ≠ ⊤)
    (W : Matrix (Fin n) (Fin k) ℝ) : 0 ≤ frob (gram (W * L1)) (mass v) :=
  frob_nonneg_of_cost_ne_top L1 L2 v hfinite (posSemidef_gram _)

theorem mass_posSemidef_of_cost_ne_top (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hsym : (mass v).IsHermitian)
    (hfinite : cost L1 L2 v ≠ ⊤) : (mass v).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsym fun x ↦ ?_
  have hP : (Matrix.vecMulVec x x).PosSemidef := by
    have := Matrix.posSemidef_vecMulVec_self_star x
    simpa only [star_trivial] using this
  have h := frob_nonneg_of_cost_ne_top L1 L2 v hfinite hP
  rw [frob_vecMulVec_self] at h
  simpa only [star_trivial] using h

#print axioms mass_posSemidef_of_cost_ne_top
#print axioms reaction_fenchel
#print axioms flux_fenchel
#print axioms frob_gram_nonneg

end

end MatrixTransport.ReactionZero
