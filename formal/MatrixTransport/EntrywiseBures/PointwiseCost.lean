import MatrixTransport.ReactionZero.PointwiseBounds
import MatrixTransport.EntrywiseBures.Operator
import MatrixTransport.EntrywiseBures.SqrtProvider

/-!
# Pointwise upper bounds for the ORIGINAL local support cost

Both bounds are proved directly from the definition of `ReactionZero.cost` as the support
function of the actual quadratic dual set: every admissible dual triple is tested against the
explicit primal density.  No pseudoinverse, Gram-channel splitting or range condition is
assumed.

* `cost_contraction_le`: Lagrangian transport density `(c M, σ M V(v), 0)` with transport
  weight `t I`; bound `|v|² tr M / (2 t² c)`.
* `cost_reaction_le`: Bures reaction density `(c W Wᵀ, 0, 2 W Δᵀ H)`; bound `2 ‖Δ‖²_F / c`,
  valid for every transport weight and every symmetric reaction weight `H`.

-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

namespace MatrixTransport.EntrywiseBures

open MatrixTransport.ReactionZero.ClosedDomain

variable {d n : ℕ}

/-! ### Two scalar inequalities -/

theorem transport_scalar_bound {c t σ a1 F G q V T : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hσ : σ ^ 2 = 1) (hq : 0 ≤ q)
    (hslack : 0 ≤ -a1 - 1 / 2 * (t ^ 2 * G) - 1 / 2 * q)
    (hsq : 0 ≤ (c * t ^ 2) ^ 2 * G - 2 * (c * t ^ 2) * σ * F + σ ^ 2 * (V * T)) :
    c * a1 + σ * F ≤ V * T / (2 * t ^ 2 * c) := by
  have hpos : 0 < 2 * t ^ 2 * c := by positivity
  rw [le_div_iff₀ hpos]
  rw [hσ, one_mul] at hsq
  have h1 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * c ^ 2 * t ^ 2) hslack
  have h2 := mul_nonneg (by positivity : (0 : ℝ) ≤ c ^ 2 * t ^ 2) hq
  nlinarith [h1, h2, hsq]

theorem scalar_cross_le {y δ c : ℝ} (hc : 0 < c) :
    2 * (y * δ) - c / 2 * (y * y) ≤ 2 / c * (δ * δ) := by
  have hc' : c ≠ 0 := hc.ne'
  have h := sq_nonneg (c * y - 2 * δ)
  have key : 2 / c * (δ * δ) - (2 * (y * δ) - c / 2 * (y * y)) =
      (c * y - 2 * δ) ^ 2 / (2 * c) := by
    field_simp
    ring
  have hpos : 0 ≤ (c * y - 2 * δ) ^ 2 / (2 * c) := div_nonneg h (by positivity)
  linarith

theorem frob_cross_le (Y D : Matrix (Fin n) (Fin n) ℝ) {c : ℝ} (hc : 0 < c) :
    2 * ReactionZero.frob Y D - c / 2 * ReactionZero.frob Y Y ≤
      2 / c * ReactionZero.frob D D := by
  unfold ReactionZero.frob
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun j _ ↦ scalar_cross_le hc

/-! ### Gram expansion against a symmetric matrix -/

theorem frob_gram_sub_expand {k : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M)
    (B X : Matrix (Fin n) (Fin k) ℝ) (α β : ℝ) :
    ReactionZero.frob (ReactionZero.gram (α • B - β • X)) M =
      α ^ 2 * ReactionZero.frob (ReactionZero.gram B) M -
        2 * α * β * ReactionZero.frob B (M * X) +
          β ^ 2 * ReactionZero.frob (ReactionZero.gram X) M := by
  have hx : (Xᵀ * M * B).trace = (Bᵀ * M * X).trace := by
    rw [← Matrix.trace_transpose (Xᵀ * M * B)]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hM, Matrix.mul_assoc]
  have hc : ReactionZero.frob B (M * X) = (Bᵀ * M * X).trace := by
    rw [ReactionZero.frob_eq_trace, Matrix.mul_assoc]
  rw [ReactionZero.frob_gram_eq_trace, ReactionZero.frob_gram_eq_trace,
    ReactionZero.frob_gram_eq_trace, hc]
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, hx]
  ring

/-! ### Lagrangian transport density -/

/-- Pointwise cost of the Lagrangian flux `Q_ℓ = σ v_ℓ M` with mass `c M` at transport
weight `t I`.  The sign `σ = ±1` covers reversed (expansion) segments. -/
theorem cost_contraction_le (R : PSDSqrt n) (H : Matrix (Fin n) (Fin n) ℝ)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) (v : Fin d → ℝ) {c t σ : ℝ}
    (hc : 0 < c) (ht : 0 < t) (hσ : σ ^ 2 = 1) :
    ReactionZero.cost (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H
        (ReactionZero.pack (c • M) (σ • (M * velocityMatrix v)) 0) ≤
      ENNReal.ofReal ((∑ ℓ, v ℓ ^ 2) * M.trace / (2 * t ^ 2 * c)) := by
  unfold ReactionZero.cost supportFunction
  refine iSup₂_le fun a ha ↦ ENNReal.ofReal_le_ofReal ?_
  rw [ReactionZero.weightedPair_pack]
  obtain ⟨_, hS⟩ := ha
  have hMt : Mᵀ = M := transpose_eq_of_posSemidef hM
  have hslack := frob_nonneg_of_posSemidef R hS hM
  have hgB : ReactionZero.gram (ReactionZero.flux a *
      (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ))) =
      t ^ 2 • ReactionZero.gram (ReactionZero.flux a) := by
    rw [Matrix.mul_smul, Matrix.mul_one, ReactionZero.gram_smul]
  rw [ReactionZero.pw_frob_sub_left, ReactionZero.pw_frob_sub_left, ReactionZero.frob_neg_left,
    ReactionZero.frob_smul_left, ReactionZero.frob_smul_left, hgB,
    ReactionZero.frob_smul_left] at hslack
  have hq := ReactionZero.frob_gram_nonneg hM (ReactionZero.reaction a * H)
  have hsq0 := ReactionZero.frob_gram_nonneg hM
    ((c * t ^ 2) • ReactionZero.flux a - σ • velocityMatrix (n := n) v)
  rw [frob_gram_sub_expand M hMt, velocity_gram, ReactionZero.frob_smul_left,
    ReactionZero.pw_frob_one_left] at hsq0
  rw [ReactionZero.frob_smul_right, ReactionZero.frob_smul_right, frob_zero_right, add_zero]
  exact transport_scalar_bound hc ht hσ hq hslack hsq0

/-! ### Bures reaction density -/

theorem frob_gram_reaction (C H W : Matrix (Fin n) (Fin n) ℝ) :
    ReactionZero.frob (ReactionZero.gram (C * H)) (ReactionZero.gram W) =
      ReactionZero.frob (Wᵀ * (C * H)) (Wᵀ * (C * H)) := by
  rw [ReactionZero.frob_gram_eq_trace, ReactionZero.frob_eq_trace]
  simp only [ReactionZero.gram, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

theorem frob_reaction_cross {H : Matrix (Fin n) (Fin n) ℝ} (hHt : Hᵀ = H)
    (C W Δ : Matrix (Fin n) (Fin n) ℝ) :
    ReactionZero.frob C (W * Δᵀ * H) = ReactionZero.frob (Wᵀ * (C * H)) Δᵀ := by
  rw [ReactionZero.frob_eq_trace, ReactionZero.frob_eq_trace]
  have h1 : Cᵀ * (W * Δᵀ * H) = (Cᵀ * W * Δᵀ) * H := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm (Cᵀ * W * Δᵀ) H]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hHt, Matrix.mul_assoc]

/-- Pointwise cost of the Bures reaction density.  Here `W = H P` and `Δ` is the factor
increment, so `W Wᵀ = H P Pᵀ H` and `2 W Δᵀ H = 2 H P Δᵀ H`. -/
theorem cost_reaction_le {k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ)
    {H : Matrix (Fin n) (Fin n) ℝ} (hHt : Hᵀ = H) (W Δ : Matrix (Fin n) (Fin n) ℝ)
    {c : ℝ} (hc : 0 < c) :
    ReactionZero.cost L H
        (ReactionZero.pack (c • ReactionZero.gram W) 0 ((2 : ℝ) • (W * Δᵀ * H))) ≤
      ENNReal.ofReal (2 / c * ReactionZero.frobeniusSq Δ) := by
  unfold ReactionZero.cost supportFunction
  refine iSup₂_le fun a ha ↦ ENNReal.ofReal_le_ofReal ?_
  rw [ReactionZero.weightedPair_pack]
  obtain ⟨_, hS⟩ := ha
  have hgW := ReactionZero.posSemidef_gram W
  have hslack := ReactionZero.frob_gram_nonneg hS W
  rw [frob_comm, ReactionZero.pw_frob_sub_left, ReactionZero.pw_frob_sub_left,
    ReactionZero.frob_neg_left, ReactionZero.frob_smul_left, ReactionZero.frob_smul_left,
    frob_gram_reaction] at hslack
  have hB := ReactionZero.frob_gram_nonneg hgW (ReactionZero.flux a * L)
  have hcross := frob_cross_le (Wᵀ * (ReactionZero.reaction a * H)) Δᵀ hc
  rw [frob_transpose_self] at hcross
  rw [ReactionZero.frob_smul_right, frob_zero_right, ReactionZero.frob_smul_right,
    frob_reaction_cross hHt]
  have h1 := mul_nonneg hc.le hslack
  have h2 := mul_nonneg hc.le hB
  nlinarith [h1, h2, hcross]

#print axioms cost_contraction_le
#print axioms cost_reaction_le

end MatrixTransport.EntrywiseBures
