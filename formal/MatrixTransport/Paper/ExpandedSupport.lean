import MatrixTransport.ReactionZero.MassScaling
import MatrixTransport.EntrywiseBures.PathOperations
import MatrixTransport.Paper.GenericBridges

/-!
# Explicit support and projection identities in the expanded exposition

The results use the original full-coordinate support cost and signed-measure action.
In particular, reference change is valid for infinite action and for a reference
density which vanishes on a set of positive measure.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.Paper.ExpandedSupport

open MatrixTransport.ReactionZero

variable {n k : ℕ}

theorem massScaleDual_comp (r s : ℝ) (a : Coord n k → ℝ) :
    massScaleDual r (massScaleDual s a) = massScaleDual (r * s) a := by
  ext c
  rcases c with p | p | p <;>
    simp [massScaleDual, pack, pow_two, mul_assoc, mul_left_comm]

theorem massScaleDual_one (a : Coord n k → ℝ) : massScaleDual 1 a = a := by
  ext c
  rcases c with p | p | p <;> simp [massScaleDual, pack] <;> rfl

/-- The quadratic dual rescaling is onto as well as constraint preserving. -/
theorem massScaleDual_bijOn (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) {r : ℝ} (hr : r ≠ 0) :
    Set.BijOn (massScaleDual r) (ReactionZero.dualSet L H) (ReactionZero.dualSet L H) := by
  refine ⟨fun a ha ↦ massScaleDual_mem L H r a ha, ?_, ?_⟩
  · intro a ha b hb hab
    have h := congrArg (massScaleDual r⁻¹) hab
    simpa only [massScaleDual_comp, inv_mul_cancel₀ hr, massScaleDual_one] using h
  · intro a ha
    refine ⟨massScaleDual r⁻¹ a, massScaleDual_mem L H r⁻¹ a ha, ?_⟩
    simp only [massScaleDual_comp, mul_inv_cancel₀ hr, massScaleDual_one]

/-- Literal positive scaling of both rate channels, including an infinite local cost. -/
theorem cost_pack_smul_rates (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (M R : Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) {c : ℝ} (hc : 0 < c) :
    cost L H (pack M (c • Z) (c • R)) =
      ENNReal.ofReal (c ^ 2) * cost L H (pack M Z R) := by
  simpa only [inv_inv] using cost_pack_div_rates L H M R Z (inv_pos.mpr hc)

/-- Any finite dominating reference computes the same original action. -/
theorem action_any_finite_reference {X : Type*} [MeasurableSpace X]
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (μ : Coord n k → SignedMeasure X) (ν : Measure X) [IsFiniteMeasure ν]
    (hμ : ∀ c, μ c ≪ᵥ ν.toENNRealVectorMeasure) :
    action L H μ = ∫⁻ x, cost L H (fun c ↦ (μ c).rnDeriv ν x) ∂ν := by
  have he : (fun c ↦ ν.withDensityᵥ ((μ c).rnDeriv ν)) = μ :=
    funext fun c ↦ SignedMeasure.withDensityᵥ_rnDeriv_eq (μ c) ν (hμ c)
  rw [← he]
  conv_rhs => rw [he]
  exact EntrywiseBures.action_densityPath L H (fun c ↦ (μ c).rnDeriv ν)
    (fun c ↦ SignedMeasure.measurable_rnDeriv (μ c) ν)
    (fun c ↦ SignedMeasure.integrable_rnDeriv (μ c) ν)

/-- The Jensen defect for an arbitrary middle matrix, before its positivity is used. -/
theorem quadratic_combination_defect {m p : ℕ}
    (B C : Matrix (Fin m) (Fin p) ℝ) (K : Matrix (Fin p) (Fin p) ℝ) (θ : ℝ) :
    θ • (B * K * Bᵀ) + (1 - θ) • (C * K * Cᵀ) -
      (θ • B + (1 - θ) • C) * K * (θ • B + (1 - θ) • C)ᵀ =
        (θ * (1 - θ)) • ((B - C) * K * (B - C)ᵀ) := by
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul]
  module

theorem quadratic_combination_defect_posSemidef {m p : ℕ}
    (B C : Matrix (Fin m) (Fin p) ℝ) {K : Matrix (Fin p) (Fin p) ℝ}
    (hK : K.PosSemidef) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (θ • (B * K * Bᵀ) + (1 - θ) • (C * K * Cᵀ) -
      (θ • B + (1 - θ) • C) * K * (θ • B + (1 - θ) • C)ᵀ).PosSemidef := by
  rw [quadratic_combination_defect]
  have hp := hK.mul_mul_conjTranspose_same (B - C)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hp
  exact hp.smul (mul_nonneg hθ (sub_nonneg.mpr hθ1))

/-- The principal-minor estimate used before the arithmetic--geometric mean bound. -/
theorem abs_entry_le_sqrt_diagonal {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosSemidef) (i j : Fin n) :
    |G i j| ≤ Real.sqrt (G i i * G j j) ∧
      Real.sqrt (G i i * G j j) ≤ (G i i + G j j) / 2 := by
  have hs : G j i = G i j := by
    simpa only [Matrix.transpose_apply] using
      congrFun (congrFun (EntrywiseBures.transpose_eq_of_posSemidef hG) i) j
  have hd : ∀ s : ℝ, s * (-2 * G i j) - (s ^ 2 / 2) * (2 * G j j) ≤ G i i := by
    intro s
    have h := dotProduct_mulVec_nonneg_of_posSemidef hG (twoPoint i j s)
    rw [dotProduct_twoPoint, hs] at h
    nlinarith
  have hb := quadratic_dual_bound (mul_nonneg (by norm_num) hG.diag_nonneg)
    hG.diag_nonneg hd
  have hprod : 0 ≤ G i i * G j j := mul_nonneg hG.diag_nonneg hG.diag_nonneg
  have hsq := Real.sq_sqrt hprod
  constructor
  · nlinarith [sq_abs (G i j), Real.sqrt_nonneg (G i i * G j j), abs_nonneg (G i j)]
  · nlinarith [sq_nonneg (G i i - G j j), Real.sqrt_nonneg (G i i * G j j),
      (hG.diag_nonneg : 0 ≤ G i i), (hG.diag_nonneg : 0 ≤ G j j)]

/-- The exact Frobenius square completion in the singular reaction-path estimate. -/
theorem frobenius_complete_square {m p : ℕ}
    (Y Δ : Matrix (Fin m) (Fin p) ℝ) :
    -(1 / 2 : ℝ) * ReactionZero.frobeniusSq Y + 2 * ReactionZero.frob Y Δ =
      2 * ReactionZero.frobeniusSq Δ -
        (1 / 2 : ℝ) * ReactionZero.frobeniusSq (Y - (2 : ℝ) • Δ) := by
  simp only [ReactionZero.frobeniusSq, ReactionZero.frob, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The explicit regularized factor in the text is the formal Bures-map factor. -/
theorem buresFactor_literal (R : EntrywiseBures.PSDSqrt n)
    {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) (hdet : X.det ≠ 0) :
    EntrywiseBures.buresMap R X Y * R.sqrt X =
      (R.sqrt X)⁻¹ * R.sqrt (R.sqrt X * Y * R.sqrt X) := by
  have hu := EntrywiseBures.isUnit_det_of_mul_self (R.sqrt_mul_sqrt X hX) hdet
  simp only [EntrywiseBures.buresMap, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

/-- The interior-ball inclusion along the straight hub contraction. -/
theorem convex_ball_contraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : Convex ℝ Ω) {x h : E} (hx : x ∈ Ω) {r s : ℝ}
    (hball : Metric.ball h r ⊆ Ω) (hs : 0 < s) (hs1 : s ≤ 1) :
    Metric.ball ((1 - s) • x + s • h) (s * r) ⊆ Ω := by
  intro y hy
  let z := h + s⁻¹ • (y - ((1 - s) • x + s • h))
  have hz : z ∈ Metric.ball h r := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖h + s⁻¹ • (y - ((1 - s) • x + s • h)) - h‖ < r
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    have hy' : ‖y - ((1 - s) • x + s • h)‖ < s * r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have h := mul_lt_mul_of_pos_left hy' (inv_pos.mpr hs)
    simpa only [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul] using h
  have hc := hΩ hx (hball hz) (sub_nonneg.mpr hs1) hs.le (by ring : 1 - s + s = 1)
  have he : (1 - s) • x + s • z = y := by
    dsimp [z]
    rw [smul_add, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    abel
  rwa [he] at hc

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
open ConvexProjection

/-- The combined Euclidean coordinate norm is bounded by the absolute-coordinate weight. -/
theorem euclidean_norm_le_sum_abs {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ i, |v i| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  apply (Real.sqrt_le_iff).mpr
  constructor
  · exact Finset.sum_nonneg fun i _ ↦ abs_nonneg (v i)
  · simpa only [sq_abs] using
      Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i ↦ |v i|) (fun i _ ↦ abs_nonneg (v i))

/-- A point attaining the distance infimum is the same nearest point. -/
theorem project_unique (K : Target E) (x q : E) (hq : q ∈ K.carrier)
    (hmin : ‖x - q‖ = ⨅ w : K.carrier, ‖x - w‖) : q = project K x := by
  let p := project K x
  have hp := project_variational K x q hq
  have hq' := (norm_eq_iInf_iff_real_inner_le_zero K.convex hq).mp hmin
    p (project_mem K x)
  change inner ℝ (x - p) (q - p) ≤ 0 at hp
  have hid : inner ℝ (q - p) (q - p) =
      inner ℝ (x - p) (q - p) + inner ℝ (x - q) (p - q) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [real_inner_self_eq_norm_sq] at hid
  have hn : ‖q - p‖ = 0 := by nlinarith [norm_nonneg (q - p)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The intermediate firm nonexpansiveness inequality displayed in the proof. -/
theorem project_firm (K : Target E) (u v : E) :
    ‖project K u - project K v‖ ^ 2 ≤
      inner ℝ (project K u - project K v) (u - v) := by
  let p := project K u
  let q := project K v
  have hu := project_variational K u q (project_mem K v)
  have hv := project_variational K v p (project_mem K u)
  change inner ℝ (u - p) (q - p) ≤ 0 at hu
  change inner ℝ (v - q) (p - q) ≤ 0 at hv
  have hneg : q - p = -(p - q) := by abel
  rw [hneg, inner_neg_right] at hu
  have hid : inner ℝ (u - v) (p - q) =
      inner ℝ (u - p) (p - q) - inner ℝ (v - q) (p - q) +
        inner ℝ (p - q) (p - q) := by
    simp only [inner_sub_left]
    ring
  change ‖p - q‖ ^ 2 ≤ inner ℝ (p - q) (u - v)
  rw [real_inner_comm, hid, real_inner_self_eq_norm_sq]
  linarith

end Projection

#print axioms massScaleDual_bijOn
#print axioms cost_pack_smul_rates
#print axioms action_any_finite_reference
#print axioms quadratic_combination_defect_posSemidef
#print axioms project_firm

end MatrixTransport.Paper.ExpandedSupport
