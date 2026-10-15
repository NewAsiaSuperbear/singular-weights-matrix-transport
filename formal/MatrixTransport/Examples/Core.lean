import MatrixTransport.ReactionZero.LimitTheorem

/-!
# Dual certificates and competitor upper bounds

This module bounds the original signed Radon minimum from below using a native
closed-domain C¹ test whose field lies in the weighted dual set. Upper bounds use
constructed `Good` paths and the continuous dual representation of the action.
The competitors carry symmetric mass and satisfy the complete original continuity
equation. Elementary helpers for scalar matrices are included.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace LiZouTransport.Examples

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain

/-! ### Elementary helpers -/

theorem fin_one_eq_zero (i : Fin 1) : i = 0 := Subsingleton.elim i 0

theorem sum_fin_one (f : Fin 1 → ℝ) : ∑ i, f i = f 0 := by
  first
    | simp [Fin.sum_univ_succ]
    | (rw [Finset.univ_unique]; simp)
    | exact Fintype.sum_unique f

theorem posSemidef_fin_one (X : Matrix (Fin 1) (Fin 1) ℝ) (h : 0 ≤ X 0 0) : X.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    have hi : i = 0 := fin_one_eq_zero i
    have hj : j = 0 := fin_one_eq_zero j
    subst hi
    subst hj
    simp
  · have hx : star x ⬝ᵥ (X *ᵥ x) = x 0 * (X 0 0 * x 0) := by
      first
        | (simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]; done)
        | (simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]; ring)
    rw [hx]
    nlinarith [mul_nonneg h (sq_nonneg (x 0))]

theorem gram_fin_one_apply {p : ℕ} (X : Matrix (Fin 1) (Fin p) ℝ) :
    gram X 0 0 = ∑ l, X 0 l ^ 2 := by
  simp [gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

/-- Membership in the actual dual set for scalar mass (`n = 1`), as one real inequality. -/
theorem mem_dualSet_fin_one {k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin 1) (Fin 1) ℝ) (a : Coord 1 k → ℝ)
    (h : mass a 0 0 + (1 / 2 : ℝ) * (∑ l, (flux a * L) 0 l ^ 2) +
      (1 / 2 : ℝ) * (reaction a * H) 0 0 ^ 2 ≤ 0) :
    a ∈ dualSet L H := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    have hi : i = 0 := fin_one_eq_zero i
    have hj : j = 0 := fin_one_eq_zero j
    subst hi
    subst hj
    simp
  · apply posSemidef_fin_one
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
      gram_fin_one_apply, sum_fin_one]
    linarith

/-- The converse extraction: a dual-set member has scalar slack `≥ 0`. -/
theorem dualSet_fin_one_bound {k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin 1) (Fin 1) ℝ) (a : Coord 1 k → ℝ) (ha : a ∈ dualSet L H) :
    mass a 0 0 + (1 / 2 : ℝ) * (∑ l, (flux a * L) 0 l ^ 2) +
      (1 / 2 : ℝ) * (reaction a * H) 0 0 ^ 2 ≤ 0 := by
  obtain ⟨_, hP⟩ := ha
  have h0 : 0 ≤ (-mass a - (1 / 2 : ℝ) • gram (flux a * L) -
      (1 / 2 : ℝ) • gram (reaction a * H)) 0 0 := hP.diag_nonneg
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
    gram_fin_one_apply, sum_fin_one] at h0
  linarith

/-- A continuous real function on a compact space is bounded (stated without `let`). -/
theorem exists_abs_bound_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → ℝ) (hf : Continuous f) : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
  refine ⟨‖(⟨f, hf⟩ : C(X, ℝ))‖, fun x => ?_⟩
  have h := (⟨f, hf⟩ : C(X, ℝ)).norm_coe_le_norm x
  simpa [Real.norm_eq_abs] using h

/-! ### ENNReal bookkeeping -/

/-- A family of lower bounds `a - ε` for every `ε > 0` gives the lower bound `a`.  Used to pass
from the one-parameter test families (`η → 0`) to the sharp constant. -/
theorem ofReal_le_of_forall_pos_sub (a : ℝ) (V : ℝ≥0∞)
    (h : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal (a - ε) ≤ V) : ENNReal.ofReal a ≤ V := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.mpr hε
  have h1 := h (ε : ℝ) hε'
  calc ENNReal.ofReal a = ENNReal.ofReal ((a - (ε : ℝ)) + (ε : ℝ)) := by rw [sub_add_cancel]
    _ ≤ ENNReal.ofReal (a - (ε : ℝ)) + ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_add_le
    _ ≤ V + ε := by
      rw [ENNReal.ofReal_coe_nnreal]
      exact add_le_add h1 le_rfl

/-! ### The two certificates -/

section Certificates

variable {d n k : ℕ} {Ω : Set (Space d)}

/-- **All-competitor lower certificate.**  Every `Good` competitor (symmetric signed Radon mass,
full closed-domain `C¹` continuity equation for the problem's endpoints and operator) has action
at least the endpoint pairing of any closed-`C¹` jet whose test field lies in the dual set. -/
theorem ofReal_endpoint_le_minimumValue [Fact (IsCompact Ω)]
    (P : Limit.Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (φ : ClosedC1Jet Ω n) (hφ : ∀ p : Q Ω, testField P.operator φ p ∈ dualSet L H) :
    ENNReal.ofReal (endpointPair P.terminal φ 1 ⟨zero_le_one, le_rfl⟩ -
        endpointPair P.initial φ 0 ⟨le_rfl, zero_le_one⟩) ≤ Limit.minimumValue P L H := by
  unfold Limit.minimumValue constrainedInfimum
  refine le_iInf fun μ => le_iInf fun hμ => ?_
  have hCE := hμ.2 φ
  change Duality.coordinatePair (fun _ ↦ 1) μ (testField P.operator φ) =
    endpointPair P.terminal φ 1 ⟨zero_le_one, le_rfl⟩ -
      endpointPair P.initial φ 0 ⟨le_rfl, zero_le_one⟩ at hCE
  rw [← hCE]
  calc ENNReal.ofReal (Duality.coordinatePair (fun _ ↦ 1) μ (testField P.operator φ))
      ≤ Duality.continuousDual (fun _ ↦ 1) (dualSet L H) μ :=
        le_iSup₂ (f := fun (a : C(Q Ω, Coord n k → ℝ)) (_ : ∀ x, a x ∈ dualSet L H) ↦
          ENNReal.ofReal (Duality.coordinatePair (fun _ ↦ 1) μ a))
          (testField P.operator φ) hφ
    _ = action L H μ := (WeightedSet.action_eq_continuousDual L H μ).symm

/-- A `Good` path bounds the minimum value from above. -/
theorem minimumValue_le_of_good (P : Limit.Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Limit.Path Ω n k) (hμ : Limit.Good P μ) :
    Limit.minimumValue P L H ≤ action L H μ := by
  unfold Limit.minimumValue constrainedInfimum
  exact iInf_le_of_le μ (iInf_le_of_le hμ le_rfl)

/-- The integrated support action is bounded as soon as the signed pairing of every continuous
admissible dual field is.  This is the proved representation `action = continuousDual`. -/
theorem action_le_of_pairing_le [Fact (IsCompact Ω)]
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (μ : Limit.Path Ω n k) (C : ℝ≥0∞)
    (h : ∀ a : C(Q Ω, Coord n k → ℝ), (∀ x, a x ∈ dualSet L H) →
      ENNReal.ofReal (Duality.coordinatePair (fun _ ↦ 1) μ a) ≤ C) :
    action L H μ ≤ C := by
  rw [WeightedSet.action_eq_continuousDual]
  exact iSup₂_le h

end Certificates

end LiZouTransport.Examples

end
