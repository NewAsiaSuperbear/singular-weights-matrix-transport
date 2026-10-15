import MatrixTransport.ReactionZero.WeightedAction
import MatrixTransport.ReactionZero.ContinuousSelectorApproximation
import MatrixTransport.ReactionZero.MeasureCompactness

/-!
# The concrete weighted matrix dual set and lower semicontinuity

This module proves that the actual quadratic dual set from `WeightedAction` contains zero and is
closed and convex. It then instantiates the proved continuous-dual representation for the actual
weighted matrix action, in arbitrary matrix dimensions and with arbitrary finite coordinate
signed measures. No representation equality or action lower semicontinuity is assumed.

The full primal mass measure still has to be restricted to the original symmetric PSD class in
the continuity-equation and reaction-zero convergence theorem; these action lemmas do not replace
that condition. The quadratic dual set is not asserted to be a cone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.ReactionZero.WeightedSet

variable {n k : ℕ}

theorem continuous_mass : Continuous (mass (n := n) (k := k)) :=
  continuous_matrix fun i j ↦ continuous_apply (Sum.inl (i, j))

theorem continuous_flux : Continuous (flux (n := n) (k := k)) :=
  continuous_matrix fun i j ↦ continuous_apply (Sum.inr (Sum.inl (i, j)))

theorem continuous_reaction : Continuous (reaction (n := n) (k := k)) :=
  continuous_matrix fun i j ↦ continuous_apply (Sum.inr (Sum.inr (i, j)))

theorem continuous_gram {m p : ℕ} :
    Continuous (gram (m := m) (p := p)) :=
  continuous_id.matrix_mul continuous_id.matrix_transpose

theorem isClosed_setOf_isHermitian {m : ℕ} :
    IsClosed {A : Matrix (Fin m) (Fin m) ℝ | A.IsHermitian} :=
  isClosed_eq continuous_id.matrix_conjTranspose continuous_id

theorem isClosed_setOf_posSemidef {m : ℕ} :
    IsClosed {A : Matrix (Fin m) (Fin m) ℝ | A.PosSemidef} := by
  have he : {A : Matrix (Fin m) (Fin m) ℝ | A.PosSemidef} =
      {A | A.IsHermitian} ∩ ⋂ v : Fin m → ℝ, {A | 0 ≤ star v ⬝ᵥ (A *ᵥ v)} := by
    ext A
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, Matrix.posSemidef_iff_dotProduct_mulVec]
  rw [he]
  apply isClosed_setOf_isHermitian.inter
  apply isClosed_iInter
  intro v
  apply isClosed_le continuous_const
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

/-- The positive semidefinite slack occurring in the original weighted dual admissibility. -/
def slack (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (a : Coord n k → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  -mass a - (1 / 2 : ℝ) • gram (flux a * L1) - (1 / 2 : ℝ) • gram (reaction a * L2)

theorem continuous_slack (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) : Continuous (slack L1 L2) :=
  ((continuous_mass.neg).sub
    ((continuous_gram.comp (continuous_flux.matrix_mul continuous_const)).const_smul (1 / 2 : ℝ))).sub
      ((continuous_gram.comp (continuous_reaction.matrix_mul continuous_const)).const_smul (1 / 2 : ℝ))

theorem isClosed_dualSet (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) : IsClosed (dualSet L1 L2) :=
  (isClosed_setOf_isHermitian.preimage continuous_mass).inter
    (isClosed_setOf_posSemidef.preimage (continuous_slack L1 L2))

theorem zero_mem_dualSet (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) : (0 : Coord n k → ℝ) ∈ dualSet L1 L2 := by
  have hm : mass (0 : Coord n k → ℝ) = 0 := rfl
  have hf : flux (0 : Coord n k → ℝ) = 0 := rfl
  have hr : reaction (0 : Coord n k → ℝ) = 0 := rfl
  simpa [dualSet, hm, hf, hr, gram] using
    (show (0 : Matrix (Fin n) (Fin n) ℝ).IsHermitian ∧
      (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef from
      ⟨Matrix.isHermitian_zero, Matrix.PosSemidef.zero⟩)

/-- The exact Gram Jensen defect, proved entry by entry. -/
theorem gram_combination_defect {m p : ℕ} (X Y : Matrix (Fin m) (Fin p) ℝ) (θ : ℝ) :
    θ • gram X + (1 - θ) • gram Y - gram (θ • X + (1 - θ) • Y) =
      (θ * (1 - θ)) • gram (X - Y) := by
  ext i j
  simp only [gram, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem gram_combination {m p : ℕ} (X Y : Matrix (Fin m) (Fin p) ℝ) (θ : ℝ) :
    gram (θ • X + (1 - θ) • Y) = θ • gram X + (1 - θ) • gram Y -
      (θ * (1 - θ)) • gram (X - Y) := by
  have h := gram_combination_defect X Y θ
  apply eq_sub_iff_add_eq.mpr
  rw [← h]
  abel

theorem slack_combination (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (a b : Coord n k → ℝ) (θ : ℝ) :
    slack L1 L2 (θ • a + (1 - θ) • b) =
      θ • slack L1 L2 a + (1 - θ) • slack L1 L2 b +
        (1 / 2 : ℝ) • ((θ * (1 - θ)) • gram (flux a * L1 - flux b * L1)) +
        (1 / 2 : ℝ) • ((θ * (1 - θ)) • gram (reaction a * L2 - reaction b * L2)) := by
  have hm : mass (θ • a + (1 - θ) • b) = θ • mass a + (1 - θ) • mass b := rfl
  have hf : flux (θ • a + (1 - θ) • b) = θ • flux a + (1 - θ) • flux b := rfl
  have hr : reaction (θ • a + (1 - θ) • b) = θ • reaction a + (1 - θ) • reaction b := rfl
  unfold slack
  rw [hm, hf, hr]
  simp only [Matrix.add_mul, Matrix.smul_mul]
  rw [gram_combination, gram_combination]
  module

theorem convex_dualSet (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) : Convex ℝ (dualSet L1 L2) := by
  intro a ha b hb θ η hθ hη hsum
  obtain ⟨haH, haP⟩ := ha
  obtain ⟨hbH, hbP⟩ := hb
  have hηeq : η = 1 - θ := by linarith
  have hm : mass (θ • a + η • b) = θ • mass a + η • mass b := rfl
  refine ⟨?_, ?_⟩
  · rw [hm]
    exact (haH.smul (IsSelfAdjoint.of_nonneg hθ)).add (hbH.smul (IsSelfAdjoint.of_nonneg hη))
  · change (slack L1 L2 (θ • a + η • b)).PosSemidef
    rw [hηeq, slack_combination]
    have hp : 0 ≤ θ * (1 - θ) := mul_nonneg hθ (by linarith)
    have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
    exact (((haP.smul hθ).add (hbP.smul (by linarith))).add
      (((posSemidef_gram (flux a * L1 - flux b * L1)).smul hp).smul hhalf)).add
        (((posSemidef_gram (reaction a * L2 - reaction b * L2)).smul hp).smul hhalf)

section IntegratedAction

variable {Q : Type*} [MeasurableSpace Q] [MetricSpace Q] [CompactSpace Q] [BorelSpace Q]

/-- The original weighted matrix action has the genuine continuous dual representation. -/
theorem action_eq_continuousDual (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q) :
    action L1 L2 μ = Duality.continuousDual (fun _ ↦ 1) (dualSet L1 L2) μ :=
  SelectorApproximation.integratedSupport_eq_continuousDual (fun _ ↦ 1) (dualSet L1 L2)
    (zero_mem_dualSet L1 L2) (isClosed_dualSet L1 L2) (convex_dualSet L1 L2) μ

/-- Fixed-weight lower semicontinuity of the actual RN integrated weighted matrix action. -/
theorem action_le_liminf (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (μ : ℕ → Coord n k → SignedMeasure Q) (ν : Coord n k → SignedMeasure Q)
    (hμ : SignedWeakStarTendsto μ ν) :
    action L1 L2 ν ≤ atTop.liminf (fun j ↦ action L1 L2 (μ j)) :=
  SelectorApproximation.integratedSupport_le_liminf (fun _ ↦ 1) (dualSet L1 L2)
    (zero_mem_dualSet L1 L2) (isClosed_dualSet L1 L2) (convex_dualSet L1 L2) μ ν hμ

end IntegratedAction

#print axioms isClosed_dualSet
#print axioms convex_dualSet
#print axioms action_eq_continuousDual
#print axioms action_le_liminf

end MatrixTransport.ReactionZero.WeightedSet
