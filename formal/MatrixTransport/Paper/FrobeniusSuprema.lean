import MatrixTransport.PartialWeights.JointWeights

/-! The exact Frobenius-squared suprema used in the varying-weight mass correction. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace MatrixTransport.Paper.FrobeniusSuprema

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {m p : ℕ}

def squaredField (B : C(X, Matrix (Fin m) (Fin p) ℝ)) : C(X, ℝ) :=
  ⟨fun x ↦ ReactionZero.frobeniusSq (B x), ReactionZero.continuous_frobeniusSq.comp B.continuous⟩

theorem norm_squaredField_eq_iSup (B : C(X, Matrix (Fin m) (Fin p) ℝ)) :
    ‖squaredField B‖ = ⨆ x, ReactionZero.frobeniusSq (B x) := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  congr 1
  funext x
  rw [Real.norm_eq_abs]
  change |ReactionZero.frobeniusSq (B x)| = ReactionZero.frobeniusSq (B x)
  exact abs_of_nonneg (ReactionZero.frobeniusSq_nonneg (B x))

theorem squaredField_le_norm (B : C(X, Matrix (Fin m) (Fin p) ℝ)) (x : X) :
    ReactionZero.frobeniusSq (B x) ≤ ‖squaredField B‖ :=
  (squaredField B).apply_le_norm x

#print axioms norm_squaredField_eq_iSup
#print axioms squaredField_le_norm

end MatrixTransport.Paper.FrobeniusSuprema
