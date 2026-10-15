import MatrixTransport.ReactionZero.LocalEstimates
import MatrixTransport.ReactionZero.MatrixBounds

/-!
# Positive semidefinite square roots as explicit data

The Bures formula needs a PSD square root.  To keep the core development independent of the
exact name of the square-root API at the pinned Mathlib revision, every theorem below takes a
`PSDSqrt n`: a function together with PROOFS of the three characterizing properties.  The
uniqueness field makes the square root canonical, so the Bures value does not depend on the
chosen provider (`PSDSqrt.sqrt_eq`).  `CanonicalSqrt.lean` constructs a provider from Mathlib.
A `PSDSqrt` is not an assumption of any target conclusion: it is ordinary data with proved
fields, and the final theorems are universally quantified over it.

-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

namespace MatrixTransport.EntrywiseBures

abbrev RMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Data of a positive semidefinite square root on real `n × n` matrices. -/
structure PSDSqrt (n : ℕ) where
  sqrt : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ
  posSemidef_sqrt : ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosSemidef → (sqrt A).PosSemidef
  sqrt_mul_sqrt : ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosSemidef → sqrt A * sqrt A = A
  eq_sqrt_of_mul_self : ∀ A B : Matrix (Fin n) (Fin n) ℝ, A.PosSemidef → B.PosSemidef →
    B * B = A → sqrt A = B

variable {n : ℕ}

/-- Any two providers agree on PSD matrices. -/
theorem PSDSqrt.sqrt_eq (R R' : PSDSqrt n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : R.sqrt A = R'.sqrt A :=
  R.eq_sqrt_of_mul_self A (R'.sqrt A) hA (R'.posSemidef_sqrt A hA) (R'.sqrt_mul_sqrt A hA)

theorem transpose_eq_of_posSemidef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    Aᵀ = A := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq

theorem transpose_eq_of_isHermitian {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    Aᵀ = A := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq

theorem PSDSqrt.transpose_sqrt (R : PSDSqrt n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : (R.sqrt A)ᵀ = R.sqrt A :=
  transpose_eq_of_posSemidef (R.posSemidef_sqrt A hA)

theorem PSDSqrt.gram_sqrt (R : PSDSqrt n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : ReactionZero.gram (R.sqrt A) = A := by
  unfold ReactionZero.gram
  rw [R.transpose_sqrt hA, R.sqrt_mul_sqrt A hA]

theorem frob_comm {m p : ℕ} (X Y : Matrix (Fin m) (Fin p) ℝ) :
    ReactionZero.frob X Y = ReactionZero.frob Y X := by
  unfold ReactionZero.frob
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

theorem frob_zero_right {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℝ) :
    ReactionZero.frob X 0 = 0 := by
  simp [ReactionZero.frob]

theorem frob_transpose_self (D : Matrix (Fin n) (Fin n) ℝ) :
    ReactionZero.frob Dᵀ Dᵀ = ReactionZero.frobeniusSq D := by
  unfold ReactionZero.frob ReactionZero.frobeniusSq
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    rw [Matrix.transpose_apply, sq]

/-- The trace pairing of two PSD matrices is nonnegative. -/
theorem frob_nonneg_of_posSemidef (R : PSDSqrt n) {S M : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) (hM : M.PosSemidef) : 0 ≤ ReactionZero.frob S M := by
  have h := ReactionZero.frob_gram_nonneg hS (R.sqrt M)
  rw [R.gram_sqrt hM, frob_comm] at h
  exact h

#print axioms PSDSqrt.sqrt_eq
#print axioms frob_nonneg_of_posSemidef

end MatrixTransport.EntrywiseBures
