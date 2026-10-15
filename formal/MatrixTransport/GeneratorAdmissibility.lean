import MatrixTransport.Continuity

set_option autoImplicit false

/-!
# Generator admissibility

`fullL0 = diag(1, -1)` and `fullL1 = [[0, 1], [1, 0]]` are the actual admissible generators for the
selected full-flux model: their common commutant in real `2 × 2` matrices is exactly the scalars.
No Hermiticity hypothesis on `X` is needed.
-/

namespace MatrixTransport

theorem full_generators_commutant_scalar (X : Mat2)
    (h0 : fullL0 * X = X * fullL0) (h1 : fullL1 * X = X * fullL1) :
    ∃ c : ℝ, X = c • (1 : Mat2) := by
  have h01 : X 0 1 = 0 := by
    have a := congrArg (fun M : Mat2 => M 0 1) h0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at a
    simp [fullL0] at a
    linarith
  have h10 : X 1 0 = 0 := by
    have a := congrArg (fun M : Mat2 => M 1 0) h0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at a
    simp [fullL0] at a
    linarith
  have h11 : X 1 1 = X 0 0 := by
    have a := congrArg (fun M : Mat2 => M 0 1) h1
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at a
    simp [fullL1] at a
    linarith
  refine ⟨X 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h01, h10, h11]

theorem full_generators_commutant_iff (X : Mat2) :
    (fullL0 * X = X * fullL0 ∧ fullL1 * X = X * fullL1) ↔
      ∃ c : ℝ, X = c • (1 : Mat2) := by
  constructor
  · rintro ⟨h0, h1⟩
    exact full_generators_commutant_scalar X h0 h1
  · rintro ⟨c, rfl⟩
    constructor <;> simp [Matrix.mul_smul, Matrix.smul_mul]

#print axioms full_generators_commutant_scalar
#print axioms full_generators_commutant_iff

end MatrixTransport
