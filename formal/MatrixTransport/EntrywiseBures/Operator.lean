import MatrixTransport.ReactionZero.ClosedDomainTests

/-!
# The entrywise-divergence operator as an original `AdjointOperator`

Transport dimension `k = d n`; the flux column `(ℓ, j)` is `finProdFinEquiv (ℓ, j)`.
The adjoint is `(D*Φ)_{i,(ℓ,j)} = ∂_{x_ℓ} Φ_{ij}`: zero-order part `0`, first-order parts
placing the `ℓ`-th partial derivative in the `ℓ`-th column block.  It is a genuine instance of
the original `ClosedDomain.AdjointOperator` structure used by `Limit.Problem`; the
continuity equation is NOT re-encoded.

`velocityMatrix v` encodes a scalar velocity field: `(M * velocityMatrix (n := n) v)_{i,(ℓ,j)} =
v_ℓ M_{ij}`, which is the flux density `Q_ℓ = v_ℓ M` of a Lagrangian motion.

-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

namespace MatrixTransport.EntrywiseBures

open MatrixTransport.ReactionZero.ClosedDomain

variable {d n : ℕ}

/-- Column `(ℓ, j)` of an `n × (d n)` flux matrix. -/
abbrev col (d n : ℕ) : Fin d × Fin n ≃ Fin (d * n) := finProdFinEquiv

/-- Place an `n × n` matrix in the `ℓ`-th column block. -/
def blockPlace (d n : ℕ) (ℓ : Fin d) : Mat n →ₗ[ℝ] Matrix (Fin n) (Fin (d * n)) ℝ where
  toFun A := Matrix.of fun i c ↦
    if ((col d n).symm c).1 = ℓ then A i ((col d n).symm c).2 else 0
  map_add' A B := by
    ext i c
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' r A := by
    ext i c
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem blockPlace_apply (ℓ : Fin d) (A : Mat n) (i : Fin n) (c : Fin (d * n)) :
    blockPlace d n ℓ A i c =
      if ((col d n).symm c).1 = ℓ then A i ((col d n).symm c).2 else 0 := rfl

/-- The original constant-coefficient operator `D* Φ = (∂_{x_ℓ} Φ)_ℓ`. -/
def entrywiseDivergence (d n : ℕ) : AdjointOperator d n (d * n) where
  D0 := 0
  Dj ℓ := (blockPlace d n ℓ).toContinuousLinearMap
  D0_one := by simp

theorem entrywiseDivergence_D0 (A : Mat n) : (entrywiseDivergence d n).D0 A = 0 := by
  simp [entrywiseDivergence]

theorem blockSum_apply (Y : Fin d → Mat n) (i : Fin n) (c : Fin (d * n)) :
    (∑ ℓ, blockPlace d n ℓ (Y ℓ)) i c = Y ((col d n).symm c).1 i ((col d n).symm c).2 := by
  rw [Matrix.sum_apply]
  simp only [blockPlace_apply]
  rw [Finset.sum_ite_eq]
  simp

theorem entrywiseDivergence_apply {Ω : Set (Space d)} (φ : ClosedC1Jet Ω n) (p : Q Ω) :
    (entrywiseDivergence d n).apply φ p = ∑ ℓ, blockPlace d n ℓ (φ.dx ℓ p) := by
  simp [AdjointOperator.apply, entrywiseDivergence]

/-- The velocity-encoding matrix. -/
def velocityMatrix (v : Fin d → ℝ) : Matrix (Fin n) (Fin (d * n)) ℝ :=
  Matrix.of fun j' c ↦ if ((col d n).symm c).2 = j' then v ((col d n).symm c).1 else 0

theorem mul_velocityMatrix_apply (M : Mat n) (v : Fin d → ℝ) (i : Fin n) (c : Fin (d * n)) :
    (M * velocityMatrix (n := n) v) i c = v ((col d n).symm c).1 * M i ((col d n).symm c).2 := by
  simp only [Matrix.mul_apply, velocityMatrix, Matrix.of_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [mul_comm]

/-- The velocity Gram matrix is `|v|² I`. -/
theorem velocity_gram (v : Fin d → ℝ) :
    ReactionZero.gram (velocityMatrix (n := n) v) = (∑ ℓ, v ℓ ^ 2) • (1 : Mat n) := by
  ext j j'
  simp only [ReactionZero.gram, Matrix.mul_apply, Matrix.transpose_apply, velocityMatrix,
    Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [← (col d n).sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  by_cases h : j = j'
  · subst h
    rw [if_pos rfl, mul_one]
    refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
    rw [Finset.sum_eq_single j]
    · simp [sq]
    · intro b _ hb
      simp [hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · simp only [h, if_false, mul_zero]
    refine Finset.sum_eq_zero fun ℓ _ ↦ Finset.sum_eq_zero fun j'' _ ↦ ?_
    by_cases h1 : j'' = j
    · have h2 : j'' ≠ j' := fun h2 ↦ h (h1.symm.trans h2)
      simp [h2]
    · simp [h1]

/-- Pairing of an entrywise-divergence dual field with the Lagrangian flux density. -/
theorem frob_blocks_velocity (Y : Fin d → Mat n) (M : Mat n) (v : Fin d → ℝ) :
    ReactionZero.frob (∑ ℓ, blockPlace d n ℓ (Y ℓ)) (M * velocityMatrix (n := n) v) =
      ∑ ℓ, v ℓ * ReactionZero.frob (Y ℓ) M := by
  simp only [ReactionZero.frob, blockSum_apply, mul_velocityMatrix_apply]
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← (col d n).sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ℓ _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

#print axioms entrywiseDivergence
#print axioms entrywiseDivergence_apply
#print axioms velocity_gram
#print axioms frob_blocks_velocity

end MatrixTransport.EntrywiseBures
