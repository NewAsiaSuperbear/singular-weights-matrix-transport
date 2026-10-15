import MatrixTransport.Paper.NativeSeparationSqrt
import MatrixTransport.Paper.ExampleBridges
import MatrixTransport.Paper.ExampleAtomBridges
import MatrixTransport.Paper.ExampleFluxBridges

/-! # Literal quadratic maximizations used in the expanded examples

The strict positive-mass hypotheses apply to the displayed pointwise quotients. The native
path theorems already handle exceptional endpoint times through almost-everywhere integration.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal Matrix BigOperators

namespace LiZouTransport.ExpandedScalarExamples

/-- The scalar square-root sum in the two-dimensional trace calculation. -/
theorem square_sqrt_sum (l₁ l₂ : ℝ) (h1 : 0 ≤ l₁) (h2 : 0 ≤ l₂) :
    (Real.sqrt l₁ + Real.sqrt l₂) ^ 2 = l₁ + l₂ + 2 * Real.sqrt (l₁ * l₂) := by
  rw [Real.sqrt_mul h1]
  nlinarith [Real.sq_sqrt h1, Real.sq_sqrt h2]

/-- The literal endpoint matrix in the eigenbasis of the rotating reaction weight. -/
theorem rotated_endpoint_one_display (θ : ℝ) :
    (MatrixTransport.Paper.RotatingReaction.rotation θ).transpose *
        MatrixTransport.Paper.RotatingReaction.endpoint1 *
        MatrixTransport.Paper.RotatingReaction.rotation θ =
      !![2 - Real.sin θ ^ 2, -Real.sin θ * Real.cos θ;
        -Real.sin θ * Real.cos θ, 1 + Real.sin θ ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatrixTransport.Paper.RotatingReaction.rotation,
      MatrixTransport.Paper.RotatingReaction.endpoint1, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The first whitened endpoint is the printed diagonal in the same eigenbasis. -/
theorem rotated_whitened_zero_display (ε θ : ℝ) (hε : 0 < ε) :
    (MatrixTransport.Paper.RotatingReaction.rotation θ).transpose *
        LiZouTransport.ExampleBridges.actualX0 ε θ *
        MatrixTransport.Paper.RotatingReaction.rotation θ = !![1, 0; 0, ε⁻¹ ^ 2] := by
  rw [LiZouTransport.ExampleBridges.actualX0,
    MatrixTransport.Paper.RotatingReaction.inverse_endpoint0 hε]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc
    (MatrixTransport.Paper.RotatingReaction.rotation θ).transpose,
    MatrixTransport.Paper.RotatingReaction.transpose_rotation_mul,
    Matrix.one_mul, Matrix.mul_one]
  rfl

/-- The second whitened endpoint is exactly the stated diagonal congruence. -/
theorem rotated_whitened_one_display (ε θ : ℝ) (hε : 0 < ε) :
    (MatrixTransport.Paper.RotatingReaction.rotation θ).transpose *
        LiZouTransport.ExampleBridges.actualX1 ε θ *
        MatrixTransport.Paper.RotatingReaction.rotation θ =
      !![1, 0; 0, ε⁻¹] *
        ((MatrixTransport.Paper.RotatingReaction.rotation θ).transpose *
          MatrixTransport.Paper.RotatingReaction.endpoint1 *
          MatrixTransport.Paper.RotatingReaction.rotation θ) * !![1, 0; 0, ε⁻¹] := by
  rw [LiZouTransport.ExampleBridges.actualX1,
    MatrixTransport.Paper.RotatingReaction.inverse_endpoint1 hε]
  have hcancel (W : Matrix (Fin 2) (Fin 2) ℝ) :
      (MatrixTransport.Paper.RotatingReaction.rotation θ).transpose *
        (MatrixTransport.Paper.RotatingReaction.rotation θ * W *
          (MatrixTransport.Paper.RotatingReaction.rotation θ).transpose) *
        MatrixTransport.Paper.RotatingReaction.rotation θ = W := by
    calc
      _ = ((MatrixTransport.Paper.RotatingReaction.rotation θ).transpose *
          MatrixTransport.Paper.RotatingReaction.rotation θ) * W *
          ((MatrixTransport.Paper.RotatingReaction.rotation θ).transpose *
          MatrixTransport.Paper.RotatingReaction.rotation θ) := by
        simp only [Matrix.mul_assoc]
      _ = W := by
        rw [MatrixTransport.Paper.RotatingReaction.transpose_rotation_mul,
          Matrix.one_mul, Matrix.mul_one]
  rw [hcancel]
  rfl

/-- Completing the square without changing the original normalization. -/
theorem scalar_quadratic_square (m z c : ℝ) (hm : 0 < m) :
    z * c - m * c ^ 2 / 2 = z ^ 2 / (2 * m) - m * (c - z / m) ^ 2 / 2 := by
  field_simp
  ring

/-- The literal scalar quadratic upper bound. -/
theorem scalar_quadratic_le (m z c : ℝ) (hm : 0 < m) :
    z * c - m * c ^ 2 / 2 ≤ z ^ 2 / (2 * m) := by
  rw [scalar_quadratic_square m z c hm]
  have h := mul_nonneg hm.le (sq_nonneg (c - z / m))
  linarith

/-- The maximum occurs at the displayed optimizer. -/
theorem scalar_quadratic_optimizer (m z : ℝ) (hm : 0 < m) :
    z * (z / m) - m * (z / m) ^ 2 / 2 = z ^ 2 / (2 * m) := by
  rw [scalar_quadratic_square m z (z / m) hm]
  simp

/-- The scalar supremum in the atomic reaction calculation is a genuine attained maximum. -/
theorem scalar_quadratic_isGreatest (m z : ℝ) (hm : 0 < m) :
    IsGreatest (Set.range (fun c : ℝ ↦ z * c - m * c ^ 2 / 2)) (z ^ 2 / (2 * m)) := by
  constructor
  · exact ⟨z / m, scalar_quadratic_optimizer m z hm⟩
  · rintro _ ⟨c, rfl⟩
    exact scalar_quadratic_le m z c hm

/-- The exact real-valued supremum as printed in the examples. -/
theorem scalar_quadratic_supremum (m z : ℝ) (hm : 0 < m) :
    sSup (Set.range (fun c : ℝ ↦ z * c - m * c ^ 2 / 2)) = z ^ 2 / (2 * m) :=
  (scalar_quadratic_isGreatest m z hm).isLUB.csSup_eq (Set.range_nonempty _)

/-- The same support supremum in the extended nonnegative-real convention of the action. -/
theorem scalar_quadratic_support (m z : ℝ) (hm : 0 < m) :
    (⨆ c : ℝ, ENNReal.ofReal (z * c - m * c ^ 2 / 2)) =
      ENNReal.ofReal (z ^ 2 / (2 * m)) := by
  apply le_antisymm
  · exact iSup_le fun c ↦ ENNReal.ofReal_le_ofReal (scalar_quadratic_le m z c hm)
  · have h := le_iSup (fun c : ℝ ↦ ENNReal.ofReal (z * c - m * c ^ 2 / 2)) (z / m)
    rwa [scalar_quadratic_optimizer m z hm] at h

/-- Exact cancellation for annihilation away from its exceptional terminal time. -/
theorem annihilation_scalar_cost (t : ℝ) (ht : t < 1) :
    (-2 * (1 - t)) ^ 2 / (2 * (1 - t) ^ 2) = (2 : ℝ) := by
  have h : 1 - t ≠ 0 := by linarith
  field_simp

/-- Exact cancellation for creation away from its exceptional initial time. -/
theorem creation_scalar_cost (t : ℝ) (ht : 0 < t) :
    (2 * t) ^ 2 / (2 * t ^ 2) = (2 : ℝ) := by
  field_simp

/-- Expansion of the identity-weight diagonal reaction objective. -/
theorem diagonal_reaction_objective (m z : ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) :
    MatrixTransport.ReactionZero.frob C !![0, 0; 0, z] -
      Matrix.trace (C * C.transpose * !![1, 0; 0, m]) / 2 =
    z * C 1 1 - (C 0 0 ^ 2 + C 0 1 ^ 2) / 2 -
      m * (C 1 0 ^ 2 + C 1 1 ^ 2) / 2 := by
  simp [MatrixTransport.ReactionZero.frob, Matrix.trace, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two]
  ring

/-- The diagonal reaction objective is bounded by the exact scalar cost. -/
theorem diagonal_reaction_objective_le (m z : ℝ) (hm : 0 < m)
    (C : Matrix (Fin 2) (Fin 2) ℝ) :
    z * C 1 1 - (C 0 0 ^ 2 + C 0 1 ^ 2) / 2 -
      m * (C 1 0 ^ 2 + C 1 1 ^ 2) / 2 ≤ z ^ 2 / (2 * m) := by
  have h := scalar_quadratic_le m z (C 1 1) hm
  nlinarith [sq_nonneg (C 0 0), sq_nonneg (C 0 1),
    mul_nonneg hm.le (sq_nonneg (C 1 0))]

/-- The displayed diagonal optimizer attains the bound, with the other entries zero. -/
theorem diagonal_reaction_objective_optimizer (m z : ℝ) (hm : 0 < m) :
    z * (z / m) - (0 ^ 2 + 0 ^ 2 : ℝ) / 2 -
      m * (0 ^ 2 + (z / m) ^ 2) / 2 = z ^ 2 / (2 * m) := by
  simpa using scalar_quadratic_optimizer m z hm

/-- The identity-weight diagonal objective has the displayed exact supremum. -/
theorem diagonal_reaction_supremum (m z : ℝ) (hm : 0 < m) :
    sSup (Set.range (fun C : Matrix (Fin 2) (Fin 2) ℝ ↦
      z * C 1 1 - (C 0 0 ^ 2 + C 0 1 ^ 2) / 2 -
        m * (C 1 0 ^ 2 + C 1 1 ^ 2) / 2)) = z ^ 2 / (2 * m) := by
  have h : IsGreatest (Set.range (fun C : Matrix (Fin 2) (Fin 2) ℝ ↦
      z * C 1 1 - (C 0 0 ^ 2 + C 0 1 ^ 2) / 2 -
        m * (C 1 0 ^ 2 + C 1 1 ^ 2) / 2)) (z ^ 2 / (2 * m)) := by
    constructor
    · refine ⟨!![0, 0; 0, z / m], ?_⟩
      simpa using diagonal_reaction_objective_optimizer m z hm
    · rintro _ ⟨C, rfl⟩
      exact diagonal_reaction_objective_le m z hm C
  exact h.isLUB.csSup_eq (Set.range_nonempty _)

/-- Literal expansion of the singular-weight objective in the rotating reaction example. -/
theorem singular_reaction_objective (m z : ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) :
    MatrixTransport.ReactionZero.frob C !![z, 0; 0, 0] -
      Matrix.trace (C * !![1, 0; 0, 0] ^ 2 * C.transpose * !![m, 0; 0, 1]) / 2 =
    z * C 0 0 - m * C 0 0 ^ 2 / 2 - C 1 0 ^ 2 / 2 := by
  simp [MatrixTransport.ReactionZero.frob, Matrix.trace, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two, Fin.sum_univ_two]
  ring

/-- The two-entry singular-weight objective in the singular reaction example. -/
theorem singular_reaction_objective_le (m z c11 c21 : ℝ) (hm : 0 < m) :
    z * c11 - m * c11 ^ 2 / 2 - c21 ^ 2 / 2 ≤ z ^ 2 / (2 * m) := by
  have h := scalar_quadratic_le m z c11 hm
  linarith [sq_nonneg c21]

/-- The singular-weight objective attains its maximum at the displayed entries. -/
theorem singular_reaction_objective_optimizer (m z : ℝ) (hm : 0 < m) :
    z * (z / m) - m * (z / m) ^ 2 / 2 - (0 : ℝ) ^ 2 / 2 = z ^ 2 / (2 * m) := by
  simpa using scalar_quadratic_optimizer m z hm

/-- The singular-weight diagonal objective also has the printed exact supremum. -/
theorem singular_reaction_supremum (m z : ℝ) (hm : 0 < m) :
    sSup (Set.range (fun C : Matrix (Fin 2) (Fin 2) ℝ ↦
      z * C 0 0 - m * C 0 0 ^ 2 / 2 - C 1 0 ^ 2 / 2)) = z ^ 2 / (2 * m) := by
  have h : IsGreatest (Set.range (fun C : Matrix (Fin 2) (Fin 2) ℝ ↦
      z * C 0 0 - m * C 0 0 ^ 2 / 2 - C 1 0 ^ 2 / 2)) (z ^ 2 / (2 * m)) := by
    constructor
    · refine ⟨!![z / m, 0; 0, 0], ?_⟩
      simpa using singular_reaction_objective_optimizer m z hm
    · rintro _ ⟨C, rfl⟩
      exact singular_reaction_objective_le m z (C 0 0) (C 1 0) hm
  exact h.isLUB.csSup_eq (Set.range_nonempty _)

/-- The factor curve's ratio is exactly its constant reaction cost at positive factor. -/
theorem factor_reaction_ratio (a p : ℝ) (hp : 0 < p) :
    (2 * a * p) ^ 2 / (2 * p ^ 2) = 2 * a ^ 2 := by
  field_simp

/-- The scalar quadratic is the actual original zero-flux support cost, for any transport weight. -/
theorem scalar_original_zeroFlux_cost {k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ)
    (m z : ℝ) (hm : 0 < m) :
    MatrixTransport.ReactionZero.cost L (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (MatrixTransport.ReactionZero.pack (fun _ _ ↦ m)
        (0 : Matrix (Fin 1) (Fin k) ℝ) (fun _ _ ↦ z)) =
      ENNReal.ofReal (z ^ 2 / (2 * m)) := by
  open MatrixTransport.ReactionZero in
  apply le_antisymm
  · unfold MatrixTransport.ReactionZero.cost MatrixTransport.supportFunction
    refine iSup_le fun a ↦ iSup_le fun ha ↦ ENNReal.ofReal_le_ofReal ?_
    erw [MatrixTransport.ReactionZero.weightedPair_pack]
    simp only [MatrixTransport.ReactionZero.frob, Fin.sum_univ_one,
      Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    have h0 := ha.2.diag_nonneg (i := (0 : Fin 1))
    have hB := (MatrixTransport.ReactionZero.posSemidef_gram
      (MatrixTransport.ReactionZero.flux a * L)).diag_nonneg (i := (0 : Fin 1))
    have hC : MatrixTransport.ReactionZero.gram
        (MatrixTransport.ReactionZero.reaction a * (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0 =
        MatrixTransport.ReactionZero.reaction a 0 0 ^ 2 := by
      simp [MatrixTransport.ReactionZero.gram, Matrix.mul_apply, pow_two]
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul] at h0
    rw [hC] at h0
    have hA : MatrixTransport.ReactionZero.mass a 0 0 ≤
        -(MatrixTransport.ReactionZero.reaction a 0 0 ^ 2) / 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hA hm.le
    have hq := scalar_quadratic_le m z (MatrixTransport.ReactionZero.reaction a 0 0) hm
    nlinarith
  · let s := z / m
    have ha := MatrixTransport.ReactionZero.pack_reaction_mem_dualSet L
      (1 : Matrix (Fin 1) (Fin 1) ℝ) s (1 : Matrix (Fin 1) (Fin 1) ℝ)
    have hf := MatrixTransport.ReactionZero.cost_fenchel L
      (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (MatrixTransport.ReactionZero.pack (fun _ _ ↦ m)
        (0 : Matrix (Fin 1) (Fin k) ℝ) (fun _ _ ↦ z)) _ ha
    have he : MatrixTransport.weightedPair (fun _ ↦ 1)
        (MatrixTransport.ReactionZero.pack
          (-(s ^ 2 / 2) • MatrixTransport.ReactionZero.gram
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1))
          (0 : Matrix (Fin 1) (Fin k) ℝ) (s • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
        (MatrixTransport.ReactionZero.pack (fun _ _ ↦ m)
          (0 : Matrix (Fin 1) (Fin k) ℝ) (fun _ _ ↦ z)) = z ^ 2 / (2 * m) := by
      erw [MatrixTransport.ReactionZero.weightedPair_pack]
      simp [MatrixTransport.ReactionZero.mass_pack, MatrixTransport.ReactionZero.flux_pack,
        MatrixTransport.ReactionZero.reaction_pack, MatrixTransport.ReactionZero.frob,
        MatrixTransport.ReactionZero.gram, s]
      linear_combination scalar_quadratic_optimizer m z hm
    rwa [he] at hf

/-- The singular reaction example's diagonal cost in the actual original support function. -/
theorem singular_diagonal_original_cost {k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ)
    (m z : ℝ) (hm : 0 < m) :
    MatrixTransport.ReactionZero.cost L !![1, 0; 0, 0]
      (MatrixTransport.ReactionZero.pack !![m, 0; 0, 1]
        (0 : Matrix (Fin 2) (Fin k) ℝ) !![z, 0; 0, 0]) =
      ENNReal.ofReal (z ^ 2 / (2 * m)) := by
  apply le_antisymm
  · unfold MatrixTransport.ReactionZero.cost MatrixTransport.supportFunction
    refine iSup_le fun a ↦ iSup_le fun ha ↦ ENNReal.ofReal_le_ofReal ?_
    rw [MatrixTransport.ReactionZero.weightedPair_pack]
    simp [MatrixTransport.ReactionZero.frob, Fin.sum_univ_two]
    have h0 := ha.2.diag_nonneg (i := (0 : Fin 2))
    have h1 := ha.2.diag_nonneg (i := (1 : Fin 2))
    have hB0 := (MatrixTransport.ReactionZero.posSemidef_gram
      (MatrixTransport.ReactionZero.flux a * L)).diag_nonneg (i := (0 : Fin 2))
    have hB1 := (MatrixTransport.ReactionZero.posSemidef_gram
      (MatrixTransport.ReactionZero.flux a * L)).diag_nonneg (i := (1 : Fin 2))
    have hC (i : Fin 2) : MatrixTransport.ReactionZero.gram
        (MatrixTransport.ReactionZero.reaction a * !![1, 0; 0, 0]) i i =
        MatrixTransport.ReactionZero.reaction a i 0 ^ 2 := by
      simp [MatrixTransport.ReactionZero.gram, Matrix.mul_apply, Fin.sum_univ_two, pow_two]
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul] at h0 h1
    rw [hC] at h0 h1
    have hA0 : MatrixTransport.ReactionZero.mass a 0 0 ≤
        -(MatrixTransport.ReactionZero.reaction a 0 0 ^ 2) / 2 := by linarith
    have hA1 : MatrixTransport.ReactionZero.mass a 1 1 ≤
        -(MatrixTransport.ReactionZero.reaction a 1 0 ^ 2) / 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hA0 hm.le
    have hq := singular_reaction_objective_le m z
      (MatrixTransport.ReactionZero.reaction a 0 0)
      (MatrixTransport.ReactionZero.reaction a 1 0) hm
    nlinarith
  · let s := z / m
    have ha := MatrixTransport.ReactionZero.pack_reaction_mem_dualSet L
      !![1, 0; 0, 0] s !![1, 0; 0, 0]
    have hf := MatrixTransport.ReactionZero.cost_fenchel L !![1, 0; 0, 0]
      (MatrixTransport.ReactionZero.pack !![m, 0; 0, 1]
        (0 : Matrix (Fin 2) (Fin k) ℝ) !![z, 0; 0, 0]) _ ha
    have hgram : MatrixTransport.ReactionZero.gram
        ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, 0]) =
        !![1, 0; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [MatrixTransport.ReactionZero.gram, Matrix.mul_apply,
          Matrix.transpose_apply, Fin.sum_univ_two]
    have he : MatrixTransport.weightedPair (fun _ ↦ 1)
        (MatrixTransport.ReactionZero.pack
          (-(s ^ 2 / 2) • MatrixTransport.ReactionZero.gram
            (!![1, 0; 0, 0] * !![1, 0; 0, 0]))
          (0 : Matrix (Fin 2) (Fin k) ℝ) (s • !![1, 0; 0, 0]))
        (MatrixTransport.ReactionZero.pack !![m, 0; 0, 1]
          (0 : Matrix (Fin 2) (Fin k) ℝ) !![z, 0; 0, 0]) = z ^ 2 / (2 * m) := by
      rw [hgram, MatrixTransport.ReactionZero.weightedPair_pack]
      simp [MatrixTransport.ReactionZero.mass_pack, MatrixTransport.ReactionZero.flux_pack,
        MatrixTransport.ReactionZero.reaction_pack, MatrixTransport.ReactionZero.frob,
        Fin.sum_univ_two, s]
      linear_combination scalar_quadratic_optimizer m z hm
    rwa [he] at hf

/-- Exact local original identity-weight support cost for the diagonal reaction density. -/
theorem identity_diagonal_original_cost (m z : ℝ) (hm : 0 < m) :
    MatrixTransport.matrixCost 1
      (MatrixTransport.packTriplet (MatrixTransport.density (m - 1))
        (0 : MatrixTransport.Flux 1) (z • MatrixTransport.E)) =
      ENNReal.ofReal (z ^ 2 / (2 * m)) := by
  have hp := Real.sqrt_pos.mpr hm
  have hsq := Real.sq_sqrt hm.le
  have h := LiZouTransport.NativeSeparation.matrixCost_sqrt_reaction
    (Real.sqrt m) (z / (2 * Real.sqrt m)) hp
  have hz : 2 * Real.sqrt m * (z / (2 * Real.sqrt m)) = z := by
    field_simp
  rw [hsq, hz] at h
  rw [h]
  congr 1
  field_simp
  nlinarith [hsq]

/-- The four-entry flux quadratic upper bound in the noncompactness example. -/
theorem matrix_quadratic_le (τ : ℝ) (hτ : 0 < τ)
    (z B : Matrix (Fin 2) (Fin 2) ℝ) :
    MatrixTransport.ReactionZero.frob B z -
      τ ^ 2 * MatrixTransport.ReactionZero.frobeniusSq B / 2 ≤
      MatrixTransport.ReactionZero.frobeniusSq z / (2 * τ ^ 2) := by
  have hm : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have h00 := scalar_quadratic_le (τ ^ 2) (z 0 0) (B 0 0) hm
  have h01 := scalar_quadratic_le (τ ^ 2) (z 0 1) (B 0 1) hm
  have h10 := scalar_quadratic_le (τ ^ 2) (z 1 0) (B 1 0) hm
  have h11 := scalar_quadratic_le (τ ^ 2) (z 1 1) (B 1 1) hm
  have h := add_le_add (add_le_add h00 h01) (add_le_add h10 h11)
  simp only [MatrixTransport.ReactionZero.frob,
    MatrixTransport.ReactionZero.frobeniusSq, Fin.sum_univ_two]
  simp only [add_div]
  nlinarith only [h]

/-- The displayed matrix optimizer is `B=z/τ²`, entry by entry. -/
theorem matrix_quadratic_optimizer (τ : ℝ) (hτ : 0 < τ)
    (z : Matrix (Fin 2) (Fin 2) ℝ) :
    MatrixTransport.ReactionZero.frob ((1 / τ ^ 2) • z) z -
      τ ^ 2 * MatrixTransport.ReactionZero.frobeniusSq ((1 / τ ^ 2) • z) / 2 =
      MatrixTransport.ReactionZero.frobeniusSq z / (2 * τ ^ 2) := by
  simp only [MatrixTransport.ReactionZero.frob,
    MatrixTransport.ReactionZero.frobeniusSq, Matrix.smul_apply, smul_eq_mul,
    Fin.sum_univ_two]
  field_simp
  ring

/-- The original four-entry flux quadratic has the stated exact supremum. -/
theorem matrix_quadratic_supremum (τ : ℝ) (hτ : 0 < τ)
    (z : Matrix (Fin 2) (Fin 2) ℝ) :
    sSup (Set.range (fun B : Matrix (Fin 2) (Fin 2) ℝ ↦
      MatrixTransport.ReactionZero.frob B z -
        τ ^ 2 * MatrixTransport.ReactionZero.frobeniusSq B / 2)) =
      MatrixTransport.ReactionZero.frobeniusSq z / (2 * τ ^ 2) := by
  have h : IsGreatest (Set.range (fun B : Matrix (Fin 2) (Fin 2) ℝ ↦
      MatrixTransport.ReactionZero.frob B z -
        τ ^ 2 * MatrixTransport.ReactionZero.frobeniusSq B / 2))
      (MatrixTransport.ReactionZero.frobeniusSq z / (2 * τ ^ 2)) := by
    constructor
    · exact ⟨(1 / τ ^ 2) • z, matrix_quadratic_optimizer τ hτ z⟩
    · rintro _ ⟨B, rfl⟩
      exact matrix_quadratic_le τ hτ z B
  exact h.isLUB.csSup_eq (Set.range_nonempty _)

/-- The closed time interval differs from its interior by null endpoint sets. -/
theorem ae_time_interior :
    ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1), t ∈ Set.Ioo 0 1 := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
    MeasureTheory.ae_restrict_of_ae (MeasureTheory.Measure.ae_ne
      MeasureTheory.volume (0 : ℝ)),
    MeasureTheory.ae_restrict_of_ae (MeasureTheory.Measure.ae_ne
      MeasureTheory.volume (1 : ℝ))] with t ht h0 h1
  exact ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩

/-- Both scalar reaction quotients equal two almost everywhere in the actual time reference. -/
theorem atom_scalar_costs_ae :
    ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1),
      (-2 * (1 - t)) ^ 2 / (2 * (1 - t) ^ 2) = (2 : ℝ) ∧
      (2 * t) ^ 2 / (2 * t ^ 2) = (2 : ℝ) := by
  filter_upwards [ae_time_interior] with t ht
  exact ⟨annihilation_scalar_cost t ht.2, creation_scalar_cost t ht.1⟩

#print axioms scalar_quadratic_supremum
#print axioms square_sqrt_sum
#print axioms rotated_endpoint_one_display
#print axioms rotated_whitened_zero_display
#print axioms rotated_whitened_one_display
#print axioms scalar_quadratic_support
#print axioms diagonal_reaction_objective
#print axioms diagonal_reaction_objective_le
#print axioms diagonal_reaction_supremum
#print axioms singular_reaction_objective
#print axioms singular_reaction_objective_le
#print axioms singular_reaction_supremum
#print axioms factor_reaction_ratio
#print axioms identity_diagonal_original_cost
#print axioms scalar_original_zeroFlux_cost
#print axioms singular_diagonal_original_cost
#print axioms matrix_quadratic_supremum
#print axioms ae_time_interior
#print axioms atom_scalar_costs_ae

end LiZouTransport.ExpandedScalarExamples
