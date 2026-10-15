import MatrixTransport.EntrywiseBures.BuresAlgebra
import MatrixTransport.EntrywiseBures.CanonicalSqrt
import MatrixTransport.EntrywiseBures.DualCertificate
import MatrixTransport.Paper.RotatingReactionLimits
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Two-dimensional algebra for the existing rotating-reaction example -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Filter Topology
namespace MatrixTransport.Paper.RotatingReaction

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

theorem trace_sq_identity (A : Mat) : A.trace ^ 2 = (A * A).trace + 2 * A.det := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.det_fin_two,
    Fin.sum_univ_two]
  ring

/-- The square-root trace formula used to evaluate the Bures term in dimension two. -/
theorem trace_sqrt (R : EntrywiseBures.PSDSqrt 2) {A : Mat} (hA : A.PosSemidef) :
    (R.sqrt A).trace = Real.sqrt (A.trace + 2 * Real.sqrt A.det) := by
  have hprovider := R.sqrt_eq (EntrywiseBures.canonicalPSDSqrt 2) hA
  have hdet : (R.sqrt A).det = Real.sqrt A.det := by
    rw [hprovider]
    simpa [EntrywiseBures.canonicalPSDSqrt, RCLike.sqrt_of_nonneg hA.det_nonneg] using hA.det_sqrt
  have hsq := trace_sq_identity (R.sqrt A)
  rw [R.sqrt_mul_sqrt A hA, hdet] at hsq
  rw [← hsq, Real.sqrt_sq (R.posSemidef_sqrt A hA).trace_nonneg]

/-- A diagonal matrix with a free second diagonal entry. -/
def diagonal (b : ℝ) : Mat := !![1, 0; 0, b]

/-- Planar rotation with the same orientation as the manuscript. -/
def rotation (θ : ℝ) : Mat := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rotation_mul_transpose (θ : ℝ) : rotation θ * (rotation θ)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem transpose_rotation_mul (θ : ℝ) : (rotation θ)ᵀ * rotation θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem trace_orthogonal_conjugate (θ : ℝ) (A : Mat) :
    (rotation θ * A * (rotation θ)ᵀ).trace = A.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, transpose_rotation_mul,
    Matrix.one_mul]

def reactionWeight (ε θ : ℝ) : Mat :=
  rotation θ * diagonal ε * (rotation θ)ᵀ

def inverseWeight (ε θ : ℝ) : Mat :=
  rotation θ * diagonal ε⁻¹ * (rotation θ)ᵀ

theorem diagonal_mul_inv {ε : ℝ} (hε : ε ≠ 0) :
    diagonal ε * diagonal ε⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.mul_apply, Fin.sum_univ_two, hε]

theorem weight_mul_inverse {ε θ : ℝ} (hε : ε ≠ 0) :
    reactionWeight ε θ * inverseWeight ε θ = 1 := by
  unfold reactionWeight inverseWeight
  calc
    rotation θ * diagonal ε * (rotation θ)ᵀ *
        (rotation θ * diagonal ε⁻¹ * (rotation θ)ᵀ) =
        rotation θ * (diagonal ε * diagonal ε⁻¹) * (rotation θ)ᵀ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (rotation θ)ᵀ,
        transpose_rotation_mul, Matrix.one_mul]
    _ = 1 := by rw [diagonal_mul_inv hε, Matrix.mul_one, rotation_mul_transpose]

theorem inverseWeight_eq {ε θ : ℝ} (hε : ε ≠ 0) :
    (reactionWeight ε θ)⁻¹ = inverseWeight ε θ := by
  exact Matrix.inv_eq_right_inv (weight_mul_inverse hε)

def endpoint0 : Mat := 1
def endpoint1 : Mat := !![2, 0; 0, 1]

/-- Whitened matrices after a common orthogonal change of basis. -/
def whitened0 (ε : ℝ) : Mat := diagonal (ε⁻¹ ^ 2)
def whitened1 (ε θ : ℝ) : Mat :=
  diagonal ε⁻¹ * ((rotation θ)ᵀ * endpoint1 * rotation θ) * diagonal ε⁻¹

theorem trace_sum_whitened (ε θ : ℝ) :
    (whitened0 ε).trace + (whitened1 ε θ).trace =
      3 - Real.sin θ ^ 2 + (2 + Real.sin θ ^ 2) * ε⁻¹ ^ 2 := by
  simp only [whitened0, whitened1, diagonal, rotation, endpoint1, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.of_apply]
  norm_num
  simp only [← inv_pow]
  linear_combination (2 + ε⁻¹ ^ 2) * Real.sin_sq_add_cos_sq θ

theorem trace_product_whitened (ε θ : ℝ) :
    (whitened0 ε * whitened1 ε θ).trace =
      2 - Real.sin θ ^ 2 + (1 + Real.sin θ ^ 2) * ε⁻¹ ^ 4 := by
  simp only [whitened0, whitened1, diagonal, rotation, endpoint1, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.of_apply]
  norm_num
  simp only [← inv_pow]
  linear_combination (2 + ε⁻¹ ^ 4) * Real.sin_sq_add_cos_sq θ

theorem det_product_whitened (ε θ : ℝ) :
    (whitened0 ε).det * (whitened1 ε θ).det = 2 * ε⁻¹ ^ 4 := by
  simp only [whitened0, whitened1, diagonal, rotation, endpoint1, Matrix.det_fin_two,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.of_apply]
  norm_num
  simp only [← inv_pow]
  linear_combination 2 * ε⁻¹ ^ 4 * (Real.sin θ ^ 2 + Real.cos θ ^ 2 + 1) *
    Real.sin_sq_add_cos_sq θ

theorem diagonal_posSemidef {b : ℝ} (hb : 0 ≤ b) : (diagonal b).PosSemidef := by
  have heq : diagonal b = Matrix.diagonal ![1, b] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.diagonal]
  rw [heq, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp [hb]

theorem endpoint1_posSemidef : endpoint1.PosSemidef := by
  have heq : endpoint1 = Matrix.diagonal ![2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [endpoint1, Matrix.diagonal]
  rw [heq, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem conjugate_posSemidef (θ : ℝ) {A : Mat} (hA : A.PosSemidef) :
    (rotation θ * A * (rotation θ)ᵀ).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hA.mul_mul_conjTranspose_same (rotation θ)

theorem sqrt_conjugate (R : EntrywiseBures.PSDSqrt 2) (θ : ℝ) {A : Mat}
    (hA : A.PosSemidef) :
    R.sqrt (rotation θ * A * (rotation θ)ᵀ) =
      rotation θ * R.sqrt A * (rotation θ)ᵀ := by
  refine R.eq_sqrt_of_mul_self _ _ (conjugate_posSemidef θ hA)
    (conjugate_posSemidef θ (R.posSemidef_sqrt A hA)) ?_
  calc
    rotation θ * R.sqrt A * (rotation θ)ᵀ *
        (rotation θ * R.sqrt A * (rotation θ)ᵀ) =
        rotation θ * (R.sqrt A * R.sqrt A) * (rotation θ)ᵀ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (rotation θ)ᵀ,
        transpose_rotation_mul, Matrix.one_mul]
    _ = rotation θ * A * (rotation θ)ᵀ := by rw [R.sqrt_mul_sqrt A hA]

theorem buresSq_conjugate (R : EntrywiseBures.PSDSqrt 2) (θ : ℝ) {X Y : Mat}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    EntrywiseBures.buresSq R (rotation θ * X * (rotation θ)ᵀ)
      (rotation θ * Y * (rotation θ)ᵀ) = EntrywiseBures.buresSq R X Y := by
  have hinner : (R.sqrt X * Y * R.sqrt X).PosSemidef :=
    EntrywiseBures.posSemidef_congr_symm (R.transpose_sqrt hX) hY
  have heq : (rotation θ * R.sqrt X * (rotation θ)ᵀ) *
      (rotation θ * Y * (rotation θ)ᵀ) *
      (rotation θ * R.sqrt X * (rotation θ)ᵀ) =
      rotation θ * (R.sqrt X * Y * R.sqrt X) * (rotation θ)ᵀ := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (rotation θ)ᵀ,
      transpose_rotation_mul, Matrix.one_mul]
  unfold EntrywiseBures.buresSq
  rw [sqrt_conjugate R θ hX, heq, sqrt_conjugate R θ hinner,
    trace_orthogonal_conjugate, trace_orthogonal_conjugate, trace_orthogonal_conjugate]

theorem whitened0_posSemidef (ε : ℝ) : (whitened0 ε).PosSemidef :=
  diagonal_posSemidef (sq_nonneg _)

theorem whitened1_posSemidef (ε θ : ℝ) : (whitened1 ε θ).PosSemidef := by
  unfold whitened1
  have hD : (diagonal ε⁻¹)ᵀ = diagonal ε⁻¹ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal]
  have ht : ((rotation θ)ᵀ * endpoint1 * rotation θ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
      endpoint1_posSemidef.mul_mul_conjTranspose_same (rotation θ)ᵀ
  exact EntrywiseBures.posSemidef_congr_symm hD ht

theorem sqrt_whitened0 (R : EntrywiseBures.PSDSqrt 2) {ε : ℝ} (hε : 0 < ε) :
    R.sqrt (whitened0 ε) = diagonal ε⁻¹ := by
  refine R.eq_sqrt_of_mul_self _ _ (whitened0_posSemidef ε)
    (diagonal_posSemidef (inv_nonneg.mpr hε.le)) ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, whitened0, Matrix.mul_apply, Fin.sum_univ_two, sq]

/-- Evaluation of the exact Bures expression before rationalization. -/
theorem buresSq_whitened (R : EntrywiseBures.PSDSqrt 2) {ε θ : ℝ} (hε : 0 < ε) :
    2 * EntrywiseBures.buresSq R (whitened0 ε) (whitened1 ε θ) =
      rawValue ε (Real.sin θ ^ 2) := by
  have hX := whitened0_posSemidef ε
  have hY := whitened1_posSemidef ε θ
  have hS := R.transpose_sqrt hX
  have hinner := EntrywiseBures.posSemidef_congr_symm hS hY
  have htrace : (R.sqrt (whitened0 ε) * whitened1 ε θ * R.sqrt (whitened0 ε)).trace =
      (whitened0 ε * whitened1 ε θ).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, R.sqrt_mul_sqrt _ hX]
  have hdet : (R.sqrt (whitened0 ε) * whitened1 ε θ * R.sqrt (whitened0 ε)).det =
      (whitened0 ε).det * (whitened1 ε θ).det := by
    have hm := congrArg Matrix.det (R.sqrt_mul_sqrt _ hX)
    simp only [Matrix.det_mul] at hm ⊢
    rw [← hm]
    ring
  have hdetroot : Real.sqrt (2 * ε⁻¹ ^ 4) = Real.sqrt 2 * ε⁻¹ ^ 2 := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show ε⁻¹ ^ 4 = (ε⁻¹ ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg _)]
  have hroot : Real.sqrt
      (2 - Real.sin θ ^ 2 + (1 + Real.sin θ ^ 2) * ε⁻¹ ^ 4 +
        2 * (Real.sqrt 2 * ε⁻¹ ^ 2)) =
      Real.sqrt (radicand ε (Real.sin θ ^ 2)) / ε ^ 2 := by
    have he : ε ≠ 0 := ne_of_gt hε
    have heq : 2 - Real.sin θ ^ 2 + (1 + Real.sin θ ^ 2) * ε⁻¹ ^ 4 +
        2 * (Real.sqrt 2 * ε⁻¹ ^ 2) = radicand ε (Real.sin θ ^ 2) / ε ^ 4 := by
      unfold radicand
      field_simp
      ring
    rw [heq, Real.sqrt_div (radicand_pos (sq_nonneg _)
      (by nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)])).le,
      show ε ^ 4 = (ε ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  unfold EntrywiseBures.buresSq
  rw [trace_sqrt R hinner, htrace, hdet, det_product_whitened, hdetroot,
    trace_product_whitened, hroot]
  have htr := trace_sum_whitened ε θ
  unfold rawValue
  rw [htr]
  simp only [← inv_pow, div_eq_mul_inv]
  ring

theorem inverse_endpoint0 {ε θ : ℝ} (hε : 0 < ε) :
    (reactionWeight ε θ)⁻¹ * endpoint0 * (reactionWeight ε θ)⁻¹ =
      rotation θ * whitened0 ε * (rotation θ)ᵀ := by
  rw [inverseWeight_eq (ne_of_gt hε)]
  unfold inverseWeight endpoint0 whitened0
  rw [Matrix.mul_one]
  have hdiag : diagonal ε⁻¹ * diagonal ε⁻¹ = diagonal (ε⁻¹ ^ 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.mul_apply, Fin.sum_univ_two, sq]
  calc
    rotation θ * diagonal ε⁻¹ * (rotation θ)ᵀ *
        (rotation θ * diagonal ε⁻¹ * (rotation θ)ᵀ) =
        rotation θ * (diagonal ε⁻¹ * diagonal ε⁻¹) * (rotation θ)ᵀ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (rotation θ)ᵀ,
        transpose_rotation_mul, Matrix.one_mul]
    _ = _ := by rw [hdiag]

theorem inverse_endpoint1 {ε θ : ℝ} (hε : 0 < ε) :
    (reactionWeight ε θ)⁻¹ * endpoint1 * (reactionWeight ε θ)⁻¹ =
      rotation θ * whitened1 ε θ * (rotation θ)ᵀ := by
  rw [inverseWeight_eq (ne_of_gt hε)]
  unfold inverseWeight whitened1
  simp only [Matrix.mul_assoc]

/-- The explicit rationalized expression is precisely the weighted Bures value.
The separate uniform-reaction theorem identifies this quantity with the original minimum. -/
theorem buresValue_rotation (R : EntrywiseBures.PSDSqrt 2) {ε θ : ℝ} (hε : 0 < ε) :
    EntrywiseBures.buresValue R (reactionWeight ε θ) endpoint0 endpoint1 =
      rationalizedValue ε (Real.sin θ ^ 2) := by
  unfold EntrywiseBures.buresValue
  rw [inverse_endpoint0 hε, inverse_endpoint1 hε,
    buresSq_conjugate R θ (whitened0_posSemidef ε) (whitened1_posSemidef ε θ),
    buresSq_whitened R hε]
  exact rawValue_eq_rationalized hε (sq_nonneg _)
    (by nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)])

theorem rotationValue_nonneg {ε θ : ℝ} (hε : 0 < ε) :
    0 ≤ rationalizedValue ε (Real.sin θ ^ 2) := by
  let R := EntrywiseBures.canonicalPSDSqrt 2
  obtain ⟨P, hgram, htr⟩ := EntrywiseBures.exists_bures_factor R
    (whitened0_posSemidef ε) (whitened1_posSemidef ε θ)
  have hcost := EntrywiseBures.frobeniusSq_factor_sub R
    (whitened0_posSemidef ε) hgram htr
  have h := ReactionZero.frobeniusSq_nonneg (P - R.sqrt (whitened0 ε))
  rw [hcost] at h
  rw [← rawValue_eq_rationalized hε (sq_nonneg _) (by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]),
    ← buresSq_whitened R hε]
  linarith

theorem reactionWeight_transpose (ε θ : ℝ) : (reactionWeight ε θ)ᵀ = reactionWeight ε θ := by
  unfold reactionWeight
  have hd : (diagonal ε)ᵀ = diagonal ε := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hd]
  simp only [Matrix.mul_assoc]

theorem reactionWeight_det (ε θ : ℝ) : (reactionWeight ε θ).det = ε := by
  unfold reactionWeight
  have hrot : (rotation θ).det = 1 := by
    simp [rotation, Matrix.det_fin_two]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hrot]
  simp [diagonal, Matrix.det_fin_two]

/-- The current rotating-family expression bounds every original competitor from below. -/
theorem rotationValue_le_minimumValue {d k : ℕ}
    {Ω : Set (ReactionZero.ClosedDomain.Space d)} [Fact (IsCompact Ω)]
    (R : EntrywiseBures.PSDSqrt 2) (P : ReactionZero.Limit.Problem Ω 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → P.operator.D0 A = 0)
    (hinitial : EntrywiseBures.totalMatrix P.initial = endpoint0)
    (hterminal : EntrywiseBures.totalMatrix P.terminal = endpoint1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (rationalizedValue ε (Real.sin θ ^ 2)) ≤
      ReactionZero.Limit.minimumValue P L (reactionWeight ε θ) := by
  have hu : IsUnit (reactionWeight ε θ).det := by
    rw [reactionWeight_det, isUnit_iff_ne_zero]
    exact ne_of_gt hε
  have h := EntrywiseBures.buresValue_le_minimumValue R P hD0
    (reactionWeight_transpose ε θ) hu L
  rwa [hinitial, hterminal, buresValue_rotation R hε] at h

def singularWeight : Mat := diagonal 0
def growthFactor : Mat := !![Real.sqrt 2, 0; 0, 1]
def growthIncrement : Mat := !![Real.sqrt 2 - 1, 0; 0, 0]

theorem singularWeight_transpose : singularWeightᵀ = singularWeight := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [singularWeight, diagonal]

theorem singularWeight_mul_growthIncrement : singularWeight * growthIncrement = growthIncrement := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [singularWeight, diagonal, growthIncrement, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply]
  all_goals norm_num

theorem one_add_growthIncrement : (1 : Mat) + growthIncrement = growthFactor := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [growthIncrement, growthFactor]

theorem frobeniusSq_growthIncrement :
    2 * ReactionZero.frobeniusSq growthIncrement = targetValue := by
  simp [ReactionZero.frobeniusSq, growthIncrement, targetValue, Fin.sum_univ_two]

theorem growthFactor_posSemidef : growthFactor.PosSemidef := by
  have heq : growthFactor = Matrix.diagonal ![Real.sqrt 2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [growthFactor, Matrix.diagonal]
  rw [heq, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp [Real.sqrt_nonneg]

theorem growthFactor_square : growthFactor * growthFactor = endpoint1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [growthFactor, endpoint1, Matrix.mul_apply, Fin.sum_univ_two,
      ← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem gram_growthFactor : ReactionZero.gram growthFactor = endpoint1 := by
  have ht : growthFactorᵀ = growthFactor := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [growthFactor]
  unfold ReactionZero.gram
  rw [ht, growthFactor_square]

theorem gram_identity : ReactionZero.gram (1 : Mat) = endpoint0 := by
  simp [ReactionZero.gram, endpoint0]

theorem continuous_rotation : Continuous rotation := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [rotation, Matrix.of_apply] <;> fun_prop

theorem continuous_diagonal : Continuous diagonal := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [diagonal, Matrix.of_apply] <;> fun_prop

/-- The example's weights converge to the stated singular matrix. -/
theorem reactionWeight_tendsto {ε θ : ℕ → ℝ}
    (hε : Filter.Tendsto ε Filter.atTop (𝓝 0))
    (hθ : Filter.Tendsto θ Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun j ↦ reactionWeight (ε j) (θ j)) Filter.atTop (𝓝 singularWeight) := by
  have hu := (continuous_rotation.tendsto 0).comp hθ
  have hd := (continuous_diagonal.tendsto 0).comp hε
  have hut := (continuous_id.matrix_transpose.tendsto (rotation 0)).comp hu
  have h := EntrywiseBures.matrix_product_tendsto
    (EntrywiseBures.matrix_product_tendsto hu hd) hut
  have hzero : rotation 0 = (1 : Mat) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotation]
  simpa only [Function.comp_def, id_eq, hzero, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one, singularWeight, reactionWeight] using h

theorem buresValue_identity (R : EntrywiseBures.PSDSqrt 2) :
    EntrywiseBures.buresValue R (1 : Mat) endpoint0 endpoint1 = targetValue := by
  have hroot0 : R.sqrt (1 : Mat) = 1 :=
    R.eq_sqrt_of_mul_self _ _ Matrix.PosSemidef.one Matrix.PosSemidef.one (Matrix.one_mul _)
  have hroot1 : R.sqrt endpoint1 = growthFactor :=
    R.eq_sqrt_of_mul_self _ _ endpoint1_posSemidef growthFactor_posSemidef growthFactor_square
  unfold EntrywiseBures.buresValue EntrywiseBures.buresSq endpoint0
  simp only [inv_one, Matrix.one_mul, Matrix.mul_one, hroot0, hroot1]
  rw [targetValue_eq]
  simp [endpoint1, growthFactor, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  ring

theorem singular_gram_le_identity :
    ((1 : Mat) * (1 : Mat)ᵀ - singularWeight * singularWeightᵀ).PosSemidef := by
  have heq : (1 : Mat) * (1 : Mat)ᵀ - singularWeight * singularWeightᵀ =
      Matrix.diagonal ![0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [singularWeight, diagonal, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.diagonal, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two, Matrix.of_apply]
    all_goals norm_num
  rw [heq, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

/-- The singular target lower bound is against the full original signed-measure class.
It reuses the nonsingular Riccati certificate at the cheaper identity reaction weight. -/
theorem targetValue_le_action {d k : ℕ}
    {Ω : Set (ReactionZero.ClosedDomain.Space d)} [Fact (IsCompact Ω)]
    (R : EntrywiseBures.PSDSqrt 2) (P : ReactionZero.Limit.Problem Ω 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → P.operator.D0 A = 0)
    (hinitial : EntrywiseBures.totalMatrix P.initial = endpoint0)
    (hterminal : EntrywiseBures.totalMatrix P.terminal = endpoint1)
    (L : Matrix (Fin k) (Fin k) ℝ) (μ : ReactionZero.Limit.Path Ω 2 k)
    (hμ : ReactionZero.Limit.Good P μ) :
    ENNReal.ofReal targetValue ≤ ReactionZero.action L singularWeight μ := by
  have h := EntrywiseBures.buresValue_le_action R P hD0
    (by simp : (1 : Mat)ᵀ = 1) (by simp : IsUnit (1 : Mat).det) L μ hμ
  rw [hinitial, hterminal, buresValue_identity R] at h
  exact h.trans (ReactionZero.action_mono_reaction L singular_gram_le_identity μ)

theorem targetValue_le_minimumValue {d k : ℕ}
    {Ω : Set (ReactionZero.ClosedDomain.Space d)} [Fact (IsCompact Ω)]
    (R : EntrywiseBures.PSDSqrt 2) (P : ReactionZero.Limit.Problem Ω 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → P.operator.D0 A = 0)
    (hinitial : EntrywiseBures.totalMatrix P.initial = endpoint0)
    (hterminal : EntrywiseBures.totalMatrix P.terminal = endpoint1)
    (L : Matrix (Fin k) (Fin k) ℝ) :
    ENNReal.ofReal targetValue ≤ ReactionZero.Limit.minimumValue P L singularWeight := by
  unfold ReactionZero.Limit.minimumValue ReactionZero.constrainedInfimum
  exact le_iInf fun μ ↦ le_iInf fun hμ ↦
    targetValue_le_action R P hD0 hinitial hterminal L μ hμ

#print axioms buresValue_rotation
#print axioms targetValue_le_minimumValue

#print axioms buresSq_whitened

end MatrixTransport.Paper.RotatingReaction
