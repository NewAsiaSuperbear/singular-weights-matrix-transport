import MatrixTransport.Paper.GenericBridges
import MatrixTransport.Paper.FluxNoncompactness
import MatrixTransport.Paper.NativeSeparation
import MatrixTransport.Paper.NativeSeparationRegime
import MatrixTransport.Examples.RotatingTransportOriginal
import MatrixTransport.Examples.KBObstruction

/-! Literal algebra, exact constructions, and parameter scope of the existing examples. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.ExampleBridges
open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain
open MatrixTransport.ReactionZero.Limit MatrixTransport.EntrywiseBures
open MatrixTransport.Paper.RotatingReaction LiZouTransport.Reaction
open LiZouTransport.Examples

def actualX0 (ε θ : ℝ) : RMat 2 :=
  (reactionWeight ε θ)⁻¹ * endpoint0 * (reactionWeight ε θ)⁻¹

def actualX1 (ε θ : ℝ) : RMat 2 :=
  (reactionWeight ε θ)⁻¹ * endpoint1 * (reactionWeight ε θ)⁻¹

theorem trace_sum_X {ε θ : ℝ} (hε : 0 < ε) :
    (actualX0 ε θ).trace + (actualX1 ε θ).trace =
      3 - Real.sin θ ^ 2 + (2 + Real.sin θ ^ 2) / ε ^ 2 := by
  unfold actualX0 actualX1
  rw [inverse_endpoint0 hε, inverse_endpoint1 hε, trace_orthogonal_conjugate,
    trace_orthogonal_conjugate, trace_sum_whitened]
  simp only [inv_pow, div_eq_mul_inv]

theorem trace_sqrt_sq (R : PSDSqrt 2) {Y : RMat 2} (hY : Y.PosSemidef) :
    (R.sqrt Y).trace ^ 2 = Y.trace + 2 * Real.sqrt Y.det := by
  rw [trace_sqrt R hY, Real.sq_sqrt]
  exact add_nonneg hY.trace_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem trace_sqrt_sandwich {n : ℕ} (R : PSDSqrt n) {X Y : RMat n}
    (hX : X.PosSemidef) : (R.sqrt X * Y * R.sqrt X).trace = (X * Y).trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, R.sqrt_mul_sqrt X hX]

theorem det_sqrt_sandwich {n : ℕ} (R : PSDSqrt n) {X Y : RMat n}
    (hX : X.PosSemidef) : (R.sqrt X * Y * R.sqrt X).det = X.det * Y.det := by
  have hs := congrArg Matrix.det (R.sqrt_mul_sqrt X hX)
  simp only [Matrix.det_mul] at hs ⊢
  rw [← hs]
  ring

theorem det_orthogonal_conjugate (θ : ℝ) (X : RMat 2) :
    (rotation θ * X * (rotation θ)ᵀ).det = X.det := by
  have hU : (rotation θ).det * ((rotation θ)ᵀ).det = 1 := by
    rw [← Matrix.det_mul, rotation_mul_transpose, Matrix.det_one]
  simp only [Matrix.det_mul]
  calc
    (rotation θ).det * X.det * ((rotation θ)ᵀ).det =
        X.det * ((rotation θ).det * ((rotation θ)ᵀ).det) := by ring
    _ = X.det := by rw [hU, mul_one]

theorem trace_product_X (R : PSDSqrt 2) {ε θ : ℝ} (hε : 0 < ε) :
    (R.sqrt (actualX0 ε θ) * actualX1 ε θ * R.sqrt (actualX0 ε θ)).trace =
      2 - Real.sin θ ^ 2 + (1 + Real.sin θ ^ 2) / ε ^ 4 := by
  have hX : (actualX0 ε θ).PosSemidef := by
    rw [actualX0, inverse_endpoint0 hε]
    exact conjugate_posSemidef θ (whitened0_posSemidef ε)
  rw [trace_sqrt_sandwich R hX]
  unfold actualX0 actualX1
  rw [inverse_endpoint0 hε, inverse_endpoint1 hε]
  have he : (rotation θ * whitened0 ε * (rotation θ)ᵀ) *
      (rotation θ * whitened1 ε θ * (rotation θ)ᵀ) =
      rotation θ * (whitened0 ε * whitened1 ε θ) * (rotation θ)ᵀ := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (rotation θ)ᵀ,
      transpose_rotation_mul, Matrix.one_mul]
  rw [he, trace_orthogonal_conjugate, trace_product_whitened]
  simp only [inv_pow, div_eq_mul_inv]

theorem det_product_X (R : PSDSqrt 2) {ε θ : ℝ} (hε : 0 < ε) :
    (R.sqrt (actualX0 ε θ) * actualX1 ε θ * R.sqrt (actualX0 ε θ)).det = 2 / ε ^ 4 := by
  have hX : (actualX0 ε θ).PosSemidef := by
    rw [actualX0, inverse_endpoint0 hε]
    exact conjugate_posSemidef θ (whitened0_posSemidef ε)
  rw [det_sqrt_sandwich R hX]
  unfold actualX0 actualX1
  rw [inverse_endpoint0 hε, inverse_endpoint1 hε, det_orthogonal_conjugate,
    det_orthogonal_conjugate, det_product_whitened]
  simp only [inv_pow, div_eq_mul_inv]

theorem singular_factorMass_eq (s : ℝ) :
    factorMass singularWeight (1 : RMat 2) growthIncrement s =
      !![(1 + (Real.sqrt 2 - 1) * s) ^ 2, 0; 0, 1] := by
  rw [factorMass, singularWeight_mul_growthIncrement]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [factorPoint, growthIncrement, gram, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem singular_factorRate_eq_deriv (s : ℝ) :
    HasDerivAt (factorMass singularWeight (1 : RMat 2) growthIncrement)
      (factorRate singularWeight (1 : RMat 2) growthIncrement s) s := by
  have he : factorMassDeriv singularWeight (1 : RMat 2) growthIncrement s =
      factorRate singularWeight (1 : RMat 2) growthIncrement s := by
    rw [factorMassDeriv, factorRate, singularWeight_mul_growthIncrement]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [factorPoint, growthIncrement, singularWeight,
        MatrixTransport.Paper.RotatingReaction.diagonal, Matrix.transpose_apply,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  exact (factorMass_deriv singularWeight (1 : RMat 2) growthIncrement s).congr_deriv he

theorem singular_path_action_eq {d k : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]
    (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : RMat 2, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) :
    action L singularWeight (reactionPath (k := k) μ singularWeight (1 : RMat 2)
      growthIncrement 0 1 ⟨le_rfl, zero_le_one⟩
      (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one) = ENNReal.ofReal targetValue := by
  let path := reactionPath (k := k) μ singularWeight (1 : RMat 2) growthIncrement 0 1
    ⟨le_rfl, zero_le_one⟩ (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
  have h1 : gram ((1 : RMat 2) + singularWeight * growthIncrement) = endpoint1 := by
    rw [singularWeight_mul_growthIncrement, one_add_growthIncrement, gram_growthFactor]
  have hg : Good (rotationProblem D μ) path := by
    simpa only [rotationProblem, path, gram_identity, h1] using
      LiZouTransport.RegularReaction.reactionPath_good_uniform_regular hΩ D μ
        singularWeight_transpose (1 : RMat 2) growthIncrement
  apply le_antisymm
  · have hu := reactionPath_action_le μ L singularWeight_transpose (1 : RMat 2)
      growthIncrement 0 1 ⟨le_rfl, zero_le_one⟩
      (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
    simpa only [div_one, hμ, mul_one, frobeniusSq_growthIncrement] using hu
  · apply targetValue_le_action (canonicalPSDSqrt 2) (rotationProblem D μ) hD0
      (totalMatrix_uniformEndpoint_probability μ hμ endpoint0)
      (totalMatrix_uniformEndpoint_probability μ hμ endpoint1) L path hg

theorem rotWeight_mulVec_uDir (θ ε : ℝ) :
    rotWeight θ ε *ᵥ ![Real.sin θ, -Real.cos θ] =
      ε • ![Real.sin θ, -Real.cos θ] := by
  ext i
  fin_cases i
  · simp [rotWeight, rotW, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination ε * Real.sin θ * Real.sin_sq_add_cos_sq θ
  · simp [rotWeight, rotW, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination -(ε * Real.cos θ) * Real.sin_sq_add_cos_sq θ

theorem uDir_unit (θ : ℝ) : ∑ i : Fin 2, uDir (Real.sin θ) (Real.cos θ) i ^ 2 = 1 := by
  simpa [Fin.sum_univ_two] using Real.sin_sq_add_cos_sq θ

theorem normDiv_hj_display (t : ℝ) (q : Q disk2) :
    (-1 / 8 : ℝ) + (1 / 2 : ℝ) * ∑ l,
        (∑ l', affFx 0 (1 / 4) l' * Lhoriz t l' l) ^ 2 +
      (1 / 2 : ℝ) * (affF 0 (-1 / 8) 0 (1 / 4) q.val) ^ 2 ≤ -3 / 128 := by
  have hs := q.property.1
  have hy := (mem_disk2_iff _).1 q.property.2
  have hy1 : q.val.2 1 ≤ 1 := by nlinarith [sq_nonneg (q.val.2 0)]
  have hy0 : -1 ≤ q.val.2 1 := by nlinarith [sq_nonneg (q.val.2 0)]
  have hf := kb_F0_sq_le q.val.1 (q.val.2 1) hs.1 hs.2 hy0 hy1
  simp [Fin.sum_univ_two, affF, Lhoriz]
  nlinarith

theorem horizontal_support_chain {A B C : ℝ}
    (h : A + (1 / 2 : ℝ) * B ^ 2 + (1 / 2 : ℝ) * C ^ 2 ≤ 0) :
    A + B ≤ -(1 / 2 : ℝ) * B ^ 2 + B ∧
      -(1 / 2 : ℝ) * B ^ 2 + B ≤ 1 / 2 := by
  constructor <;> nlinarith [sq_nonneg C, sq_nonneg (B - 1)]

theorem vertical_support_chain {t A B0 B1 C : ℝ} (ht : t ≠ 0)
    (h : A + (1 / 2 : ℝ) * (B0 ^ 2 + (B1 * t) ^ 2) + (1 / 2 : ℝ) * C ^ 2 ≤ 0) :
    A + 2 * B1 ≤ -(t ^ 2 / 2) * B1 ^ 2 + 2 * B1 ∧
      -(t ^ 2 / 2) * B1 ^ 2 + 2 * B1 ≤ 2 / t ^ 2 := by
  constructor
  · nlinarith [sq_nonneg B0, sq_nonneg C]
  · apply (le_div_iff₀ (sq_pos_of_ne_zero ht)).mpr
    have hid : (-(t ^ 2 / 2) * B1 ^ 2 + 2 * B1) * t ^ 2 - 2 =
        -((t ^ 2 * B1 - 2) ^ 2) / 2 := by ring
    apply sub_nonpos.mp
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)

theorem kbJet_abs_bounds (q : Q disk2) :
    |q.val.2 1 / 4 - q.val.1 / 8| ≤ 3 / 8 ∧ |q.val.1 / 8| ≤ 1 / 8 := by
  have hs := q.property.1
  have hy := (mem_disk2_iff _).1 q.property.2
  have hy1 : q.val.2 1 ≤ 1 := by nlinarith [sq_nonneg (q.val.2 0)]
  have hy0 : -1 ≤ q.val.2 1 := by nlinarith [sq_nonneg (q.val.2 0)]
  constructor <;> rw [abs_le] <;> constructor <;> linarith [hs.1, hs.2]

theorem kbJet_diag_bounds (q : Q disk2) :
    (-1 / 8 : ℝ) + (1 / 2 : ℝ) * (q.val.2 1 / 4 - q.val.1 / 8) ^ 2 ≤ -3 / 128 ∧
    (-1 / 8 : ℝ) + (1 / 2 : ℝ) * (q.val.1 / 8) ^ 2 ≤ -15 / 128 := by
  obtain ⟨h0, h1⟩ := kbJet_abs_bounds q
  have hsq0 := sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 8) |>.2 h0
  have hsq1 := sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 8) |>.2 h1
  rw [sq_abs] at hsq0 hsq1
  constructor <;> nlinarith

theorem kbJet_first_diag_intermediate (q : Q disk2) :
    (-1 / 8 : ℝ) + (1 / 2 : ℝ) * (q.val.2 1 / 4 - q.val.1 / 8) ^ 2 ≤
      -1 / 8 + 9 / 128 ∧ (-1 / 8 + 9 / 128 : ℝ) ≤ -3 / 128 := by
  have h := (kbJet_abs_bounds q).1
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 8)).2 h
  rw [sq_abs] at hs
  constructor <;> nlinarith

theorem buresSq_self {n : ℕ} (R : PSDSqrt n) {X : RMat n} (hX : X.PosSemidef) :
    buresSq R X X = 0 := by
  have he : R.sqrt X * X * R.sqrt X = X * X := by
    calc
      R.sqrt X * X * R.sqrt X =
          R.sqrt X * (R.sqrt X * R.sqrt X) * R.sqrt X := by
            rw [R.sqrt_mul_sqrt X hX]
      _ = (R.sqrt X * R.sqrt X) * (R.sqrt X * R.sqrt X) := by
        simp only [Matrix.mul_assoc]
      _ = X * X := by rw [R.sqrt_mul_sqrt X hX]
  have hXX : (X * X).PosSemidef := by
    have ht : Xᵀ = X := transpose_eq_of_posSemidef hX
    simpa only [gram, ht] using posSemidef_gram X
  have hs : R.sqrt (X * X) = X :=
    R.eq_sqrt_of_mul_self _ _ hXX hX rfl
  simp only [buresSq, he, hs]
  ring

theorem buresValue_self {n : ℕ} (R : PSDSqrt n) (H : RMat n)
    (hH : Hᵀ = H) {A : RMat n} (hA : A.PosSemidef) : buresValue R H A A = 0 := by
  unfold buresValue
  have hHi : (H⁻¹)ᵀ = H⁻¹ := transpose_inv_of_symm hH
  rw [buresSq_self R (posSemidef_congr_symm hHi hA)]
  ring

theorem kb_not_tendsto_bures (R : PSDSqrt 2) (t : ℕ → ℝ) :
    ¬ Tendsto (fun j ↦ minimumValue kbProblem (!![t j]) (1 : RMat 2)) atTop
      (𝓝 (ENNReal.ofReal (buresValue R (1 : RMat 2) (1 : RMat 2) (1 : RMat 2)))) := by
  rw [buresValue_self R (1 : RMat 2) (by simp) Matrix.PosSemidef.one,
    ENNReal.ofReal_zero]
  exact (kb_obstruction t).2

theorem kbOp_D0_eq_zero : kbOp.D0 = 0 := rfl

theorem cutoff_gradient_gram_eq (θ ε : ℝ) (hε : ε ≠ 0) (x : Space 2) :
    (∑ l : Fin 2, (∑ l' : Fin 2,
      (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) x / ε) *
        (uDir (Real.sin θ) (Real.cos θ) l' / ε)) * rotWeight θ ε l' l) ^ 2) =
      cutF (Real.sin θ) (Real.cos θ) ε x *
        (1 - cutF (Real.sin θ) (Real.cos θ) ε x) := by
  let D := sineCutoffD (uSig (Real.sin θ) (Real.cos θ) x / ε)
  have he (j : Fin 2) : D * (uDir (Real.sin θ) (Real.cos θ) j / ε) =
      (D / ε) * uDir (Real.sin θ) (Real.cos θ) j := by ring
  calc
    _ = (ε * (D / ε)) ^ 2 := by
      simp only [← show D = sineCutoffD (uSig (Real.sin θ) (Real.cos θ) x / ε) from rfl, he]
      exact rotW_flux (Real.sin θ) (Real.cos θ) ε (D / ε) (Real.sin_sq_add_cos_sq θ)
    _ = D ^ 2 := by congr 1; field_simp
    _ = _ := sineCutoffD_sq _

/-- The squared KB normalization used for the smooth endpoint family in the separation section. -/
abbrev kbDistSq (ρ : MatrixTransport.Spatial → ℝ) (hρ : Continuous ρ)
    (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ)) : ℝ≥0∞ :=
  2 * LiZouTransport.NativeSeparation.smoothValue kbOp ρ hρ hb

theorem rot_hj_eq (θ ε δ : ℝ) (hε : ε ≠ 0) (q : Ambient 2) :
    rotFt (Real.sin θ) (Real.cos θ) ε δ q +
      (1 / 2 : ℝ) * ∑ l, (∑ l', rotFx (Real.sin θ) (Real.cos θ) ε δ l' q *
        rotWeight θ ε l' l) ^ 2 +
      (1 / 2 : ℝ) * (rotF (Real.sin θ) (Real.cos θ) ε δ q) ^ 2 = 0 := by
  have hSc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hflux : ∀ l' : Fin 2, rotFx (Real.sin θ) (Real.cos θ) ε δ l' q =
      ((bTime δ q.1 - aTime δ q.1) *
        (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε)) *
        uDir (Real.sin θ) (Real.cos θ) l' := by
    intro l'
    unfold rotFx
    ring
  have hsum : ∑ l : Fin 2, (∑ l' : Fin 2, rotFx (Real.sin θ) (Real.cos θ) ε δ l' q *
      rotWeight θ ε l' l) ^ 2 =
      (ε * ((bTime δ q.1 - aTime δ q.1) *
        (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε))) ^ 2 := by
    simp only [hflux]
    exact rotW_flux (Real.sin θ) (Real.cos θ) ε _ hSc
  have hcancel : ε * (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε) =
      sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) := by
    field_simp
  have hε2 : ε * ((bTime δ q.1 - aTime δ q.1) *
      (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε)) =
      (bTime δ q.1 - aTime δ q.1) * sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) := by
    calc ε * ((bTime δ q.1 - aTime δ q.1) *
          (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε))
        = (bTime δ q.1 - aTime δ q.1) *
          (ε * (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε)) := by ring
      _ = _ := by rw [hcancel]
  rw [hsum, hε2]
  have key := rot_hj_real (aTime δ q.1) (bTime δ q.1) (aD δ q.1) (bD δ q.1)
    (cutF (Real.sin θ) (Real.cos θ) ε q.2)
    (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε))
    (((bTime δ q.1 - aTime δ q.1) *
      sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε)) ^ 2)
    (aD_eq δ q.1) (bD_eq δ q.1) (sineCutoffD_sq _) rfl
  unfold rotFt rotF
  linarith [key]

theorem fullZeroLinear_eq_zero_iff (X : MatrixTransport.Mat2) :
    LiZouTransport.NativeSeparation.fullZeroLinear X = 0 ↔
      MatrixTransport.fullL0 * X = X * MatrixTransport.fullL0 ∧
        MatrixTransport.fullL1 * X = X * MatrixTransport.fullL1 := by
  constructor
  · intro h
    have h0 : MatrixTransport.fullL0 * X - X * MatrixTransport.fullL0 = 0 := by
      ext i j
      fin_cases j
      · have he := congrFun (congrFun h i) (4 : Fin 8)
        simpa [LiZouTransport.NativeSeparation.fullZeroLinear_apply, MatrixTransport.fullCol]
          using he
      · have he := congrFun (congrFun h i) (5 : Fin 8)
        simpa [LiZouTransport.NativeSeparation.fullZeroLinear_apply, MatrixTransport.fullCol]
          using he
    have h1 : MatrixTransport.fullL1 * X - X * MatrixTransport.fullL1 = 0 := by
      ext i j
      fin_cases j
      · have he := congrFun (congrFun h i) (6 : Fin 8)
        simpa [LiZouTransport.NativeSeparation.fullZeroLinear_apply, MatrixTransport.fullCol]
          using he
      · have he := congrFun (congrFun h i) (7 : Fin 8)
        simpa [LiZouTransport.NativeSeparation.fullZeroLinear_apply, MatrixTransport.fullCol]
          using he
    exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩
  · rintro ⟨h0, h1⟩
    ext i k
    simp [LiZouTransport.NativeSeparation.fullZeroLinear_apply, h0, h1]

theorem fullOperator_constant_zero_iff {Ω : Set (Space 2)} (φ : ClosedC1Jet Ω 2)
    (hx : ∀ j p, φ.dx j p = 0) (p : Q Ω) :
    LiZouTransport.NativeSeparation.fullOperator.apply φ p = 0 ↔
      MatrixTransport.fullL0 * φ.value p = φ.value p * MatrixTransport.fullL0 ∧
        MatrixTransport.fullL1 * φ.value p = φ.value p * MatrixTransport.fullL1 := by
  have he : LiZouTransport.NativeSeparation.fullOperator.apply φ p =
      LiZouTransport.NativeSeparation.fullZeroLinear (φ.value p) := by
    simp [AdjointOperator.apply, LiZouTransport.NativeSeparation.fullOperator, hx]
  rw [he]
  exact fullZeroLinear_eq_zero_iff _

end LiZouTransport.ExampleBridges

#print axioms LiZouTransport.ExampleBridges.trace_sum_X
#print axioms LiZouTransport.ExampleBridges.trace_sqrt_sq
#print axioms LiZouTransport.ExampleBridges.trace_sqrt_sandwich
#print axioms LiZouTransport.ExampleBridges.det_sqrt_sandwich
#print axioms LiZouTransport.ExampleBridges.det_orthogonal_conjugate
#print axioms LiZouTransport.ExampleBridges.trace_product_X
#print axioms LiZouTransport.ExampleBridges.det_product_X
#print axioms LiZouTransport.ExampleBridges.singular_factorMass_eq
#print axioms LiZouTransport.ExampleBridges.singular_factorRate_eq_deriv
#print axioms LiZouTransport.ExampleBridges.singular_path_action_eq
#print axioms LiZouTransport.ExampleBridges.rotWeight_mulVec_uDir
#print axioms LiZouTransport.ExampleBridges.uDir_unit
#print axioms LiZouTransport.ExampleBridges.normDiv_hj_display
#print axioms LiZouTransport.ExampleBridges.horizontal_support_chain
#print axioms LiZouTransport.ExampleBridges.vertical_support_chain
#print axioms LiZouTransport.ExampleBridges.kbJet_abs_bounds
#print axioms LiZouTransport.ExampleBridges.kbJet_diag_bounds
#print axioms LiZouTransport.ExampleBridges.kbJet_first_diag_intermediate
#print axioms LiZouTransport.ExampleBridges.buresSq_self
#print axioms LiZouTransport.ExampleBridges.buresValue_self
#print axioms LiZouTransport.ExampleBridges.kb_not_tendsto_bures
#print axioms LiZouTransport.ExampleBridges.kbOp_D0_eq_zero
#print axioms LiZouTransport.ExampleBridges.cutoff_gradient_gram_eq
#print axioms LiZouTransport.ExampleBridges.rot_hj_eq
#print axioms LiZouTransport.ExampleBridges.fullZeroLinear_eq_zero_iff
#print axioms LiZouTransport.ExampleBridges.fullOperator_constant_zero_iff
