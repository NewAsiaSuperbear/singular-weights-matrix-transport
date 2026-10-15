import MatrixTransport.EntrywiseBures.SqrtProvider
import MatrixTransport.ReactionZero.WeightedSet
import Mathlib.Analysis.Matrix.Order

/-!
# Finite-dimensional Bures algebra, including singular endpoints

* `buresSq R X Y = tr X + tr Y - 2 tr √(√X Y √X)` for every PSD `X, Y` (no invertibility).
* `sqrt_tendsto`: continuity of the square root along sequences of PSD matrices, derived only
  from the provider's uniqueness field, closedness of the PSD cone and compactness of bounded
  sets.
* `exists_bures_factor`: for all PSD `X, Y` there is `P` with `P Pᵀ = Y` and
  `tr(√X P) = tr √(√X Y √X)`, hence `‖P - √X‖²_F = buresSq X Y`.  Invertible `X` gives the
  explicit factor `T √X` with `T = (√X)⁻¹ √(√X Y √X) (√X)⁻¹`; the singular case is a limit of
  regularizations `X + δ I`.
* `regData`: for `δ > 0` the map `T_δ` between `X + δI` and `Y + δI`, used by the lower bound.

-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace MatrixTransport.EntrywiseBures

variable {n : ℕ}

theorem continuous_matrix_product :
    Continuous (fun a : RMat n × RMat n ↦ a.1 * a.2) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun a : RMat n × RMat n ↦ ∑ k : Fin n, a.1 i k * a.2 k j)
  apply continuous_finsetSum
  intro k _
  have h1 : Continuous (fun a : RMat n × RMat n ↦ a.1 i k) := by fun_prop
  have h2 : Continuous (fun a : RMat n × RMat n ↦ a.2 k j) := by fun_prop
  exact h1.mul h2

theorem matrix_product_tendsto {α : Type*} {l : Filter α}
    {A B : α → RMat n} {A0 B0 : RMat n}
    (hA : Tendsto A l (𝓝 A0)) (hB : Tendsto B l (𝓝 B0)) :
    Tendsto (fun x ↦ A x * B x) l (𝓝 (A0 * B0)) :=
  (continuous_matrix_product.tendsto (A0, B0)).comp (hA.prodMk_nhds hB)

/-- Squared Bures-Wasserstein distance, defined for every pair of matrices and used on PSD
pairs. -/
def buresSq (R : PSDSqrt n) (X Y : RMat n) : ℝ :=
  X.trace + Y.trace - 2 * (R.sqrt (R.sqrt X * Y * R.sqrt X)).trace

/-! ### Elementary PSD facts -/

theorem posSemidef_congr_symm {S A : RMat n} (hS : Sᵀ = S) (hA : A.PosSemidef) :
    (S * A * S).PosSemidef := by
  have h := hA.mul_mul_conjTranspose_same S
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hS] at h

theorem posSemidef_add_smul_one {X : RMat n} (hX : X.PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ) :
    (X + δ • (1 : RMat n)).PosSemidef :=
  hX.add (Matrix.PosSemidef.one.smul hδ)

theorem dotProduct_self_pos {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  rcases (show 0 ≤ v ⬝ᵥ v from Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)).lt_or_eq with h | h
  · exact h
  · exfalso
    exact hv (dotProduct_self_eq_zero.mp h.symm)

/-- `X + δ I` is invertible for PSD `X` and `δ > 0`. -/
theorem det_add_smul_one_ne_zero {X : RMat n} (hX : X.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    (X + δ • (1 : RMat n)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hq : v ⬝ᵥ ((X + δ • (1 : RMat n)) *ᵥ v) = v ⬝ᵥ (X *ᵥ v) + δ * (v ⬝ᵥ v) := by
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
  rw [hzero, dotProduct_zero] at hq
  have h1 : 0 ≤ v ⬝ᵥ (X *ᵥ v) := by
    simpa only [star_trivial] using hX.dotProduct_mulVec_nonneg v
  have h2 := dotProduct_self_pos hv
  nlinarith

theorem isUnit_det_of_mul_self {S A : RMat n} (hSA : S * S = A) (hA : A.det ≠ 0) :
    IsUnit S.det := by
  rw [isUnit_iff_ne_zero]
  intro h
  apply hA
  rw [← hSA, Matrix.det_mul, h, zero_mul]

theorem transpose_inv_of_symm {S : RMat n} (hS : Sᵀ = S) : (S⁻¹)ᵀ = S⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hS]

/-! ### The Bures map for an invertible source -/

section Map

variable (R : PSDSqrt n)

/-- `T = S⁻¹ F S⁻¹` with `S = √X` and `F = √(S Y S)`. -/
def buresMap (X Y : RMat n) : RMat n :=
  (R.sqrt X)⁻¹ * R.sqrt (R.sqrt X * Y * R.sqrt X) * (R.sqrt X)⁻¹

variable {R}

theorem buresMap_transpose {X Y : RMat n} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (buresMap R X Y)ᵀ = buresMap R X Y := by
  have hS := R.transpose_sqrt hX
  have hSYS := posSemidef_congr_symm hS hY
  unfold buresMap
  rw [Matrix.transpose_mul, Matrix.transpose_mul, transpose_inv_of_symm hS,
    R.transpose_sqrt hSYS]
  simp only [Matrix.mul_assoc]

/-- The map pushes `X` to `Y`. -/
theorem buresMap_push {X Y : RMat n} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hdet : X.det ≠ 0) : buresMap R X Y * X * buresMap R X Y = Y := by
  set S := R.sqrt X
  have hS := R.transpose_sqrt hX
  have hSS : S * S = X := R.sqrt_mul_sqrt X hX
  have hu : IsUnit S.det := isUnit_det_of_mul_self hSS hdet
  have hSYS := posSemidef_congr_symm hS hY
  have hFF : R.sqrt (S * Y * S) * R.sqrt (S * Y * S) = S * Y * S := R.sqrt_mul_sqrt _ hSYS
  have h1 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hu
  have h2 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hu
  unfold buresMap
  change S⁻¹ * R.sqrt (S * Y * S) * S⁻¹ * X *
    (S⁻¹ * R.sqrt (S * Y * S) * S⁻¹) = Y
  rw [← hSS]
  calc S⁻¹ * R.sqrt (S * Y * S) * S⁻¹ * (S * S) * (S⁻¹ * R.sqrt (S * Y * S) * S⁻¹)
      = S⁻¹ * R.sqrt (S * Y * S) * (S⁻¹ * S) * (S * S⁻¹) * R.sqrt (S * Y * S) * S⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = S⁻¹ * (R.sqrt (S * Y * S) * R.sqrt (S * Y * S)) * S⁻¹ := by
        rw [h1, h2]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = S⁻¹ * S * Y * (S * S⁻¹) := by
        rw [hFF]
        simp only [Matrix.mul_assoc]
    _ = Y := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/-- `S · (T S) = F`, so `tr(√X · T √X) = tr √(√X Y √X)`. -/
theorem sqrt_mul_buresFactor {X Y : RMat n} (hX : X.PosSemidef) (hdet : X.det ≠ 0) :
    R.sqrt X * (buresMap R X Y * R.sqrt X) = R.sqrt (R.sqrt X * Y * R.sqrt X) := by
  set S := R.sqrt X
  have hu : IsUnit S.det := isUnit_det_of_mul_self (R.sqrt_mul_sqrt X hX) hdet
  have h1 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hu
  have h2 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hu
  unfold buresMap
  calc S * (S⁻¹ * R.sqrt (S * Y * S) * S⁻¹ * S)
      = (S * S⁻¹) * R.sqrt (S * Y * S) * (S⁻¹ * S) := by simp only [Matrix.mul_assoc]
    _ = R.sqrt (S * Y * S) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem trace_buresMap_mul {X Y : RMat n} (hX : X.PosSemidef) (hdet : X.det ≠ 0) :
    (buresMap R X Y * X).trace = (R.sqrt (R.sqrt X * Y * R.sqrt X)).trace := by
  calc
    (buresMap R X Y * X).trace =
        (buresMap R X Y * (R.sqrt X * R.sqrt X)).trace := by
          rw [R.sqrt_mul_sqrt X hX]
    _ = (R.sqrt X * (buresMap R X Y * R.sqrt X)).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    _ = (R.sqrt (R.sqrt X * Y * R.sqrt X)).trace := by
      rw [sqrt_mul_buresFactor hX hdet]

theorem buresMap_posSemidef {X Y : RMat n} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (buresMap R X Y).PosSemidef := by
  have hS := R.transpose_sqrt hX
  have hSYS := posSemidef_congr_symm hS hY
  exact posSemidef_congr_symm (transpose_inv_of_symm hS) (R.posSemidef_sqrt _ hSYS)

end Map

/-! ### Factors with prescribed Gram and trace pairing -/

theorem frobeniusSq_eq_trace (A : RMat n) : ReactionZero.frobeniusSq A = (A * Aᵀ).trace := by
  simp only [ReactionZero.frobeniusSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, sq]

/-- A factor achieving the Bures value gives `‖P - √X‖² = buresSq X Y`. -/
theorem frobeniusSq_factor_sub (R : PSDSqrt n) {X Y P : RMat n} (hX : X.PosSemidef)
    (hP : P * Pᵀ = Y) (htr : (R.sqrt X * P).trace = (R.sqrt (R.sqrt X * Y * R.sqrt X)).trace) :
    ReactionZero.frobeniusSq (P - R.sqrt X) = buresSq R X Y := by
  have hS := R.transpose_sqrt hX
  have hSS := R.sqrt_mul_sqrt X hX
  have hPS : (P * R.sqrt X).trace = (R.sqrt X * P).trace := Matrix.trace_mul_comm _ _
  have hSP : (R.sqrt X * Pᵀ).trace = (R.sqrt X * P).trace := by
    rw [← Matrix.trace_transpose (R.sqrt X * Pᵀ), Matrix.transpose_mul, Matrix.transpose_transpose,
      hS, Matrix.trace_mul_comm]
  rw [frobeniusSq_eq_trace, Matrix.transpose_sub, hS, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, hP, hSS, hPS, hSP,
    htr]
  unfold buresSq
  ring

/-- Explicit optimal factor for an invertible source. -/
theorem exists_bures_factor_of_det_ne_zero (R : PSDSqrt n) {X Y : RMat n} (hX : X.PosSemidef)
    (hY : Y.PosSemidef) (hdet : X.det ≠ 0) :
    ∃ P : RMat n, P * Pᵀ = Y ∧
      (R.sqrt X * P).trace = (R.sqrt (R.sqrt X * Y * R.sqrt X)).trace := by
  refine ⟨buresMap R X Y * R.sqrt X, ?_, by rw [sqrt_mul_buresFactor hX hdet]⟩
  rw [Matrix.transpose_mul, R.transpose_sqrt hX, buresMap_transpose hX hY, Matrix.mul_assoc,
    ← Matrix.mul_assoc (R.sqrt X), R.sqrt_mul_sqrt X hX, ← Matrix.mul_assoc]
  exact buresMap_push hX hY hdet

/-! ### Continuity of the square root along PSD sequences -/

theorem sq_entry_le_trace_of_mul_self {B A : RMat n} (hB : Bᵀ = B) (hBA : B * B = A)
    (i j : Fin n) : B i j ^ 2 ≤ A.trace := by
  have htr : A.trace = ∑ a, ∑ b, B a b ^ 2 := by
    rw [← hBA]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    have hba : B b a = B a b := by
      have := congrFun (congrFun hB a) b
      simpa [Matrix.transpose_apply] using this
    rw [hba, sq]
  rw [htr]
  calc B i j ^ 2 ≤ ∑ b, B i b ^ 2 :=
        Finset.single_le_sum (f := fun b ↦ B i b ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ b, B a b ^ 2 :=
        Finset.single_le_sum (f := fun a ↦ ∑ b, B a b ^ 2)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)

theorem norm_le_of_entry_sq_le {B : RMat n} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i j, B i j ^ 2 ≤ C) :
    ‖B‖ ≤ Real.sqrt C := by
  rw [Matrix.norm_le_iff (Real.sqrt_nonneg C)]
  intro i j
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (h i j)

theorem sqrt_tendsto (R : PSDSqrt n) {A : ℕ → RMat n} {A0 : RMat n}
    (hA : ∀ j, (A j).PosSemidef) (hA0 : A0.PosSemidef) (hlim : Tendsto A atTop (𝓝 A0)) :
    Tendsto (fun j ↦ R.sqrt (A j)) atTop (𝓝 (R.sqrt A0)) := by
  have htr : Tendsto (fun j ↦ (A j).trace) atTop (𝓝 A0.trace) :=
    ((continuous_id.matrix_trace).tendsto A0).comp hlim
  obtain ⟨C, hC⟩ := htr.bddAbove_range
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hbound : ∀ j, R.sqrt (A j) ∈ Metric.closedBall (0 : RMat n) (Real.sqrt (max C 0)) := by
    intro j
    rw [Metric.mem_closedBall, dist_zero_right]
    refine norm_le_of_entry_sq_le hC0 fun a b ↦ ?_
    have h1 := sq_entry_le_trace_of_mul_self (R.transpose_sqrt (hA j))
      (R.sqrt_mul_sqrt _ (hA j)) a b
    have h2 : (A j).trace ≤ C := hC ⟨j, rfl⟩
    exact h1.trans (h2.trans (le_max_left _ _))
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨B0, _, φ, hφ, hB0⟩ := (isCompact_closedBall (0 : RMat n) (Real.sqrt (max C 0))).tendsto_subseq
    (fun k ↦ hbound (ns k))
  refine ⟨φ, ?_⟩
  have hsub : Tendsto (fun k ↦ A (ns (φ k))) atTop (𝓝 A0) :=
    hlim.comp (hns.comp hφ.tendsto_atTop)
  have hB0psd : B0.PosSemidef :=
    ReactionZero.WeightedSet.isClosed_setOf_posSemidef.mem_of_tendsto hB0
      (Eventually.of_forall fun k ↦ R.posSemidef_sqrt _ (hA (ns (φ k))))
  have hmul : Tendsto (fun k ↦ R.sqrt (A (ns (φ k))) * R.sqrt (A (ns (φ k)))) atTop
      (𝓝 (B0 * B0)) := matrix_product_tendsto hB0 hB0
  have heq : (fun k ↦ R.sqrt (A (ns (φ k))) * R.sqrt (A (ns (φ k)))) =
      fun k ↦ A (ns (φ k)) := funext fun k ↦ R.sqrt_mul_sqrt _ (hA (ns (φ k)))
  rw [heq] at hmul
  have hBB : B0 * B0 = A0 := tendsto_nhds_unique hmul hsub
  rw [R.eq_sqrt_of_mul_self A0 B0 hA0 hB0psd hBB]
  exact hB0

/-! ### Regularization -/

/-- `δ_j = 1/(j+1)`. -/
def regSeq (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem regSeq_pos (j : ℕ) : 0 < regSeq j := by
  unfold regSeq
  positivity

theorem tendsto_regSeq : Tendsto regSeq atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_add_regSeq (X : RMat n) :
    Tendsto (fun j ↦ X + regSeq j • (1 : RMat n)) atTop (𝓝 X) := by
  have h : Tendsto (fun j ↦ regSeq j • (1 : RMat n)) atTop (𝓝 ((0 : ℝ) • (1 : RMat n))) :=
    tendsto_regSeq.smul_const (1 : RMat n)
  rw [zero_smul] at h
  simpa using (tendsto_const_nhds (x := X)).add h

theorem tendsto_congr_mul {S : ℕ → RMat n} {S0 : RMat n} {Y : ℕ → RMat n} {Y0 : RMat n}
    (hS : Tendsto S atTop (𝓝 S0)) (hY : Tendsto Y atTop (𝓝 Y0)) :
    Tendsto (fun j ↦ S j * Y j * S j) atTop (𝓝 (S0 * Y0 * S0)) :=
  (hS.mul hY).mul hS

/-- The regularized inner square roots converge to the Bures inner square root. -/
theorem tendsto_reg_inner (R : PSDSqrt n) {X Y : RMat n} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    Tendsto (fun j ↦ R.sqrt (R.sqrt (X + regSeq j • (1 : RMat n)) * (Y + regSeq j • (1 : RMat n)) *
        R.sqrt (X + regSeq j • (1 : RMat n)))) atTop
      (𝓝 (R.sqrt (R.sqrt X * Y * R.sqrt X))) := by
  have hXj : ∀ j, (X + regSeq j • (1 : RMat n)).PosSemidef :=
    fun j ↦ posSemidef_add_smul_one hX (regSeq_pos j).le
  have hYj : ∀ j, (Y + regSeq j • (1 : RMat n)).PosSemidef :=
    fun j ↦ posSemidef_add_smul_one hY (regSeq_pos j).le
  have hS := sqrt_tendsto R hXj hX (tendsto_add_regSeq X)
  have hin := tendsto_congr_mul hS (tendsto_add_regSeq Y)
  exact sqrt_tendsto R
    (fun j ↦ posSemidef_congr_symm (R.transpose_sqrt (hXj j)) (hYj j))
    (posSemidef_congr_symm (R.transpose_sqrt hX) hY) hin

theorem tendsto_reg_buresSq (R : PSDSqrt n) {X Y : RMat n} (hX : X.PosSemidef)
    (hY : Y.PosSemidef) :
    Tendsto (fun j ↦ X.trace + Y.trace - 2 * (R.sqrt (R.sqrt (X + regSeq j • (1 : RMat n)) *
        (Y + regSeq j • (1 : RMat n)) * R.sqrt (X + regSeq j • (1 : RMat n)))).trace) atTop
      (𝓝 (buresSq R X Y)) := by
  have h := ((continuous_id.matrix_trace).tendsto _).comp (tendsto_reg_inner R hX hY)
  exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul h))

/-- Optimal factor for arbitrary PSD endpoints (Procrustes by compactness). -/
theorem exists_bures_factor (R : PSDSqrt n) {X Y : RMat n} (hX : X.PosSemidef)
    (hY : Y.PosSemidef) :
    ∃ P : RMat n, P * Pᵀ = Y ∧
      (R.sqrt X * P).trace = (R.sqrt (R.sqrt X * Y * R.sqrt X)).trace := by
  have hXj : ∀ j, (X + regSeq j • (1 : RMat n)).PosSemidef :=
    fun j ↦ posSemidef_add_smul_one hX (regSeq_pos j).le
  have hdet : ∀ j, (X + regSeq j • (1 : RMat n)).det ≠ 0 :=
    fun j ↦ det_add_smul_one_ne_zero hX (regSeq_pos j)
  choose P hPP hPtr using fun j ↦ exists_bures_factor_of_det_ne_zero R (hXj j) hY (hdet j)
  have hbound : ∀ j, P j ∈ Metric.closedBall (0 : RMat n) (Real.sqrt (max Y.trace 0)) := by
    intro j
    rw [Metric.mem_closedBall, dist_zero_right]
    refine norm_le_of_entry_sq_le (le_max_right _ _) fun a b ↦ ?_
    have hdiag : P j a b ^ 2 ≤ Y.trace := by
      rw [← hPP j]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
      calc P j a b ^ 2 ≤ ∑ c, P j a c * P j a c := by
            rw [sq]
            exact Finset.single_le_sum (f := fun c ↦ P j a c * P j a c)
              (fun _ _ ↦ mul_self_nonneg _) (Finset.mem_univ b)
        _ ≤ ∑ i, ∑ c, P j i c * P j i c :=
            Finset.single_le_sum (f := fun i ↦ ∑ c, P j i c * P j i c)
              (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _) (Finset.mem_univ a)
    exact hdiag.trans (le_max_left _ _)
  obtain ⟨P0, _, φ, hφ, hP0⟩ :=
    (isCompact_closedBall (0 : RMat n) (Real.sqrt (max Y.trace 0))).tendsto_subseq hbound
  refine ⟨P0, ?_, ?_⟩
  · have hgram : Tendsto (fun k ↦ P (φ k) * (P (φ k))ᵀ) atTop (𝓝 (P0 * P0ᵀ)) :=
      matrix_product_tendsto hP0 ((continuous_id.matrix_transpose.tendsto P0).comp hP0)
    have hconst : (fun k ↦ P (φ k) * (P (φ k))ᵀ) = fun _ ↦ Y := funext fun k ↦ hPP (φ k)
    rw [hconst] at hgram
    exact (tendsto_nhds_unique hgram tendsto_const_nhds)
  · have hS : Tendsto (fun k ↦ R.sqrt (X + regSeq (φ k) • (1 : RMat n))) atTop (𝓝 (R.sqrt X)) :=
      (sqrt_tendsto R hXj hX (tendsto_add_regSeq X)).comp hφ.tendsto_atTop
    have hleft : Tendsto (fun k ↦ (R.sqrt (X + regSeq (φ k) • (1 : RMat n)) * P (φ k)).trace)
        atTop (𝓝 ((R.sqrt X * P0).trace)) :=
      ((continuous_id.matrix_trace).tendsto _).comp (matrix_product_tendsto hS hP0)
    have hYj : ∀ j, (X + regSeq j • (1 : RMat n)).PosSemidef := hXj
    have hin : Tendsto (fun j ↦ R.sqrt (X + regSeq j • (1 : RMat n)) * Y *
        R.sqrt (X + regSeq j • (1 : RMat n))) atTop (𝓝 (R.sqrt X * Y * R.sqrt X)) :=
      tendsto_congr_mul (sqrt_tendsto R hXj hX (tendsto_add_regSeq X)) tendsto_const_nhds
    have hF : Tendsto (fun j ↦ R.sqrt (R.sqrt (X + regSeq j • (1 : RMat n)) * Y *
        R.sqrt (X + regSeq j • (1 : RMat n)))) atTop (𝓝 (R.sqrt (R.sqrt X * Y * R.sqrt X))) :=
      sqrt_tendsto R (fun j ↦ posSemidef_congr_symm (R.transpose_sqrt (hYj j)) hY)
        (posSemidef_congr_symm (R.transpose_sqrt hX) hY) hin
    have hright : Tendsto (fun k ↦ (R.sqrt (X + regSeq (φ k) • (1 : RMat n)) * P (φ k)).trace)
        atTop (𝓝 ((R.sqrt (R.sqrt X * Y * R.sqrt X)).trace)) := by
      have h := ((continuous_id.matrix_trace).tendsto _).comp (hF.comp hφ.tendsto_atTop)
      refine h.congr fun k ↦ ?_
      exact (hPtr (φ k)).symm
    exact tendsto_nhds_unique hleft hright

/-! ### Regularized data for the dual certificate -/

/-- For `δ > 0`, the Bures map between `X + δ I` and `Y + δ I`. -/
def regMap (R : PSDSqrt n) (X Y : RMat n) (δ : ℝ) : RMat n :=
  buresMap R (X + δ • (1 : RMat n)) (Y + δ • (1 : RMat n))

theorem regMap_push (R : PSDSqrt n) {X Y : RMat n} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) :
    regMap R X Y δ * (X + δ • (1 : RMat n)) * regMap R X Y δ = Y + δ • (1 : RMat n) :=
  buresMap_push (posSemidef_add_smul_one hX hδ.le) (posSemidef_add_smul_one hY hδ.le)
    (det_add_smul_one_ne_zero hX hδ)

theorem regMap_transpose (R : PSDSqrt n) {X Y : RMat n} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {δ : ℝ} (hδ : 0 ≤ δ) : (regMap R X Y δ)ᵀ = regMap R X Y δ :=
  buresMap_transpose (posSemidef_add_smul_one hX hδ) (posSemidef_add_smul_one hY hδ)

theorem regMap_posSemidef (R : PSDSqrt n) {X Y : RMat n} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {δ : ℝ} (hδ : 0 ≤ δ) : (regMap R X Y δ).PosSemidef :=
  buresMap_posSemidef (posSemidef_add_smul_one hX hδ) (posSemidef_add_smul_one hY hδ)

theorem trace_regMap_mul (R : PSDSqrt n) {X Y : RMat n} (hX : X.PosSemidef) {δ : ℝ}
    (hδ : 0 < δ) :
    (regMap R X Y δ * (X + δ • (1 : RMat n))).trace =
      (R.sqrt (R.sqrt (X + δ • (1 : RMat n)) * (Y + δ • (1 : RMat n)) *
        R.sqrt (X + δ • (1 : RMat n)))).trace :=
  trace_buresMap_mul (posSemidef_add_smul_one hX hδ.le) (det_add_smul_one_ne_zero hX hδ)

theorem det_regMap_ne_zero (R : PSDSqrt n) {X Y : RMat n} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) : (regMap R X Y δ).det ≠ 0 := by
  intro h
  have hpush := congrArg Matrix.det (regMap_push R hX hY hδ)
  rw [Matrix.det_mul, Matrix.det_mul, h, zero_mul, mul_zero] at hpush
  exact det_add_smul_one_ne_zero hY hδ hpush.symm

#print axioms sqrt_tendsto
#print axioms exists_bures_factor
#print axioms frobeniusSq_factor_sub
#print axioms tendsto_reg_buresSq
#print axioms regMap_push

end MatrixTransport.EntrywiseBures
