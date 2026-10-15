import MatrixTransport.PartialWeights.LimitTheorem

/-!
# Automatic relative Gram comparison for fixed diagonal directions

Coordinate convergence of diagonal weights constructs a positive comparison factor tending
to one. Active coefficients may approach from either side and need not be monotone. Empty
transport or reaction coordinate sets are included. The original signed Radon conclusions
are then obtained from the already-proved simultaneous partial-weight certificate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialWeights

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {m n k d p q : ℕ}

/-- Only nonzero limiting diagonal directions contribute a relative squared error. -/
def squaredRatioError (a astar : ℝ) : ℝ :=
  if astar = 0 then 0 else |a ^ 2 / astar ^ 2 - 1|

theorem squaredRatioError_nonneg (a astar : ℝ) : 0 ≤ squaredRatioError a astar := by
  unfold squaredRatioError
  split_ifs <;> positivity

theorem squaredRatioError_tendsto_zero (a : ℕ → ℝ) (astar : ℝ)
    (ha : Tendsto a atTop (𝓝 astar)) :
    Tendsto (fun j ↦ squaredRatioError (a j) astar) atTop (𝓝 0) := by
  by_cases hs : astar = 0
  · simpa only [squaredRatioError, hs, ite_true] using
      (tendsto_const_nhds (x := (0 : ℝ)))
  · have h := (((ha.pow 2).div_const (astar ^ 2)).sub_const 1).abs
    simpa only [squaredRatioError, hs, ↓reduceIte, div_self (pow_ne_zero 2 hs),
      sub_self, abs_zero] using h

/-- A finite sum, with value zero also in dimension zero. -/
def diagonalRelativeError (a astar : Fin m → ℝ) : ℝ :=
  ∑ i, squaredRatioError (a i) (astar i)

theorem diagonalRelativeError_nonneg (a astar : Fin m → ℝ) :
    0 ≤ diagonalRelativeError a astar :=
  Finset.sum_nonneg fun _ _ ↦ squaredRatioError_nonneg _ _

theorem squaredRatioError_le_diagonalRelativeError (a astar : Fin m → ℝ) (i : Fin m) :
    squaredRatioError (a i) (astar i) ≤ diagonalRelativeError a astar :=
  Finset.single_le_sum (fun _ _ ↦ squaredRatioError_nonneg _ _) (Finset.mem_univ i)

theorem diagonalRelativeError_tendsto_zero (a : ℕ → Fin m → ℝ)
    (astar : Fin m → ℝ) (ha : ∀ i, Tendsto (fun j ↦ a j i) atTop (𝓝 (astar i))) :
    Tendsto (fun j ↦ diagonalRelativeError (a j) astar) atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ fun i _ ↦
    squaredRatioError_tendsto_zero (fun j ↦ a j i) (astar i) (ha i)
  simpa only [diagonalRelativeError, Finset.sum_const_zero] using h

/-- One factor compares both independently sized diagonal Gram matrices. -/
def diagonalComparisonFactor (l lstar : Fin k → ℝ) (h hstar : Fin n → ℝ) : ℝ :=
  max (1 / 2) (1 - (diagonalRelativeError l lstar + diagonalRelativeError h hstar))

theorem diagonalComparisonFactor_pos (l lstar : Fin k → ℝ) (h hstar : Fin n → ℝ) :
    0 < diagonalComparisonFactor l lstar h hstar :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_left _ _)

theorem diagonalComparisonFactor_le_one (l lstar : Fin k → ℝ)
    (h hstar : Fin n → ℝ) : diagonalComparisonFactor l lstar h hstar ≤ 1 := by
  apply max_le (by norm_num : (1 / 2 : ℝ) ≤ 1)
  linarith [diagonalRelativeError_nonneg l lstar, diagonalRelativeError_nonneg h hstar]

theorem diagonalComparisonFactor_tendsto_one
    (l : ℕ → Fin k → ℝ) (lstar : Fin k → ℝ)
    (hl : ∀ i, Tendsto (fun j ↦ l j i) atTop (𝓝 (lstar i)))
    (h : ℕ → Fin n → ℝ) (hstar : Fin n → ℝ)
    (hh : ∀ i, Tendsto (fun j ↦ h j i) atTop (𝓝 (hstar i))) :
    Tendsto (fun j ↦ diagonalComparisonFactor (l j) lstar (h j) hstar)
      atTop (𝓝 1) := by
  have he := (diagonalRelativeError_tendsto_zero l lstar hl).add
    (diagonalRelativeError_tendsto_zero h hstar hh)
  have hs : Tendsto
      (fun j ↦ 1 - (diagonalRelativeError (l j) lstar +
        diagonalRelativeError (h j) hstar)) atTop (𝓝 1) := by
    simpa only [zero_add, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub he
  simpa only [diagonalComparisonFactor, max_eq_right (by norm_num : (1 / 2 : ℝ) ≤ 1)] using
    (tendsto_const_nhds (x := (1 / 2 : ℝ))).max hs

theorem coefficient_sq_ge_factor (a astar : Fin m → ℝ) (α : ℝ)
    (hα : α ≤ 1 - diagonalRelativeError a astar) (i : Fin m) :
    α * astar i ^ 2 ≤ a i ^ 2 := by
  by_cases hs : astar i = 0
  · simpa only [hs, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using sq_nonneg (a i)
  · have he := squaredRatioError_le_diagonalRelativeError a astar i
    simp only [squaredRatioError, hs, ↓reduceIte] at he
    have hr : α ≤ a i ^ 2 / astar i ^ 2 := by
      linarith [neg_le_abs (a i ^ 2 / astar i ^ 2 - 1)]
    exact (le_div_iff₀ (sq_pos_of_ne_zero hs)).mp hr

theorem gram_diagonal (a : Fin m → ℝ) :
    gram (Matrix.diagonal a) = Matrix.diagonal (fun i ↦ a i ^ 2) := by
  simp only [gram, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, pow_two]

/-- Relative squared-coordinate bounds are the actual PSD diagonal Gram comparison. -/
theorem diagonal_gram_deficit_posSemidef (a astar : Fin m → ℝ) (α : ℝ)
    (hα : α ≤ 1 - diagonalRelativeError a astar) :
    (gram (Matrix.diagonal a) - α • gram (Matrix.diagonal astar)).PosSemidef := by
  rw [gram_diagonal, gram_diagonal, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  change 0 ≤ a i ^ 2 - α * astar i ^ 2
  exact sub_nonneg.mpr (coefficient_sq_ge_factor a astar α hα i)

/-- Coefficient convergence automatically supplies the full two-Gram comparison certificate. -/
theorem exists_diagonal_relative_grams
    (l : ℕ → Fin k → ℝ) (lstar : Fin k → ℝ)
    (hl : ∀ i, Tendsto (fun j ↦ l j i) atTop (𝓝 (lstar i)))
    (h : ℕ → Fin n → ℝ) (hstar : Fin n → ℝ)
    (hh : ∀ i, Tendsto (fun j ↦ h j i) atTop (𝓝 (hstar i))) :
    ∃ α : ℕ → ℝ, (∀ j, 0 < α j ∧ α j ≤ 1) ∧ Tendsto α atTop (𝓝 1) ∧
      ∀ᶠ j in atTop,
        (gram (Matrix.diagonal (l j)) - α j • gram (Matrix.diagonal lstar)).PosSemidef ∧
        (gram (Matrix.diagonal (h j)) - α j • gram (Matrix.diagonal hstar)).PosSemidef := by
  let α := fun j ↦ diagonalComparisonFactor (l j) lstar (h j) hstar
  refine ⟨α, fun j ↦ ⟨diagonalComparisonFactor_pos _ _ _ _,
    diagonalComparisonFactor_le_one _ _ _ _⟩,
    diagonalComparisonFactor_tendsto_one l lstar hl h hstar hh, ?_⟩
  have he : Tendsto
      (fun j ↦ diagonalRelativeError (l j) lstar + diagonalRelativeError (h j) hstar)
      atTop (𝓝 0) := by
    simpa only [zero_add] using (diagonalRelativeError_tendsto_zero l lstar hl).add
      (diagonalRelativeError_tendsto_zero h hstar hh)
  filter_upwards [he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with j hj
  have hclamp : (1 / 2 : ℝ) ≤
      1 - (diagonalRelativeError (l j) lstar + diagonalRelativeError (h j) hstar) := by
    linarith
  have hαl : α j ≤ 1 - diagonalRelativeError (l j) lstar := by
    dsimp [α, diagonalComparisonFactor]
    rw [max_eq_right hclamp]
    linarith [diagonalRelativeError_nonneg (h j) hstar]
  have hαh : α j ≤ 1 - diagonalRelativeError (h j) hstar := by
    dsimp [α, diagonalComparisonFactor]
    rw [max_eq_right hclamp]
    linarith [diagonalRelativeError_nonneg (l j) lstar]
  exact ⟨diagonal_gram_deficit_posSemidef _ _ _ hαl,
    diagonal_gram_deficit_posSemidef _ _ _ hαh⟩

theorem diagonal_tendsto (a : ℕ → Fin m → ℝ) (astar : Fin m → ℝ)
    (ha : ∀ i, Tendsto (fun j ↦ a j i) atTop (𝓝 (astar i))) :
    Tendsto (fun j ↦ Matrix.diagonal (a j)) atTop (𝓝 (Matrix.diagonal astar)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro b
  by_cases hib : i = b
  · subst b
    simpa only [Matrix.diagonal_apply_eq] using ha i
  · simpa only [Matrix.diagonal_apply_ne _ hib] using
      (tendsto_const_nhds (x := (0 : ℝ)))

variable {Ω : Set (ClosedDomain.Space d)} [Fact (IsCompact Ω)]

/-- Original extended minimum convergence for diagonal coefficients, without an extra Gram input. -/
theorem diagonal_minimumValue_tendsto (P : Problem Ω n k)
    (l : ℕ → Fin k → ℝ) (lstar : Fin k → ℝ)
    (hl : ∀ i, Tendsto (fun j ↦ l j i) atTop (𝓝 (lstar i)))
    (h : ℕ → Fin n → ℝ) (hstar : Fin n → ℝ)
    (hh : ∀ i, Tendsto (fun j ↦ h j i) atTop (𝓝 (hstar i))) :
    Tendsto (fun j ↦ minimumValue P (Matrix.diagonal (l j)) (Matrix.diagonal (h j))) atTop
      (𝓝 (minimumValue P (Matrix.diagonal lstar) (Matrix.diagonal hstar))) := by
  obtain ⟨α, hαpos, hα, hG⟩ := exists_diagonal_relative_grams l lstar hl h hstar hh
  exact minimumValue_tendsto_of_eventually_relative_grams P _ _
    (diagonal_tendsto l lstar hl) _ _ (diagonal_tendsto h hstar hh) α hα
    (hG.mono fun j hj ↦ ⟨(hαpos j).1, hj⟩)

/-- The complete original-model conclusion, including rectangular kernel variations.
The conclusion uses only the stated coefficient convergence assumptions. -/
def FixedBasisConclusion (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (p q : ℕ) : Prop :=
  Tendsto (fun j ↦ minimumValue P (L j) (H j)) atTop
    (𝓝 (minimumValue P Lstar Hstar)) ∧
  (minimumValue P Lstar Hstar ≠ ⊤ →
    ∃ ν : Path Ω n k, Good P ν ∧ action Lstar Hstar ν = minimumValue P Lstar Hstar ∧
      ∀ B, MeasurableSet B → (MatrixPositivity.massMeasureValue ν B).PosSemidef) ∧
  (∀ (μ : ℕ → Path Ω n k), (∀ j, Good P (μ j)) →
    ∀ (η : ℕ → ℝ≥0∞), Tendsto η atTop (𝓝 0) →
    (∀ j, action (L j) (H j) (μ j) ≤ minimumValue P (L j) (H j) + η j) →
    Tendsto (fun j ↦ action (L j) (H j) (μ j)) atTop
      (𝓝 (minimumValue P Lstar Hstar)) ∧
    (minimumValue P Lstar Hstar ≠ ⊤ →
      (∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
        SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν ∧
        action Lstar Hstar ν = minimumValue P Lstar Hstar ∧
        ∀ B, MeasurableSet B → (MatrixPositivity.massMeasureValue ν B).PosSemidef) ∧
      (∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (ν : Path Ω n k),
        SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν →
        Good P ν ∧ action Lstar Hstar ν = minimumValue P Lstar Hstar ∧
        ∀ B, MeasurableSet B → (MatrixPositivity.massMeasureValue ν B).PosSemidef) ∧
      (∀ (A : Matrix (Fin k) (Fin p) ℝ), Lstar.transpose * A = 0 →
        Tendsto (fun j ↦ rightFluxFrobeniusTV (μ j) A) atTop (𝓝 0)) ∧
      (∀ (A : Matrix (Fin n) (Fin q) ℝ), Hstar.transpose * A = 0 →
        Tendsto (fun j ↦ PartialReaction.rightReactionFrobeniusTV (μ j) A)
          atTop (𝓝 0))))

/-- Complete diagonal regime from coefficient convergence alone, in arbitrary dimensions. -/
theorem diagonal_partial_weights_regime (P : Problem Ω n k)
    (l : ℕ → Fin k → ℝ) (lstar : Fin k → ℝ)
    (hl : ∀ i, Tendsto (fun j ↦ l j i) atTop (𝓝 (lstar i)))
    (h : ℕ → Fin n → ℝ) (hstar : Fin n → ℝ)
    (hh : ∀ i, Tendsto (fun j ↦ h j i) atTop (𝓝 (hstar i))) :
    FixedBasisConclusion P (fun j ↦ Matrix.diagonal (l j)) (Matrix.diagonal lstar)
      (fun j ↦ Matrix.diagonal (h j)) (Matrix.diagonal hstar) p q := by
  obtain ⟨α, hαpos, hα, hG⟩ := exists_diagonal_relative_grams l lstar hl h hstar hh
  exact partial_weights_regime P _ _ (diagonal_tendsto l lstar hl) _ _
    (diagonal_tendsto h hstar hh) α hα
    (hG.mono fun j hj ↦ ⟨(hαpos j).1, hj⟩)

/-- A single fixed eigenbasis, shared by all terms of a weight sequence. -/
def fixedBasisWeight (U : Matrix (Fin m) (Fin m) ℝ) (a : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  U * Matrix.diagonal a * U.transpose

theorem gram_conjugate_of_orthogonal (U A : Matrix (Fin m) (Fin m) ℝ)
    (hU : U.transpose * U = 1) :
    gram (U * A * U.transpose) = U * gram A * U.transpose := by
  unfold gram
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    U * A * U.transpose * (U * (A.transpose * U.transpose)) =
        U * A * (U.transpose * U) * A.transpose * U.transpose := by
      simp only [Matrix.mul_assoc]
    _ = U * (A * A.transpose) * U.transpose := by
      rw [hU]
      simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem fixedBasisWeight_tendsto (U : Matrix (Fin m) (Fin m) ℝ)
    (a : ℕ → Fin m → ℝ) (astar : Fin m → ℝ)
    (ha : ∀ i, Tendsto (fun j ↦ a j i) atTop (𝓝 (astar i))) :
    Tendsto (fun j ↦ fixedBasisWeight U (a j)) atTop (𝓝 (fixedBasisWeight U astar)) :=
  ((tendsto_const_nhds (x := U)).mul (diagonal_tendsto a astar ha)).mul
    (tendsto_const_nhds (x := U.transpose))

theorem fixedBasis_gram_deficit_posSemidef (U : Matrix (Fin m) (Fin m) ℝ)
    (hU : U.transpose * U = 1) (a astar : Fin m → ℝ) (α : ℝ)
    (hG : (gram (Matrix.diagonal a) - α • gram (Matrix.diagonal astar)).PosSemidef) :
    (gram (fixedBasisWeight U a) - α • gram (fixedBasisWeight U astar)).PosSemidef := by
  have hc := hG.mul_mul_conjTranspose_same U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hc
  simpa only [fixedBasisWeight, gram_conjugate_of_orthogonal U _ hU,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using hc

/-- Nonnegative coefficients give genuine PSD weights in every fixed basis. -/
theorem fixedBasisWeight_posSemidef (U : Matrix (Fin m) (Fin m) ℝ)
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (fixedBasisWeight U a).PosSemidef := by
  have hc := (Matrix.posSemidef_diagonal_iff.mpr ha).mul_mul_conjTranspose_same U
  simpa only [fixedBasisWeight, Matrix.conjTranspose_eq_transpose_of_trivial] using hc

/-- A fixed orthogonal eigenbasis converts coefficient convergence into the same automatic
relative comparison. The two weights may have different fixed bases and dimensions. -/
theorem exists_fixedBasis_relative_grams
    (U : Matrix (Fin k) (Fin k) ℝ) (hU : U.transpose * U = 1)
    (V : Matrix (Fin n) (Fin n) ℝ) (hV : V.transpose * V = 1)
    (l : ℕ → Fin k → ℝ) (lstar : Fin k → ℝ)
    (hl : ∀ i, Tendsto (fun j ↦ l j i) atTop (𝓝 (lstar i)))
    (h : ℕ → Fin n → ℝ) (hstar : Fin n → ℝ)
    (hh : ∀ i, Tendsto (fun j ↦ h j i) atTop (𝓝 (hstar i))) :
    ∃ α : ℕ → ℝ, (∀ j, 0 < α j ∧ α j ≤ 1) ∧ Tendsto α atTop (𝓝 1) ∧
      ∀ᶠ j in atTop,
        (gram (fixedBasisWeight U (l j)) - α j • gram (fixedBasisWeight U lstar)).PosSemidef ∧
        (gram (fixedBasisWeight V (h j)) - α j • gram (fixedBasisWeight V hstar)).PosSemidef := by
  obtain ⟨α, hαpos, hα, hG⟩ := exists_diagonal_relative_grams l lstar hl h hstar hh
  refine ⟨α, hαpos, hα, ?_⟩
  exact hG.mono fun j hj ↦
    ⟨fixedBasis_gram_deficit_posSemidef U hU _ _ _ hj.1,
      fixedBasis_gram_deficit_posSemidef V hV _ _ _ hj.2⟩

/-- Complete original-model partial-weight regime in fixed orthogonal eigenbases.
No monotonicity, positive limiting rank, positive dimension or extra Gram premise is needed. -/
theorem fixedBasis_partial_weights_regime (P : Problem Ω n k)
    (U : Matrix (Fin k) (Fin k) ℝ) (hU : U.transpose * U = 1)
    (V : Matrix (Fin n) (Fin n) ℝ) (hV : V.transpose * V = 1)
    (l : ℕ → Fin k → ℝ) (lstar : Fin k → ℝ)
    (hl : ∀ i, Tendsto (fun j ↦ l j i) atTop (𝓝 (lstar i)))
    (h : ℕ → Fin n → ℝ) (hstar : Fin n → ℝ)
    (hh : ∀ i, Tendsto (fun j ↦ h j i) atTop (𝓝 (hstar i))) :
    FixedBasisConclusion P (fun j ↦ fixedBasisWeight U (l j)) (fixedBasisWeight U lstar)
      (fun j ↦ fixedBasisWeight V (h j)) (fixedBasisWeight V hstar) p q := by
  obtain ⟨α, hαpos, hα, hG⟩ := exists_fixedBasis_relative_grams
    U hU V hV l lstar hl h hstar hh
  exact partial_weights_regime P _ _ (fixedBasisWeight_tendsto U l lstar hl) _ _
    (fixedBasisWeight_tendsto V h hstar hh) α hα
    (hG.mono fun j hj ↦ ⟨(hαpos j).1, hj⟩)

#print axioms exists_diagonal_relative_grams
#print axioms diagonal_partial_weights_regime
#print axioms exists_fixedBasis_relative_grams
#print axioms fixedBasis_partial_weights_regime

end MatrixTransport.PartialWeights
