import MatrixTransport.EntrywiseBures.BuresAlgebra
import MatrixTransport.EntrywiseBures.DualCertificate
import MatrixTransport.EntrywiseBures.CanonicalSqrt
import MatrixTransport.Paper.UniformReactionProblem
import MatrixTransport.EntrywiseBures.ReactionPiece

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.Reaction
open MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures
open MatrixTransport.ReactionZero.Limit
variable {d n k : ℕ} {Ω : Set (Space d)}

/-- A factor of the congruence-transformed endpoint becomes a factor of the original endpoint. -/
theorem gram_weighted_factor {H A P : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    (hP : MatrixTransport.ReactionZero.gram P = H⁻¹ * A * H⁻¹) :
    MatrixTransport.ReactionZero.gram (H * P) = A := by
  have hl := Matrix.mul_nonsing_inv H hHu
  unfold MatrixTransport.ReactionZero.gram at hP ⊢
  rw [Matrix.transpose_mul, hH]
  calc H * P * (Pᵀ * H) = H * (P * Pᵀ) * H := by simp only [Matrix.mul_assoc]
    _ = H * (H⁻¹ * A * H⁻¹) * H := by rw [hP]
    _ = (H * H⁻¹) * A * (H⁻¹ * H) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hl, Matrix.nonsing_inv_mul H hHu, Matrix.one_mul, Matrix.mul_one]

/-- Existing PSD Bures factor construction in the original reaction coordinates. Singular
endpoint matrices are included; only the reaction weight is invertible. -/
theorem exists_bures_reaction_factor (R : PSDSqrt n) {H A0 A1 : RMat n}
    (hH : Hᵀ = H) (hHu : IsUnit H.det) (hA0 : A0.PosSemidef) (hA1 : A1.PosSemidef) :
    ∃ P Δ : RMat n, MatrixTransport.ReactionZero.gram P = A0 ∧
      MatrixTransport.ReactionZero.gram (P + H * Δ) = A1 ∧
      2 * MatrixTransport.ReactionZero.frobeniusSq Δ = buresValue R H A0 A1 := by
  let X0 := H⁻¹ * A0 * H⁻¹
  let X1 := H⁻¹ * A1 * H⁻¹
  have hHi : (H⁻¹)ᵀ = H⁻¹ := transpose_inv_of_symm hH
  have hX0 : X0.PosSemidef := posSemidef_congr_symm hHi hA0
  have hX1 : X1.PosSemidef := posSemidef_congr_symm hHi hA1
  obtain ⟨Q,hQ,htrace⟩ := exists_bures_factor R hX0 hX1
  refine ⟨H * R.sqrt X0, Q - R.sqrt X0, ?_, ?_, ?_⟩
  · exact gram_weighted_factor hH hHu (R.gram_sqrt hX0)
  · have he : H * R.sqrt X0 + H * (Q - R.sqrt X0) = H * Q := by
      rw [Matrix.mul_sub]
      abel
    rw [he]
    exact gram_weighted_factor hH hHu hQ
  · rw [frobeniusSq_factor_sub R hX0 hQ htrace]
    rfl

theorem buresValue_nonneg (R : PSDSqrt n) {H A0 A1 : RMat n}
    (hH : Hᵀ = H) (hHu : IsUnit H.det) (hA0 : A0.PosSemidef) (hA1 : A1.PosSemidef) :
    0 ≤ buresValue R H A0 A1 := by
  obtain ⟨P,Δ,_,_,he⟩ := exists_bures_reaction_factor R hH hHu hA0 hA1
  rw [← he]
  exact mul_nonneg (by norm_num) (MatrixTransport.ReactionZero.frobeniusSq_nonneg Δ)

variable [Fact (IsCompact Ω)]

/-- Weighted Bures lower bound for the actual uniform-endpoint problem at every transport
weight and against the complete original Radon competitor class. -/
theorem uniform_bures_lower (R : PSDSqrt n) (D : AdjointOperator d n k)
    (hD0 : ∀ A : RMat n, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    {H A0 A1 : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    (hA0 : A0.PosSemidef) (hA1 : A1.PosSemidef) (L : Matrix (Fin k) (Fin k) ℝ) :
    ENNReal.ofReal (buresValue R H A0 A1) ≤
      minimumValue (uniformProblem D μ A0 A1 hA0 hA1) L H := by
  have h := buresValue_le_minimumValue R (uniformProblem D μ A0 A1 hA0 hA1)
    hD0 hH hHu L
  simpa only [uniformProblem, totalMatrix_uniformEndpoint_probability μ hμ] using h

/-- Exact weighted Bures minimum for uniform PSD endpoints in the original Radon problem.
The upper bound uses a constructed factor path; the lower bound tests every competitor. -/
theorem uniform_reaction_minimumValue (R : PSDSqrt n) (G : HubGeometry d Ω)
    (D : AdjointOperator d n k)
    (hD0 : ∀ A : RMat n, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    {H A0 A1 : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    (hA0 : A0.PosSemidef) (hA1 : A1.PosSemidef) (L : Matrix (Fin k) (Fin k) ℝ) :
    minimumValue (uniformProblem D μ A0 A1 hA0 hA1) L H =
      ENNReal.ofReal (buresValue R H A0 A1) := by
  apply le_antisymm
  · obtain ⟨P,Δ,hP,hPD,hcost⟩ := exists_bures_reaction_factor R hH hHu hA0 hA1
    have hGood := reactionPath_good_uniform G D μ hH P Δ
    have hGood' : Good (uniformProblem D μ A0 A1 hA0 hA1)
        (reactionPath μ H P Δ 0 1 ⟨le_rfl,zero_le_one⟩
          (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one) := by
      simpa only [hP,hPD] using hGood
    have hAction := reactionPath_action_le μ L hH P Δ 0 1
      ⟨le_rfl,zero_le_one⟩ (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
    have hUpper : MatrixTransport.ReactionZero.action L H
        (reactionPath μ H P Δ 0 1 ⟨le_rfl,zero_le_one⟩
          (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one) ≤
        ENNReal.ofReal (buresValue R H A0 A1) := by
      simpa only [div_one,hμ,mul_one,hcost] using hAction
    exact iInf_le_of_le _ (iInf_le_of_le hGood' hUpper)
  · exact uniform_bures_lower R D hD0 μ hμ hH hHu hA0 hA1 L

#print axioms gram_weighted_factor
#print axioms exists_bures_reaction_factor
#print axioms buresValue_nonneg
#print axioms uniform_bures_lower
#print axioms uniform_reaction_minimumValue
end LiZouTransport.Reaction
