import MatrixTransport.Paper.RotatingReactionAlgebra
import MatrixTransport.EntrywiseBures.UniformBures
import MatrixTransport.EntrywiseBures.ReactionPiece

/-! # Exact original minima for the rotating-reaction example -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Matrix

namespace MatrixTransport.Paper.RotatingReaction
open MatrixTransport.EntrywiseBures
open MatrixTransport.ReactionZero.ClosedDomain
open MatrixTransport.ReactionZero.Limit
open LiZouTransport.Reaction

variable {d n k : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

def rotationProblem (D : AdjointOperator d 2 k) (μ : Measure ↥Ω) [IsFiniteMeasure μ] :
    Problem Ω 2 k :=
  uniformProblem D μ endpoint0 endpoint1 Matrix.PosSemidef.one endpoint1_posSemidef

/-- The exact formula is the infimum over the complete original signed-Radon class. -/
theorem rotation_minimum_eq (G : HubGeometry d Ω) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℝ} (hε : 0 < ε) :
    minimumValue (rotationProblem D μ) L (reactionWeight ε θ) =
      ENNReal.ofReal (rationalizedValue ε (Real.sin θ ^ 2)) := by
  have hu : IsUnit (reactionWeight ε θ).det := by
    rw [reactionWeight_det, isUnit_iff_ne_zero]
    exact ne_of_gt hε
  have h := uniform_reaction_minimumValue (canonicalPSDSqrt 2) G D hD0 μ hμ
    (reactionWeight_transpose ε θ) hu Matrix.PosSemidef.one endpoint1_posSemidef L
  change minimumValue (rotationProblem D μ) L (reactionWeight ε θ) =
    ENNReal.ofReal (buresValue (canonicalPSDSqrt 2) (reactionWeight ε θ)
      endpoint0 endpoint1) at h
  rw [buresValue_rotation (canonicalPSDSqrt 2) hε] at h
  exact h

/-- The limit's unchanged kernel component is retained in the explicit upper path. -/
theorem singular_minimum_eq (G : HubGeometry d Ω) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) :
    minimumValue (rotationProblem D μ) L singularWeight = ENNReal.ofReal targetValue := by
  apply le_antisymm
  · let path := LiZouTransport.Reaction.reactionPath (k := k) μ singularWeight (1 : Mat) growthIncrement 0 1
      ⟨le_rfl, zero_le_one⟩ (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
    have h0 := gram_identity
    have h1 : ReactionZero.gram ((1 : Mat) + singularWeight * growthIncrement) =
        endpoint1 := by
      rw [singularWeight_mul_growthIncrement, one_add_growthIncrement, gram_growthFactor]
    have hg : Good (rotationProblem D μ) path := by
      simpa only [rotationProblem, path, h0, h1] using
        reactionPath_good_uniform G D μ singularWeight_transpose (1 : Mat) growthIncrement
    have hmin : minimumValue (rotationProblem D μ) L singularWeight ≤
        ReactionZero.action L singularWeight path := by
      unfold minimumValue ReactionZero.constrainedInfimum
      exact iInf_le_of_le path (iInf_le_of_le hg le_rfl)
    have hupper := LiZouTransport.Reaction.reactionPath_action_le μ L singularWeight_transpose
      (1 : Mat) growthIncrement 0 1 ⟨le_rfl, zero_le_one⟩
      (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
    exact hmin.trans (by
      simpa only [div_one, hμ, mul_one, frobeniusSq_growthIncrement] using hupper)
  · apply targetValue_le_minimumValue (canonicalPSDSqrt 2) (rotationProblem D μ) hD0
    · exact totalMatrix_uniformEndpoint_probability μ hμ endpoint0
    · exact totalMatrix_uniformEndpoint_probability μ hμ endpoint1

theorem rotation_minimum_toReal_eq (G : HubGeometry d Ω) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℝ} (hε : 0 < ε) :
    (minimumValue (rotationProblem D μ) L (reactionWeight ε θ)).toReal =
      rationalizedValue ε (Real.sin θ ^ 2) := by
  rw [rotation_minimum_eq G D hD0 μ hμ L hε,
    ENNReal.toReal_ofReal (rotationValue_nonneg hε)]

/-- The finite scale classification concerns the original minimum values. -/
theorem rotation_minimum_finite_limit (G : HubGeometry d Ω) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℕ → ℝ} {ℓ : ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ Real.sin (θ j) ^ 2 / ε j) atTop (𝓝 ℓ)) :
    Tendsto (fun j ↦ (minimumValue (rotationProblem D μ) L
      (reactionWeight (ε j) (θ j))).toReal) atTop (𝓝 (targetValue + ℓ ^ 2 / 2)) := by
  have hp : Tendsto (fun j ↦ Real.sin (θ j) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sin_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using ((Real.continuous_sin.tendsto 0).comp hθ).pow 2
  apply (tendsto_value_finite hε hp hratio).congr
  intro j
  exact (rotation_minimum_toReal_eq G D hD0 μ hμ L (hεpos j)).symm

/-- The infinite `p/ε` case in the extended-limit classification. -/
theorem rotation_minimum_atTop (G : HubGeometry d Ω) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℕ → ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ Real.sin (θ j) ^ 2 / ε j) atTop atTop) :
    Tendsto (fun j ↦ (minimumValue (rotationProblem D μ) L
      (reactionWeight (ε j) (θ j))).toReal) atTop atTop := by
  have hp : Tendsto (fun j ↦ Real.sin (θ j) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sin_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using ((Real.continuous_sin.tendsto 0).comp hθ).pow 2
  apply (tendsto_value_atTop hε hp hratio).congr
  intro j
  exact (rotation_minimum_toReal_eq G D hD0 μ hμ L (hεpos j)).symm

/-- Subcritical and critical angle limits for the original minima, including `a=0`. -/
theorem rotation_minimum_angle_finite_limit (G : HubGeometry d Ω) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℕ → ℝ} {a : ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ θ j / Real.sqrt (ε j)) atTop (𝓝 a)) :
    Tendsto (fun j ↦ (minimumValue (rotationProblem D μ) L
      (reactionWeight (ε j) (θ j))).toReal) atTop (𝓝 (targetValue + a ^ 4 / 2)) := by
  apply (tendsto_value_angle_finite hεpos hε hθ hratio).congr
  intro j
  exact (rotation_minimum_toReal_eq G D hD0 μ hμ L (hεpos j)).symm

/-- Supercritical original minima diverge. -/
theorem rotation_minimum_angle_atTop (G : HubGeometry d Ω) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℕ → ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ |θ j| / Real.sqrt (ε j)) atTop atTop) :
    Tendsto (fun j ↦ (minimumValue (rotationProblem D μ) L
      (reactionWeight (ε j) (θ j))).toReal) atTop atTop := by
  apply (tendsto_value_angle_atTop hεpos hε hθ hratio).congr
  intro j
  exact (rotation_minimum_toReal_eq G D hD0 μ hμ L (hεpos j)).symm

/-- The supercritical equivalence is proved for original minima, with the exact constant. -/
theorem rotation_minimum_angle_asymptotic (G : HubGeometry d Ω) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℕ → ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ |θ j| / Real.sqrt (ε j)) atTop atTop) :
    Tendsto (fun j ↦ (minimumValue (rotationProblem D μ) L
      (reactionWeight (ε j) (θ j))).toReal / (θ j ^ 4 / (2 * ε j ^ 2)))
      atTop (𝓝 1) := by
  apply (tendsto_value_div_angle_scale hεpos hε hθ hratio).congr
  intro j
  rw [rotation_minimum_toReal_eq G D hD0 μ hμ L (hεpos j)]

#print axioms rotation_minimum_eq
#print axioms singular_minimum_eq
#print axioms rotation_minimum_finite_limit
#print axioms rotation_minimum_atTop
#print axioms rotation_minimum_angle_finite_limit
#print axioms rotation_minimum_angle_atTop
#print axioms rotation_minimum_angle_asymptotic
end MatrixTransport.Paper.RotatingReaction
