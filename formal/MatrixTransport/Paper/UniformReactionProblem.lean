import MatrixTransport.EntrywiseBures.EndpointDensity

/-! # Uniform PSD endpoints for the original continuity equation -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LiZouTransport.Reaction

open MatrixTransport
open MatrixTransport.ReactionZero.ClosedDomain
open MatrixTransport.ReactionZero.Limit
open MatrixTransport.EntrywiseBures

variable {d n k : ℕ} {Ω : Set (Space d)}

def uniformEndpoint (μ : Measure ↥Ω) [IsFiniteMeasure μ] (A : RMat n) :
    (Fin n × Fin n) → SignedMeasure ↥Ω :=
  fun ij ↦ μ.withDensityᵥ (fun _ ↦ A ij.1 ij.2)

theorem uniformEndpoint_apply (μ : Measure ↥Ω) [IsFiniteMeasure μ] (A : RMat n)
    {s : Set ↥Ω} (hs : MeasurableSet s) (i j : Fin n) :
    uniformEndpoint μ A (i, j) s = μ.real s * A i j := by
  unfold uniformEndpoint
  rw [withDensityᵥ_apply (integrable_const _) hs]
  simp [Measure.real, integral_const]

theorem uniformEndpoint_posSemidef (μ : Measure ↥Ω) [IsFiniteMeasure μ]
    {A : RMat n} (hA : A.PosSemidef) : EndpointPositiveSemidefinite (uniformEndpoint μ A) := by
  intro s hs
  have heq : (fun i j ↦ uniformEndpoint μ A (i, j) s) = μ.real s • A := by
    ext i j
    rw [uniformEndpoint_apply μ A hs]
    rfl
  rw [heq]
  exact hA.smul ENNReal.toReal_nonneg

theorem totalMatrix_uniformEndpoint (μ : Measure ↥Ω) [IsFiniteMeasure μ] (A : RMat n) :
    totalMatrix (uniformEndpoint μ A) = μ.real univ • A := by
  ext i j
  exact uniformEndpoint_apply μ A MeasurableSet.univ i j

theorem totalMatrix_uniformEndpoint_probability (μ : Measure ↥Ω) [IsFiniteMeasure μ]
    (hμ : μ univ = 1) (A : RMat n) : totalMatrix (uniformEndpoint μ A) = A := by
  rw [totalMatrix_uniformEndpoint]
  simp [Measure.real, hμ]

variable [Fact (IsCompact Ω)]

theorem endpointPair_uniformEndpoint (μ : Measure ↥Ω) [IsFiniteMeasure μ] (A : RMat n)
    (φ : ClosedC1Jet Ω n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    endpointPair (uniformEndpoint μ A) φ t ht =
      ∫ x, ReactionZero.frob (φ.value (timeBoundary t ht x)) A ∂μ := by
  have hcont : ∀ i j, Continuous fun x ↦ φ.value (timeBoundary t ht x) i j := fun i j ↦
    (continuous_apply j).comp ((continuous_apply i).comp
      (φ.value.continuous.comp (timeBoundary t ht).continuous))
  have hint : ∀ i j, Integrable (fun x ↦ φ.value (timeBoundary t ht x) i j * A i j) μ :=
    fun i j ↦ ((hcont i j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).mul_const _
  unfold endpointPair ReactionZero.frob uniformEndpoint
  rw [integral_finsetSum Finset.univ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum Finset.univ fun j _ ↦ hint i j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  apply signedPair_withDensityᵥ μ measurable_const (integrable_const _) (hcont i j).measurable
  let f : C(↥Ω, ℝ) := ⟨_, hcont i j⟩
  exact ⟨‖f‖, fun x ↦ by
    simpa only [Real.norm_eq_abs, f, ContinuousMap.coe_mk] using f.norm_coe_le_norm x⟩

def uniformProblem (D : AdjointOperator d n k) (μ : Measure ↥Ω) [IsFiniteMeasure μ]
    (A0 A1 : RMat n) (hA0 : A0.PosSemidef) (hA1 : A1.PosSemidef) : Problem Ω n k where
  operator := D
  initial := uniformEndpoint μ A0
  terminal := uniformEndpoint μ A1
  initial_positive := uniformEndpoint_posSemidef μ hA0
  terminal_positive := uniformEndpoint_posSemidef μ hA1

#print axioms uniformEndpoint_posSemidef
#print axioms endpointPair_uniformEndpoint
end LiZouTransport.Reaction
