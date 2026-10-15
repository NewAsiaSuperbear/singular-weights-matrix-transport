import MatrixTransport.PartialWeights.KernelExtinction

/-!
# Frobenius variation of any matrix channel and its right products

Matrix coordinates are flattened into Euclidean space, whose norm is the Frobenius
norm. The variation is Mathlib's vector-measure variation, rather than a sum of
coordinate variations or the default matrix norm.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.Paper.FrobeniusVariation

variable {m r p : ℕ} {X : Type*} [MeasurableSpace X]

def flatten (A : Matrix (Fin m) (Fin p) ℝ) : EuclideanSpace ℝ (Fin m × Fin p) :=
  WithLp.toLp 2 (fun a ↦ A a.1 a.2)

@[simp] theorem flatten_apply (A : Matrix (Fin m) (Fin p) ℝ) (a : Fin m × Fin p) :
    flatten A a = A a.1 a.2 := rfl

theorem flatten_norm (A : Matrix (Fin m) (Fin p) ℝ) :
    ‖flatten A‖ = Real.sqrt (ReactionZero.frobeniusSq A) := by
  simp only [EuclideanSpace.norm_eq, flatten_apply, Real.norm_eq_abs, sq_abs,
    ReactionZero.frobeniusSq, Fintype.sum_prod_type]

def densityVectorMeasure (ρ : Measure X) (F : X → Matrix (Fin m) (Fin p) ℝ) :
    VectorMeasure X (EuclideanSpace ℝ (Fin m × Fin p)) :=
  ρ.withDensityᵥ (fun x ↦ flatten (F x))

theorem integrable_flatten (ρ : Measure X) (F : X → Matrix (Fin m) (Fin p) ℝ)
    (hf : ∀ i j, Integrable (fun x ↦ F x i j) ρ) :
    Integrable (fun x ↦ flatten (F x)) ρ :=
  Integrable.of_eval_piLp (fun a ↦ hf a.1 a.2)

theorem densityVectorMeasure_apply (ρ : Measure X) (F : X → Matrix (Fin m) (Fin p) ℝ)
    (hf : ∀ i j, Integrable (fun x ↦ F x i j) ρ) {S : Set X} (hS : MeasurableSet S)
    (i : Fin m) (j : Fin p) :
    densityVectorMeasure ρ F S (i, j) = ρ.withDensityᵥ (fun x ↦ F x i j) S := by
  rw [densityVectorMeasure, withDensityᵥ_apply (integrable_flatten ρ F hf) hS]
  rw [eval_integral_piLp (f := fun x ↦ flatten (F x))
    (μ := ρ.restrict S) (fun a ↦ (hf a.1 a.2).integrableOn) (i, j),
    withDensityᵥ_apply (hf i j) hS]
  rfl

theorem densityVectorMeasure_variation (ρ : Measure X)
    (F : X → Matrix (Fin m) (Fin p) ℝ) (hf : ∀ i j, Integrable (fun x ↦ F x i j) ρ) :
    (densityVectorMeasure ρ F).variation univ =
      ∫⁻ x, ENNReal.ofReal (Real.sqrt (ReactionZero.frobeniusSq (F x))) ∂ρ := by
  rw [densityVectorMeasure, Measure.variation_withDensityᵥ (integrable_flatten ρ F hf),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, flatten_norm]

theorem densityVectorMeasure_eq_of_coordinates
    (ρ ν : Measure X) (F G : X → Matrix (Fin m) (Fin p) ℝ)
    (hf : ∀ i j, Integrable (fun x ↦ F x i j) ρ)
    (hg : ∀ i j, Integrable (fun x ↦ G x i j) ν)
    (hcoord : ∀ i j, ρ.withDensityᵥ (fun x ↦ F x i j) =
      ν.withDensityᵥ (fun x ↦ G x i j)) : densityVectorMeasure ρ F = densityVectorMeasure ν G := by
  ext S hS a
  rw [densityVectorMeasure_apply ρ F hf hS a.1 a.2,
    densityVectorMeasure_apply ν G hg hS a.1 a.2, hcoord]

theorem frobenius_integral_reference_independent
    (ρ ν : Measure X) (F G : X → Matrix (Fin m) (Fin p) ℝ)
    (hf : ∀ i j, Integrable (fun x ↦ F x i j) ρ)
    (hg : ∀ i j, Integrable (fun x ↦ G x i j) ν)
    (hcoord : ∀ i j, ρ.withDensityᵥ (fun x ↦ F x i j) =
      ν.withDensityᵥ (fun x ↦ G x i j)) :
    (∫⁻ x, ENNReal.ofReal (Real.sqrt (ReactionZero.frobeniusSq (F x))) ∂ρ) =
      ∫⁻ x, ENNReal.ofReal (Real.sqrt (ReactionZero.frobeniusSq (G x))) ∂ν := by
  rw [← densityVectorMeasure_variation ρ F hf, ← densityVectorMeasure_variation ν G hg,
    densityVectorMeasure_eq_of_coordinates ρ ν F G hf hg hcoord]

variable {ι : Type*} [Fintype ι]

def channelDensity (μ : ι → SignedMeasure X) (channel : Fin m × Fin r → ι) (x : X) :
    Matrix (Fin m) (Fin r) ℝ := fun i j ↦ (μ (channel (i, j))).rnDeriv (jointReference μ) x

def rightChannelMeasure (μ : ι → SignedMeasure X) (channel : Fin m × Fin r → ι)
    (A : Matrix (Fin r) (Fin p) ℝ) (i : Fin m) (j : Fin p) : SignedMeasure X :=
  ∑ a, A a j • μ (channel (i, a))

theorem integrable_rightChannelDensity (μ : ι → SignedMeasure X)
    (channel : Fin m × Fin r → ι) (A : Matrix (Fin r) (Fin p) ℝ) (i : Fin m) (j : Fin p) :
    Integrable (fun x ↦ (channelDensity μ channel x * A) i j) (jointReference μ) := by
  simp only [Matrix.mul_apply, channelDensity]
  apply integrable_finsetSum
  intro a _
  exact (integrable_rnDeriv_jointReference μ _).mul_const _

theorem withDensity_rightChannelMeasure (μ : ι → SignedMeasure X)
    (channel : Fin m × Fin r → ι) (A : Matrix (Fin r) (Fin p) ℝ) (i : Fin m) (j : Fin p) :
    (jointReference μ).withDensityᵥ (fun x ↦ (channelDensity μ channel x * A) i j) =
      rightChannelMeasure μ channel A i j := by
  simp only [Matrix.mul_apply, channelDensity, mul_comm]
  rw [PartialReaction.withDensity_finiteSum]
  · unfold rightChannelMeasure
    apply Finset.sum_congr rfl
    intro a _
    have h := withDensityᵥ_smul' (μ := jointReference μ)
      (fun x ↦ (μ (channel (i, a))).rnDeriv (jointReference μ) x) (A a j)
    simp only [smul_eq_mul] at h
    rw [h, withDensityᵥ_rnDeriv_jointReference]
  · intro a
    exact (integrable_rnDeriv_jointReference μ _).const_mul _

def rightChannelVectorMeasure (μ : ι → SignedMeasure X) (channel : Fin m × Fin r → ι)
    (A : Matrix (Fin r) (Fin p) ℝ) : VectorMeasure X (EuclideanSpace ℝ (Fin m × Fin p)) :=
  densityVectorMeasure (jointReference μ) (fun x ↦ channelDensity μ channel x * A)

theorem rightChannelVectorMeasure_coordinate (μ : ι → SignedMeasure X)
    (channel : Fin m × Fin r → ι) (A : Matrix (Fin r) (Fin p) ℝ)
    {S : Set X} (hS : MeasurableSet S) (i : Fin m) (j : Fin p) :
    rightChannelVectorMeasure μ channel A S (i, j) = rightChannelMeasure μ channel A i j S := by
  rw [rightChannelVectorMeasure,
    densityVectorMeasure_apply _ _ (integrable_rightChannelDensity μ channel A) hS,
    withDensity_rightChannelMeasure]

theorem rightChannelVectorMeasure_variation (μ : ι → SignedMeasure X)
    (channel : Fin m × Fin r → ι) (A : Matrix (Fin r) (Fin p) ℝ) :
    (rightChannelVectorMeasure μ channel A).variation univ =
      ∫⁻ x, ENNReal.ofReal (Real.sqrt
        (ReactionZero.frobeniusSq (channelDensity μ channel x * A))) ∂jointReference μ :=
  densityVectorMeasure_variation _ _ (integrable_rightChannelDensity μ channel A)

section OriginalChannels

variable {n k : ℕ}

theorem rightFluxFrobeniusTV_eq_variation (μ : ReactionZero.Coord n k → SignedMeasure X)
    (A : Matrix (Fin k) (Fin p) ℝ) :
    PartialWeights.rightFluxFrobeniusTV μ A =
      (rightChannelVectorMeasure μ (fun a ↦ Sum.inr (Sum.inl a)) A).variation univ := by
  exact (rightChannelVectorMeasure_variation μ (fun a ↦ Sum.inr (Sum.inl a)) A).symm

theorem rightReactionFrobeniusTV_eq_variation (μ : ReactionZero.Coord n k → SignedMeasure X)
    (A : Matrix (Fin n) (Fin p) ℝ) :
    PartialReaction.rightReactionFrobeniusTV μ A =
      (rightChannelVectorMeasure μ (fun a ↦ Sum.inr (Sum.inr a)) A).variation univ := by
  exact (rightChannelVectorMeasure_variation μ (fun a ↦ Sum.inr (Sum.inr a)) A).symm

theorem rightMassFrobeniusTV_eq_variation (μ : ReactionZero.Coord n k → SignedMeasure X)
    (A : Matrix (Fin n) (Fin p) ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.sqrt
      (ReactionZero.frobeniusSq (ReactionZero.mass (ReactionZero.density μ x) * A)))
      ∂jointReference μ) = (rightChannelVectorMeasure μ Sum.inl A).variation univ := by
  exact (rightChannelVectorMeasure_variation μ Sum.inl A).symm

theorem rightFluxMeasure_eq_rightChannelMeasure (μ : ReactionZero.Coord n k → SignedMeasure X)
    (A : Matrix (Fin k) (Fin p) ℝ) (i : Fin n) (j : Fin p) :
    PartialWeights.rightFluxMeasure μ A i j =
      rightChannelMeasure μ (fun a ↦ Sum.inr (Sum.inl a)) A i j := rfl

theorem rightReactionMeasure_eq_rightChannelMeasure
    (μ : ReactionZero.Coord n k → SignedMeasure X)
    (A : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) (j : Fin p) :
    PartialReaction.rightReactionMeasure μ A i j =
      rightChannelMeasure μ (fun a ↦ Sum.inr (Sum.inr a)) A i j := rfl

end OriginalChannels

#print axioms densityVectorMeasure_variation
#print axioms frobenius_integral_reference_independent
#print axioms rightChannelVectorMeasure_coordinate
#print axioms rightChannelVectorMeasure_variation
#print axioms rightFluxFrobeniusTV_eq_variation
#print axioms rightReactionFrobeniusTV_eq_variation
#print axioms rightMassFrobeniusTV_eq_variation

end MatrixTransport.Paper.FrobeniusVariation
