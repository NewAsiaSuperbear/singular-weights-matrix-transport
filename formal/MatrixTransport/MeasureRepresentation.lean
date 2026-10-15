import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# Common Radon-Nikodym representation for finite families of signed measures

For a finite family `μ : ι → SignedMeasure α` we build the joint reference measure
`jointReference μ = ∑ i, (μ i).totalVariation`. It is a finite positive measure that dominates
every coordinate total variation, so every coordinate is absolutely continuous with respect to it
(arbitrary finite signed measures are covered, including singular ones). Consequently each
coordinate has a measurable, integrable real Radon-Nikodym density against this one reference,
and `withDensityᵥ` of that density recovers the coordinate.

This module only provides a common RN representation for finite coordinate signed measures.
It is not the full optimal-transport action or the continuity equation, and it has no
dependency on the concrete matrix modules. No positive definiteness assumption appears.
-/

open MeasureTheory
open MeasureTheory.VectorMeasure

namespace MatrixTransport

variable {α : Type*} [MeasurableSpace α] {ι : Type*}

/-- The joint reference measure: the sum of the coordinate total variations. -/
noncomputable def jointReference [Fintype ι] (μ : ι → SignedMeasure α) : Measure α :=
  ∑ i, (μ i).totalVariation

instance jointReference_isFiniteMeasure [Fintype ι] (μ : ι → SignedMeasure α) :
    IsFiniteMeasure (jointReference μ) := by
  unfold jointReference
  infer_instance

theorem jointReference_of_isEmpty [Fintype ι] [IsEmpty ι] (μ : ι → SignedMeasure α) :
    jointReference μ = 0 := by
  simp [jointReference]

theorem totalVariation_le_jointReference [Fintype ι] (μ : ι → SignedMeasure α) (i : ι) :
    (μ i).totalVariation ≤ jointReference μ := by
  unfold jointReference
  exact Finset.single_le_sum (f := fun j ↦ (μ j).totalVariation)
    (fun j _ ↦ bot_le) (Finset.mem_univ i)

theorem absolutelyContinuous_jointReference [Fintype ι] (μ : ι → SignedMeasure α) (i : ι) :
    μ i ≪ᵥ (jointReference μ).toENNRealVectorMeasure := by
  rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
  exact Measure.absolutelyContinuous_of_le (totalVariation_le_jointReference μ i)

theorem measurable_rnDeriv_jointReference [Fintype ι] (μ : ι → SignedMeasure α) (i : ι) :
    Measurable ((μ i).rnDeriv (jointReference μ)) :=
  SignedMeasure.measurable_rnDeriv (μ i) (jointReference μ)

theorem integrable_rnDeriv_jointReference [Fintype ι] (μ : ι → SignedMeasure α) (i : ι) :
    Integrable ((μ i).rnDeriv (jointReference μ)) (jointReference μ) :=
  SignedMeasure.integrable_rnDeriv (μ i) (jointReference μ)

theorem withDensityᵥ_rnDeriv_jointReference [Fintype ι] (μ : ι → SignedMeasure α) (i : ι) :
    (jointReference μ).withDensityᵥ ((μ i).rnDeriv (jointReference μ)) = μ i :=
  SignedMeasure.withDensityᵥ_rnDeriv_eq (μ i) (jointReference μ)
    (absolutelyContinuous_jointReference μ i)

/-- A common finite reference measure with real densities restoring each coordinate. -/
structure RNRepresentation (μ : ι → SignedMeasure α) where
  reference : Measure α
  finite : IsFiniteMeasure reference
  density : ι → α → ℝ
  measurable_density : ∀ i, Measurable (density i)
  integrable_density : ∀ i, Integrable (density i) reference
  withDensityᵥ_density : ∀ i, reference.withDensityᵥ (density i) = μ i

/-- The canonical representation built from `jointReference` and the coordinate RN derivatives. -/
noncomputable def canonicalRepresentation [Fintype ι] (μ : ι → SignedMeasure α) :
    RNRepresentation μ where
  reference := jointReference μ
  finite := jointReference_isFiniteMeasure μ
  density := fun i ↦ (μ i).rnDeriv (jointReference μ)
  measurable_density := fun i ↦ measurable_rnDeriv_jointReference μ i
  integrable_density := fun i ↦ integrable_rnDeriv_jointReference μ i
  withDensityᵥ_density := fun i ↦ withDensityᵥ_rnDeriv_jointReference μ i

theorem canonicalRepresentation_reference [Fintype ι] (μ : ι → SignedMeasure α) :
    (canonicalRepresentation μ).reference = jointReference μ :=
  rfl

theorem nonempty_rnRepresentation_of_fintype [Fintype ι] (μ : ι → SignedMeasure α) :
    Nonempty (RNRepresentation μ) :=
  ⟨canonicalRepresentation μ⟩

theorem nonempty_rnRepresentation [Finite ι] (μ : ι → SignedMeasure α) :
    Nonempty (RNRepresentation μ) := by
  cases nonempty_fintype ι
  exact ⟨canonicalRepresentation μ⟩

theorem exists_common_reference [Finite ι] (μ : ι → SignedMeasure α) :
    ∃ (ν : Measure α) (_ : IsFiniteMeasure ν) (f : ι → α → ℝ),
      (∀ i, Measurable (f i)) ∧ (∀ i, Integrable (f i) ν) ∧
        ∀ i, ν.withDensityᵥ (f i) = μ i := by
  obtain ⟨r⟩ := nonempty_rnRepresentation μ
  exact ⟨r.reference, r.finite, r.density, r.measurable_density, r.integrable_density,
    r.withDensityᵥ_density⟩

#print axioms nonempty_rnRepresentation
#print axioms nonempty_rnRepresentation_of_fintype
#print axioms exists_common_reference
#print axioms absolutelyContinuous_jointReference
#print axioms withDensityᵥ_rnDeriv_jointReference

end MatrixTransport
