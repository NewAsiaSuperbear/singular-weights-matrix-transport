import MatrixTransport.Paper.ExpandedGluing
import MatrixTransport.Paper.ExpandedTimeSupport

/-!
# Exact action gluing from actual coordinate time support

A common reference for both full coordinate families turns disjoint measure supports
into disjoint Radon--Nikodym density tuples. The hypotheses use total variations, so
cancellation of signed coordinates cannot supply a spurious support condition.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace MatrixTransport.Paper.ExpandedSlabGluing

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ExpandedGluing
open MatrixTransport.EntrywiseBures MatrixTransport.Paper.ExpandedTimeSupport

variable {X : Type*} [MeasurableSpace X]

theorem measure_rnDeriv_zero_on (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (S : Set X) (hS : MeasurableSet S) (hμ : μ S = 0) :
    ∀ᵐ x ∂ν, x ∈ S → μ.rnDeriv ν x = 0 := by
  have hd := Measure.rnDeriv_restrict μ ν hS
  rw [Measure.restrict_eq_zero.mpr hμ] at hd
  filter_upwards [hd, Measure.rnDeriv_zero ν] with x hx hz
  intro hxs
  rw [Set.indicator_of_mem hxs] at hx
  exact hx.symm.trans hz

theorem signed_rnDeriv_zero_on (s : SignedMeasure X) (ν : Measure X)
    [IsFiniteMeasure ν] (S : Set X) (hS : MeasurableSet S)
    (hs : s.totalVariation S = 0) :
    ∀ᵐ x ∂ν, x ∈ S → s.rnDeriv ν x = 0 := by
  have hp : s.toJordanDecomposition.posPart S = 0 ∧
      s.toJordanDecomposition.negPart S = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] using hs
  filter_upwards [measure_rnDeriv_zero_on _ ν S hS hp.1,
    measure_rnDeriv_zero_on _ ν S hS hp.2] with x hpos hneg
  intro hxs
  simp only [SignedMeasure.rnDeriv_def, hpos hxs, hneg hxs, ENNReal.toReal_zero, sub_self]

variable {n k : ℕ}

theorem action_add_of_disjoint_measures (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ η : Coord n k → SignedMeasure X)
    (S : Set X) (hS : MeasurableSet S)
    (hμ : ∀ c, (μ c).totalVariation Sᶜ = 0)
    (hη : ∀ c, (η c).totalVariation S = 0) :
    action L H (μ + η) = action L H μ + action L H η := by
  classical
  let family : Sum (Coord n k) (Coord n k) → SignedMeasure X := Sum.elim μ η
  let ν := jointReference family
  let v : Coord n k → X → ℝ := fun c ↦ (μ c).rnDeriv ν
  let w : Coord n k → X → ℝ := fun c ↦ (η c).rnDeriv ν
  have hvM : ∀ c, Measurable (v c) := fun c ↦
    measurable_rnDeriv_jointReference family (Sum.inl c)
  have hwM : ∀ c, Measurable (w c) := fun c ↦
    measurable_rnDeriv_jointReference family (Sum.inr c)
  have hvI : ∀ c, Integrable (v c) ν := fun c ↦
    integrable_rnDeriv_jointReference family (Sum.inl c)
  have hwI : ∀ c, Integrable (w c) ν := fun c ↦
    integrable_rnDeriv_jointReference family (Sum.inr c)
  have hv0 : ∀ᵐ x ∂ν, ∀ c, x ∉ S → v c x = 0 := by
    rw [ae_all_iff]
    intro c
    exact signed_rnDeriv_zero_on (μ c) ν Sᶜ hS.compl (hμ c)
  have hw0 : ∀ᵐ x ∂ν, ∀ c, x ∈ S → w c x = 0 := by
    rw [ae_all_iff]
    intro c
    exact signed_rnDeriv_zero_on (η c) ν S hS (hη c)
  have hdisj : ∀ᵐ x ∂ν, (fun c ↦ v c x) = 0 ∨ (fun c ↦ w c x) = 0 := by
    filter_upwards [hv0, hw0] with x hx hy
    by_cases hxs : x ∈ S
    · exact Or.inr (funext fun c ↦ hy c hxs)
    · exact Or.inl (funext fun c ↦ hx c hxs)
  have heμ : (fun c ↦ ν.withDensityᵥ (v c)) = μ := by
    funext c
    exact withDensityᵥ_rnDeriv_jointReference family (Sum.inl c)
  have heη : (fun c ↦ ν.withDensityᵥ (w c)) = η := by
    funext c
    exact withDensityᵥ_rnDeriv_jointReference family (Sum.inr c)
  have he := action_add_of_disjoint_density L H ν v w hvM hwM hvI hwI hdisj
  change action L H ((fun c ↦ ν.withDensityᵥ (v c)) +
    (fun c ↦ ν.withDensityᵥ (w c))) = _ at he
  rwa [heμ, heη] at he

theorem totalVariation_add_le (s t : SignedMeasure X) :
    (s + t).totalVariation ≤ s.totalVariation + t.totalVariation := by
  simpa only [SignedMeasure.totalVariation_eq_variation] using
    (VectorMeasure.variation_add_le (μ := s) (ν := t))

theorem totalVariation_add_zero (s t : SignedMeasure X) (S : Set X)
    (hs : s.totalVariation S = 0) (ht : t.totalVariation S = 0) :
    (s + t).totalVariation S = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    (s + t).totalVariation S ≤ (s.totalVariation + t.totalVariation) S :=
      totalVariation_add_le s t S
    _ = 0 := by simp only [Measure.add_apply, hs, ht, add_zero]

end MatrixTransport.Paper.ExpandedSlabGluing
