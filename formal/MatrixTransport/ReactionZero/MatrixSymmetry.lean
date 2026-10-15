import MatrixTransport.ReactionZero.MeasureCompactness
import MatrixTransport.ReactionZero.WeightedAction

/-!
# Actual signed-measure symmetry and its weak closure

Continuous real tests determine a finite signed Borel measure on a compact metric space.
The proof reduces to the existing uniqueness theorem for positive finite measures, applied
to the two cross sums of Jordan parts. Thus equality of the matrix mass coordinates is
preserved by the actual signed-measure weak convergence from `MeasureCompactness`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

noncomputable section

namespace MatrixTransport.ReactionZero

variable {Q : Type*} [MetricSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]

/-- All continuous tests determine an actual signed measure, without assuming an embedding
into an abstract dual space is injective. -/
theorem signedMeasure_eq_of_continuousPair_eq (s t : SignedMeasure Q)
    (h : ∀ f : C(Q, ℝ), MatrixTransport.signedPair s f =
      MatrixTransport.signedPair t f) : s = t := by
  let a : FiniteMeasure Q :=
    ⟨s.toJordanDecomposition.posPart + t.toJordanDecomposition.negPart, inferInstance⟩
  let b : FiniteMeasure Q :=
    ⟨t.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart, inferInstance⟩
  have hab : a = b := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    have hh := h f.toContinuousMap
    unfold MatrixTransport.signedPair at hh
    change (∫ x, f.toContinuousMap x ∂(s.toJordanDecomposition.posPart +
        t.toJordanDecomposition.negPart)) =
      ∫ x, f.toContinuousMap x ∂(t.toJordanDecomposition.posPart +
        s.toJordanDecomposition.negPart)
    rw [integral_add_measure (continuousTest_integrable f.toContinuousMap _)
      (continuousTest_integrable f.toContinuousMap _),
      integral_add_measure (continuousTest_integrable f.toContinuousMap _)
      (continuousTest_integrable f.toContinuousMap _)]
    linarith
  have hmeasure : s.toJordanDecomposition.posPart + t.toJordanDecomposition.negPart =
      t.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart :=
    congrArg (fun μ : FiniteMeasure Q ↦ (μ : Measure Q)) hab
  apply VectorMeasure.ext
  intro u hu
  rw [SignedMeasure.apply_eq_posPart_real_sub_negPart_real s hu,
    SignedMeasure.apply_eq_posPart_real_sub_negPart_real t hu]
  have hh := congrArg (fun μ : Measure Q ↦ μ.real u) hmeasure
  rw [measureReal_add_apply, measureReal_add_apply] at hh
  linarith

variable {ι : Type*}

/-- Equality of any two actual signed coordinates is weakly closed. -/
theorem coordinate_eq_of_signedWeakStar (μ : ℕ → ι → SignedMeasure Q)
    (ν : ι → SignedMeasure Q) (hμ : SignedWeakStarTendsto μ ν)
    (i j : ι) (hij : ∀ l, μ l i = μ l j) : ν i = ν j := by
  apply signedMeasure_eq_of_continuousPair_eq
  intro f
  have hi := hμ i f
  have hj := hμ j f
  have heq : (fun l ↦ MatrixTransport.signedPair (μ l i) f) =
      (fun l ↦ MatrixTransport.signedPair (μ l j) f) := by
    funext l
    rw [hij l]
  rw [heq] at hi
  exact tendsto_nhds_unique hi hj

variable {n k : ℕ}

/-- Matrix mass symmetry is imposed on the actual measure coordinates. -/
def MassSymmetric (μ : Coord n k → SignedMeasure Q) : Prop :=
  ∀ i j, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i))

/-- Every weak limit of symmetric matrix mass measures has symmetric matrix mass. -/
theorem massSymmetric_of_signedWeakStar (μ : ℕ → Coord n k → SignedMeasure Q)
    (ν : Coord n k → SignedMeasure Q) (hμ : SignedWeakStarTendsto μ ν)
    (hs : ∀ l, MassSymmetric (μ l)) : MassSymmetric ν := by
  intro i j
  exact coordinate_eq_of_signedWeakStar μ ν hμ _ _ (fun l ↦ hs l i j)

omit [MetricSpace Q] [CompactSpace Q] [BorelSpace Q] in
/-- Measure symmetry gives pointwise symmetric RN mass coordinates for the same reference
measure. No almost-everywhere replacement or symmetry hypothesis on the density is needed. -/
theorem mass_rnDeriv_isHermitian (μ : Coord n k → SignedMeasure Q)
    (hs : MassSymmetric μ) (ρ : Measure Q) (x : Q) :
    (mass (fun c ↦ (μ c).rnDeriv ρ x)).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  change (μ (Sum.inl (j, i))).rnDeriv ρ x = (μ (Sum.inl (i, j))).rnDeriv ρ x
  rw [hs j i]

#print axioms signedMeasure_eq_of_continuousPair_eq
#print axioms coordinate_eq_of_signedWeakStar
#print axioms massSymmetric_of_signedWeakStar
#print axioms mass_rnDeriv_isHermitian

end MatrixTransport.ReactionZero
