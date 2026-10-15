import Mathlib
import MatrixTransport.MatrixAction

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace MatrixTransport

variable {α : Type*} [MeasurableSpace α]

theorem ofReal_integral_le_lintegral_ofReal {ν : Measure α} {p : α → ℝ}
    (hp : Integrable p ν) :
    ENNReal.ofReal (∫ x, p x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (p x) ∂ν := by
  have hg : Integrable (fun x => max (p x) 0) ν := hp.pos_part
  have h1 : ∫ x, p x ∂ν ≤ ∫ x, max (p x) 0 ∂ν :=
    integral_mono hp hg (fun x => le_max_left _ _)
  have h2 : ENNReal.ofReal (∫ x, max (p x) 0 ∂ν) =
      ∫⁻ x, ENNReal.ofReal (max (p x) 0) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ fun x => le_max_right _ _)
  have h3 : ∀ x, ENNReal.ofReal (max (p x) 0) = ENNReal.ofReal (p x) := by
    intro x
    rcases le_total (p x) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  calc ENNReal.ofReal (∫ x, p x ∂ν)
      ≤ ENNReal.ofReal (∫ x, max (p x) 0 ∂ν) := ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ x, ENNReal.ofReal (max (p x) 0) ∂ν := h2
    _ = ∫⁻ x, ENNReal.ofReal (p x) ∂ν := by simp_rw [h3]

theorem integrable_canonicalPair_integrand (r : ℕ)
    (μ : TransportCoord r → SignedMeasure α)
    (a : α → TransportCoord r → ℝ)
    (haM : ∀ c, Measurable (fun x => a x c))
    (haB : ∃ C : ℝ, ∀ x c, |a x c| ≤ C) :
    Integrable (fun x => weightedPair (fun _ => 1) (a x) (matrixDensity r μ x))
      (jointReference μ) := by
  obtain ⟨C, hC⟩ := haB
  simp only [weightedPair]
  refine integrable_finsetSum (f := fun c x => 1 * a x c * matrixDensity r μ x c)
    Finset.univ ?_
  intro c _
  have h := (integrable_rnDeriv_jointReference μ c).bdd_mul (f := fun x => a x c) (c := C)
    (haM c).aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x c)
  simpa only [one_mul, matrixDensity] using h

def canonicalPair (r : ℕ) (μ : TransportCoord r → SignedMeasure α)
    (a : α → TransportCoord r → ℝ) : ℝ :=
  ∫ x, weightedPair (fun _ => 1) (a x) (matrixDensity r μ x) ∂jointReference μ

theorem canonicalPair_le_matrixAction (r : ℕ)
    (μ : TransportCoord r → SignedMeasure α)
    (a : α → TransportCoord r → ℝ)
    (haM : ∀ c, Measurable (fun x => a x c))
    (haB : ∃ C : ℝ, ∀ x c, |a x c| ≤ C)
    (hdual : ∀ x, a x ∈ dualSet r) :
    ENNReal.ofReal (canonicalPair r μ a) ≤ matrixAction r μ := by
  unfold canonicalPair matrixAction
  refine (ofReal_integral_le_lintegral_ofReal
    (integrable_canonicalPair_integrand r μ a haM haB)).trans ?_
  exact lintegral_mono fun x => matrixCost_fenchel r _ _ (hdual x)

end MatrixTransport

end
