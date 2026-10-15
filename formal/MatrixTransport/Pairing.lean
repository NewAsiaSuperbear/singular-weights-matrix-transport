import Mathlib
import MatrixTransport.ActionBound
import MatrixTransport.DensityReference

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace MatrixTransport

variable {α : Type*} [MeasurableSpace α]

def signedPair (s : SignedMeasure α) (φ : α → ℝ) : ℝ :=
  (∫ x, φ x ∂s.toJordanDecomposition.posPart) - (∫ x, φ x ∂s.toJordanDecomposition.negPart)

theorem signedPair_withDensityᵥ (ν : Measure α) {f φ : α → ℝ} (hf : Measurable f)
    (hfI : Integrable f ν) (hφ : Measurable φ) (hB : ∃ C : ℝ, ∀ x, |φ x| ≤ C) :
    signedPair (ν.withDensityᵥ f) φ = ∫ x, φ x * f x ∂ν := by
  obtain ⟨C, hC⟩ := hB
  have hmain := SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity hf hfI
    (VectorMeasure.MutuallySingular.zero_left :
      VectorMeasure.MutuallySingular (0 : SignedMeasure α) ν.toENNRealVectorMeasure)
    (show ν.withDensityᵥ f = 0 + ν.withDensityᵥ f by simp)
  have h0p : (0 : SignedMeasure α).toJordanDecomposition.posPart = 0 := by
    rw [SignedMeasure.toJordanDecomposition_zero]; rfl
  have h0n : (0 : SignedMeasure α).toJordanDecomposition.negPart = 0 := by
    rw [SignedMeasure.toJordanDecomposition_zero]; rfl
  have hpos : (SignedMeasure.toJordanDecomposition (ν.withDensityᵥ f)).posPart =
      ν.withDensity (fun x => ENNReal.ofReal (f x)) := by
    have := congrArg JordanDecomposition.posPart hmain
    simpa [h0p] using this
  have hneg : (SignedMeasure.toJordanDecomposition (ν.withDensityᵥ f)).negPart =
      ν.withDensity (fun x => ENNReal.ofReal (-f x)) := by
    have := congrArg JordanDecomposition.negPart hmain
    simpa [h0n] using this
  have hfm : Measurable (fun x => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hf
  have hfm' : Measurable (fun x => ENNReal.ofReal (-f x)) :=
    ENNReal.measurable_ofReal.comp hf.neg
  have hflt : ∀ᵐ x ∂ν, ENNReal.ofReal (f x) < ∞ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have hflt' : ∀ᵐ x ∂ν, ENNReal.ofReal (-f x) < ∞ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have e1 : ∫ x, φ x ∂ν.withDensity (fun x => ENNReal.ofReal (f x)) =
      ∫ x, φ x * max (f x) 0 ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul hfm hflt]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal', mul_comm]
  have e2 : ∫ x, φ x ∂ν.withDensity (fun x => ENNReal.ofReal (-f x)) =
      ∫ x, φ x * max (-f x) 0 ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul hfm' hflt']
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal', mul_comm]
  have h1 : Integrable (fun x => φ x * max (f x) 0) ν :=
    hfI.pos_part.bdd_mul (f := φ) (c := C) hφ.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hnegI : Integrable (fun x => max (-f x) 0) ν := hfI.neg.pos_part
  have h2 : Integrable (fun x => φ x * max (-f x) 0) ν :=
    hnegI.bdd_mul (f := φ) (c := C) hφ.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  unfold signedPair
  rw [hpos, hneg, e1, e2, ← integral_sub h1 h2]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show φ x * max (f x) 0 - φ x * max (-f x) 0 = φ x * f x
  rcases le_total (f x) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -f x)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith : -f x ≤ 0)]
    ring

theorem signedPair_rnDeriv (ν : Measure α) [IsFiniteMeasure ν] (s : SignedMeasure α)
    (hs : VectorMeasure.AbsolutelyContinuous s ν.toENNRealVectorMeasure)
    {φ : α → ℝ} (hφ : Measurable φ) (hB : ∃ C : ℝ, ∀ x, |φ x| ≤ C) :
    signedPair s φ = ∫ x, φ x * s.rnDeriv ν x ∂ν := by
  have h := SignedMeasure.withDensityᵥ_rnDeriv_eq s ν hs
  have key := signedPair_withDensityᵥ ν (SignedMeasure.measurable_rnDeriv s ν)
    (SignedMeasure.integrable_rnDeriv s ν) hφ hB
  rw [h] at key
  exact key

def signedCoordinatePair (r : ℕ) (μ : TransportCoord r → SignedMeasure α)
    (a : α → TransportCoord r → ℝ) : ℝ :=
  ∑ c, signedPair (μ c) (fun x => a x c)

theorem signedCoordinatePair_eq_canonicalPair (r : ℕ)
    (μ : TransportCoord r → SignedMeasure α)
    (a : α → TransportCoord r → ℝ)
    (haM : ∀ c, Measurable (fun x => a x c))
    (haB : ∃ C : ℝ, ∀ x c, |a x c| ≤ C) :
    signedCoordinatePair r μ a = canonicalPair r μ a := by
  obtain ⟨C, hC⟩ := haB
  have hterm : ∀ c, signedPair (μ c) (fun x => a x c) =
      ∫ x, a x c * matrixDensity r μ x c ∂jointReference μ := fun c =>
    signedPair_rnDeriv (jointReference μ) (μ c) (absolutelyContinuous_jointReference μ c)
      (haM c) ⟨C, fun x => hC x c⟩
  have hint : ∀ c, Integrable (fun x => a x c * matrixDensity r μ x c) (jointReference μ) :=
    fun c =>
      (integrable_rnDeriv_jointReference μ c).bdd_mul (f := fun x => a x c) (c := C)
        (haM c).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x c)
  have h1 : signedCoordinatePair r μ a =
      ∑ c, ∫ x, a x c * matrixDensity r μ x c ∂jointReference μ :=
    Finset.sum_congr rfl fun c _ => hterm c
  have hsum := integral_finsetSum (μ := jointReference μ) Finset.univ
    (f := fun c x => a x c * matrixDensity r μ x c) (fun c _ => hint c)
  unfold canonicalPair
  rw [h1]
  refine hsum.symm.trans ?_
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show ∑ c, a x c * matrixDensity r μ x c =
    weightedPair (fun _ => 1) (a x) (matrixDensity r μ x)
  simp only [weightedPair, one_mul]

theorem canonicalPair_withDensityᵥ (r : ℕ) (ν : Measure α) [IsFiniteMeasure ν]
    (z : TransportCoord r → α → ℝ)
    (hzM : ∀ c, Measurable (z c)) (hzI : ∀ c, Integrable (z c) ν)
    (a : α → TransportCoord r → ℝ)
    (haM : ∀ c, Measurable (fun x => a x c))
    (haB : ∃ C : ℝ, ∀ x c, |a x c| ≤ C) :
    canonicalPair r (fun c => ν.withDensityᵥ (z c)) a =
      ∫ x, weightedPair (fun _ => 1) (a x) (fun c => z c x) ∂ν := by
  have hbridge := signedCoordinatePair_eq_canonicalPair r
    (fun c => ν.withDensityᵥ (z c)) a haM haB
  rw [← hbridge]
  obtain ⟨C, hC⟩ := haB
  have h1 : signedCoordinatePair r (fun c => ν.withDensityᵥ (z c)) a =
      ∑ c, ∫ x, a x c * z c x ∂ν :=
    Finset.sum_congr rfl fun c _ =>
      signedPair_withDensityᵥ ν (hzM c) (hzI c) (haM c) ⟨C, fun x => hC x c⟩
  have hint : ∀ c, Integrable (fun x => a x c * z c x) ν := fun c =>
    (hzI c).bdd_mul (f := fun x => a x c) (c := C) (haM c).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x c)
  have hsum := integral_finsetSum (μ := ν) Finset.univ
    (f := fun c x => a x c * z c x) (fun c _ => hint c)
  rw [h1]
  refine hsum.symm.trans ?_
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show ∑ c, a x c * z c x = weightedPair (fun _ => 1) (a x) (fun c => z c x)
  simp only [weightedPair, one_mul]

#print axioms signedPair_withDensityᵥ
#print axioms signedPair_rnDeriv
#print axioms signedCoordinatePair_eq_canonicalPair
#print axioms canonicalPair_withDensityᵥ

end MatrixTransport

end
