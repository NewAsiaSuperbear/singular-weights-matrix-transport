import Mathlib
import MatrixTransport.MeasureRepresentation

/-!
# Canonical reference change for an integrable finite-coordinate density

The reference is the sum of coordinate total variations. For this single density family,
its Radon-Nikodym coordinates and the integral of any measurable homogeneous local action
are computed against the original positive measure. This is a measure helper, not a proof
of a transport-distance bound or of general reference independence.
-/

set_option autoImplicit false

open MeasureTheory
open MeasureTheory.Measure
open MeasureTheory.VectorMeasure
open scoped ENNReal

namespace MatrixTransport

variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]
  {ν : Measure α} [IsFiniteMeasure ν]

noncomputable def coordinateWeight (z : ι → α → ℝ) (x : α) : ℝ :=
  ∑ i, |z i x|

theorem measurable_coordinateWeight (z : ι → α → ℝ) (hzM : ∀ i, Measurable (z i)) :
    Measurable (coordinateWeight z) := by
  show Measurable fun x => ∑ i, |z i x|
  exact Finset.measurable_sum _ (fun i _ => continuous_abs.measurable.comp (hzM i))

theorem abs_le_coordinateWeight (z : ι → α → ℝ) (i : ι) (x : α) :
    |z i x| ≤ coordinateWeight z x :=
  Finset.single_le_sum (f := fun j => |z j x|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

theorem sum_withDensity_fun {κ : Type*} (m : Measure α) (s : Finset κ) (f : κ → α → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∑ i ∈ s, m.withDensity (f i) = m.withDensity (fun x => ∑ i ∈ s, f i x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact withDensity_zero.symm
  · intro a s ha ih
    have hfun : (fun x => ∑ i ∈ insert a s, f i x) = f a + fun x => ∑ i ∈ s, f i x := by
      funext x
      simp [Finset.sum_insert ha]
    rw [Finset.sum_insert ha, ih, hfun, withDensity_add_left (hf a)]

theorem jointReference_withDensityᵥ (z : ι → α → ℝ) (hzM : ∀ i, Measurable (z i))
    (hzI : ∀ i, Integrable (z i) ν) :
    jointReference (fun i => ν.withDensityᵥ (z i)) =
      ν.withDensity (fun x => ENNReal.ofReal (coordinateWeight z x)) := by
  have h1 : ∀ i, SignedMeasure.totalVariation (ν.withDensityᵥ (z i)) =
      ν.withDensity (fun x => ENNReal.ofReal |z i x|) := by
    intro i
    rw [SignedMeasure.totalVariation_eq_variation, Measure.variation_withDensityᵥ (hzI i)]
    simp only [Real.enorm_eq_ofReal_abs]
  have hmeas : ∀ i, Measurable (fun x => ENNReal.ofReal |z i x|) := fun i =>
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hzM i))
  have key : ∑ i, ν.withDensity (fun x => ENNReal.ofReal |z i x|) =
      ν.withDensity (fun x => ∑ i, ENNReal.ofReal |z i x|) :=
    sum_withDensity_fun ν Finset.univ (fun i x => ENNReal.ofReal |z i x|) hmeas
  calc jointReference (fun i => ν.withDensityᵥ (z i))
      = ∑ i, ν.withDensity (fun x => ENNReal.ofReal |z i x|) :=
        Finset.sum_congr rfl (fun i _ => h1 i)
    _ = ν.withDensity (fun x => ∑ i, ENNReal.ofReal |z i x|) := key
    _ = ν.withDensity (fun x => ENNReal.ofReal (coordinateWeight z x)) := by
        congr 1
        funext x
        unfold coordinateWeight
        exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg (z i x))).symm

theorem integrable_div_coordinateWeight (z : ι → α → ℝ) (hzM : ∀ i, Measurable (z i))
    (hzI : ∀ i, Integrable (z i) ν) (hw : ∀ x, 1 ≤ coordinateWeight z x) (i : ι) :
    Integrable (fun x => z i x / coordinateWeight z x)
      (jointReference (fun j => ν.withDensityᵥ (z j))) := by
  have hwM := measurable_coordinateWeight z hzM
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((( hzM i).div hwM).aestronglyMeasurable) (ae_of_all _ (fun x => ?_))
  have hpos : 0 < coordinateWeight z x := lt_of_lt_of_le one_pos (hw x)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
  exact (div_le_one hpos).mpr (abs_le_coordinateWeight z i x)

theorem withDensityᵥ_div_coordinateWeight (z : ι → α → ℝ) (hzM : ∀ i, Measurable (z i))
    (hzI : ∀ i, Integrable (z i) ν) (hw : ∀ x, 1 ≤ coordinateWeight z x) (i : ι) :
    (jointReference (fun j => ν.withDensityᵥ (z j))).withDensityᵥ
        (fun x => z i x / coordinateWeight z x) = ν.withDensityᵥ (z i) := by
  have hwM := measurable_coordinateWeight z hzM
  have hfm : AEMeasurable (fun x => ENNReal.ofReal (coordinateWeight z x)) ν :=
    (ENNReal.measurable_ofReal.comp hwM).aemeasurable
  have hflt : ∀ᵐ x ∂ν, ENNReal.ofReal (coordinateWeight z x) < ∞ :=
    ae_of_all _ (fun x => ENNReal.ofReal_lt_top)
  have hfun : (fun x => (ENNReal.ofReal (coordinateWeight z x)).toReal •
      (z i x / coordinateWeight z x)) = z i := by
    funext x
    have hpos : 0 < coordinateWeight z x := lt_of_lt_of_le one_pos (hw x)
    have hne : coordinateWeight z x ≠ 0 := hpos.ne'
    rw [ENNReal.toReal_ofReal hpos.le, smul_eq_mul]
    field_simp
  have hint : Integrable (fun x => (ENNReal.ofReal (coordinateWeight z x)).toReal •
      (z i x / coordinateWeight z x)) ν := by
    rw [hfun]
    exact hzI i
  have key := withDensityᵥ_smul_eq_withDensityᵥ_withDensity' (μ := ν)
    (f := fun x => ENNReal.ofReal (coordinateWeight z x))
    (g := fun x => z i x / coordinateWeight z x) hfm hflt hint
  rw [hfun] at key
  rw [jointReference_withDensityᵥ z hzM hzI]
  exact key.symm

theorem rnDeriv_jointReference_withDensityᵥ (z : ι → α → ℝ) (hzM : ∀ i, Measurable (z i))
    (hzI : ∀ i, Integrable (z i) ν) (hw : ∀ x, 1 ≤ coordinateWeight z x) (i : ι) :
    SignedMeasure.rnDeriv (ν.withDensityᵥ (z i))
        (jointReference (fun j => ν.withDensityᵥ (z j)))
      =ᵐ[jointReference (fun j => ν.withDensityᵥ (z j))]
        fun x => z i x / coordinateWeight z x := by
  have h1 := withDensityᵥ_rnDeriv_jointReference (fun j => ν.withDensityᵥ (z j)) i
  have h2 := withDensityᵥ_div_coordinateWeight z hzM hzI hw i
  exact Integrable.ae_eq_of_withDensityᵥ_eq
    (integrable_rnDeriv_jointReference (fun j => ν.withDensityᵥ (z j)) i)
    (integrable_div_coordinateWeight z hzM hzI hw i) (h1.trans h2.symm)

theorem lintegral_canonicalDensity_withDensity (z : ι → α → ℝ)
    (hzM : ∀ i, Measurable (z i)) (hzI : ∀ i, Integrable (z i) ν)
    (hw : ∀ x, 1 ≤ coordinateWeight z x)
    (J : (ι → ℝ) → ℝ≥0∞) (hJ : Measurable J)
    (hJhom : ∀ t : ℝ, 0 ≤ t → ∀ v, J (t • v) = ENNReal.ofReal t * J v) :
    ∫⁻ x, J (fun i => SignedMeasure.rnDeriv (ν.withDensityᵥ (z i))
        (jointReference (fun j => ν.withDensityᵥ (z j))) x)
      ∂(jointReference (fun j => ν.withDensityᵥ (z j)))
      = ∫⁻ x, J (fun i => z i x) ∂ν := by
  have hwM := measurable_coordinateWeight z hzM
  have hae : ∀ᵐ x ∂(jointReference (fun j => ν.withDensityᵥ (z j))),
      (fun i => SignedMeasure.rnDeriv (ν.withDensityᵥ (z i))
        (jointReference (fun j => ν.withDensityᵥ (z j))) x)
        = fun i => z i x / coordinateWeight z x := by
    have := ae_all_iff.2 (fun i => rnDeriv_jointReference_withDensityᵥ z hzM hzI hw i)
    filter_upwards [this] with x hx
    funext i
    exact hx i
  have hfm : Measurable (fun x => ENNReal.ofReal (coordinateWeight z x)) :=
    ENNReal.measurable_ofReal.comp hwM
  have hgm : Measurable (fun x => J (fun i => z i x / coordinateWeight z x)) :=
    hJ.comp (measurable_pi_iff.2 (fun i => (hzM i).div hwM))
  calc ∫⁻ x, J (fun i => SignedMeasure.rnDeriv (ν.withDensityᵥ (z i))
        (jointReference (fun j => ν.withDensityᵥ (z j))) x)
        ∂(jointReference (fun j => ν.withDensityᵥ (z j)))
      = ∫⁻ x, J (fun i => z i x / coordinateWeight z x)
          ∂(jointReference (fun j => ν.withDensityᵥ (z j))) :=
        lintegral_congr_ae (hae.mono (fun x hx => congrArg J hx))
    _ = ∫⁻ x, J (fun i => z i x / coordinateWeight z x)
          ∂(ν.withDensity (fun x => ENNReal.ofReal (coordinateWeight z x))) := by
        rw [jointReference_withDensityᵥ z hzM hzI]
    _ = ∫⁻ x, ENNReal.ofReal (coordinateWeight z x) *
          J (fun i => z i x / coordinateWeight z x) ∂ν :=
        lintegral_withDensity_eq_lintegral_mul ν hfm hgm
    _ = ∫⁻ x, J (fun i => z i x) ∂ν := by
        refine lintegral_congr (fun x => ?_)
        have hpos : 0 < coordinateWeight z x := lt_of_lt_of_le one_pos (hw x)
        have hne : coordinateWeight z x ≠ 0 := hpos.ne'
        have hv : (coordinateWeight z x) • (fun i => z i x / coordinateWeight z x)
            = fun i => z i x := by
          funext i
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp
        have hhom := hJhom (coordinateWeight z x) hpos.le
          (fun i => z i x / coordinateWeight z x)
        rw [← hhom, hv]

#print axioms jointReference_withDensityᵥ
#print axioms rnDeriv_jointReference_withDensityᵥ
#print axioms lintegral_canonicalDensity_withDensity

end MatrixTransport
