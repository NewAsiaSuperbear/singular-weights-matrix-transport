import Mathlib

open scoped ContDiff
open MeasureTheory

namespace MatrixTransport

abbrev Spatial := EuclideanSpace ℝ (Fin 2)

def disk : Set Spatial := Metric.closedBall (0 : Spatial) 1

noncomputable def e1 : Spatial := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

theorem exists_bump :
    ∃ f : Spatial → ℝ,
      tsupport f ⊆ Metric.ball (0 : Spatial) (1 / 2 : ℝ) ∧ HasCompactSupport f ∧
        ContDiff ℝ ∞ f ∧ Set.range f ⊆ Set.Icc 0 1 ∧ f 0 = 1 :=
  exists_contDiff_tsupport_subset (n := ⊤)
    (Metric.ball_mem_nhds (0 : Spatial) (by norm_num : (0 : ℝ) < 1 / 2))

noncomputable def chi : Spatial → ℝ := Classical.choose exists_bump

theorem chi_tsupport_subset : tsupport chi ⊆ Metric.ball (0 : Spatial) (1 / 2 : ℝ) :=
  (Classical.choose_spec exists_bump).1

theorem chi_compact : HasCompactSupport chi :=
  (Classical.choose_spec exists_bump).2.1

theorem chi_contDiff : ContDiff ℝ ∞ chi :=
  (Classical.choose_spec exists_bump).2.2.1

theorem chi_range : Set.range chi ⊆ Set.Icc 0 1 :=
  (Classical.choose_spec exists_bump).2.2.2.1

theorem chi_zero : chi 0 = 1 :=
  (Classical.choose_spec exists_bump).2.2.2.2

theorem chi_nonneg (x : Spatial) : 0 ≤ chi x :=
  (chi_range ⟨x, rfl⟩).1

theorem chi_le_one (x : Spatial) : chi x ≤ 1 :=
  (chi_range ⟨x, rfl⟩).2

theorem chi_continuous : Continuous chi := chi_contDiff.continuous

theorem chi_tsupport_subset_disk : tsupport chi ⊆ disk :=
  chi_tsupport_subset.trans
    (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by norm_num)))

theorem chi_integrable : Integrable chi volume :=
  chi_continuous.integrable_of_hasCompactSupport chi_compact

theorem chi_sq_integrable : Integrable (fun x => chi x ^ 2) volume := by
  have h : HasCompactSupport (chi * chi) := chi_compact.mul_right
  have h2 : HasCompactSupport (fun x => chi x ^ 2) := by
    refine HasCompactSupport.mono h ?_
    intro x hx
    simp only [Function.mem_support, Pi.mul_apply] at hx ⊢
    rwa [pow_two] at hx
  exact (chi_continuous.pow 2).integrable_of_hasCompactSupport h2

theorem chi_integral_pos : 0 < ∫ x, chi x ∂volume :=
  integral_pos_of_integrable_nonneg_nonzero (μ := volume) (x := (0 : Spatial))
    chi_continuous chi_integrable (fun x => chi_nonneg x)
    (by rw [chi_zero]; norm_num)

noncomputable def dChi (x : Spatial) : ℝ := fderiv ℝ chi x e1

theorem dChi_continuous : Continuous dChi :=
  (chi_contDiff.continuous_fderiv (by simp)).clm_apply continuous_const

theorem dChi_compact : HasCompactSupport dChi := by
  unfold dChi
  exact chi_compact.fderiv_apply ℝ e1

theorem dChi_tsupport_subset : tsupport dChi ⊆ tsupport chi := by
  unfold dChi
  exact tsupport_fderiv_apply_subset ℝ e1

theorem dChi_tsupport_subset_ball :
    tsupport dChi ⊆ Metric.ball (0 : Spatial) (1 / 2 : ℝ) :=
  dChi_tsupport_subset.trans chi_tsupport_subset

theorem dChi_integrable : Integrable dChi volume :=
  dChi_continuous.integrable_of_hasCompactSupport dChi_compact

theorem dChi_bound : ∃ L : ℝ, ∀ x, |dChi x| ≤ L := by
  obtain ⟨C, hC⟩ := dChi_compact.exists_bound_of_continuous dChi_continuous
  refine ⟨C, fun x => ?_⟩
  simpa [Real.norm_eq_abs] using hC x

#print axioms exists_bump
#print axioms chi_contDiff
#print axioms chi_integral_pos
#print axioms dChi_bound

end MatrixTransport
