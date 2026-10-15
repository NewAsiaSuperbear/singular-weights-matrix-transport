import Mathlib
import MatrixTransport.Oscillation
import MatrixTransport.ClosedDomain

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ContDiff

namespace MatrixTransport

theorem hasCompactSupport_mul_left' (u v : Spatial → ℝ) (hu : HasCompactSupport u) :
    HasCompactSupport (fun x => u x * v x) :=
  hu.mono (fun x hx => Function.mem_support.2 fun h =>
    Function.mem_support.1 hx (by simp [h]))

theorem integrable_chi_mul {g : Spatial → ℝ} (hg : Continuous g) :
    Integrable (fun x => chi x * g x) volume :=
  (chi_continuous.mul hg).integrable_of_hasCompactSupport
    (hasCompactSupport_mul_left' chi g chi_compact)

theorem integrable_dChi_mul {g : Spatial → ℝ} (hg : Continuous g) :
    Integrable (fun x => dChi x * g x) volume :=
  (dChi_continuous.mul hg).integrable_of_hasCompactSupport
    (hasCompactSupport_mul_left' dChi g dChi_compact)

theorem endpointWave_mul_eq (n : ℕ) (g : Spatial → ℝ) (x : Spatial) :
    endpointWave n x * g x
      = dChi x * g x * Real.sin (waveNumber n * x 0) / waveNumber n
        + chi x * g x * oscillatoryCos (n + 1) x := by
  unfold endpointWave oscillatoryCos waveNumber
  push_cast
  ring

theorem integrable_sinPart {g : Spatial → ℝ} (hg : Continuous g) (n : ℕ) :
    Integrable (fun x => dChi x * g x * Real.sin (waveNumber n * x 0) / waveNumber n)
      volume := by
  have hs : Continuous fun x : Spatial => Real.sin (waveNumber n * x 0) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_coord)
  have h : Integrable (fun x => dChi x * g x * Real.sin (waveNumber n * x 0)) volume := by
    refine Integrable.mono' (integrable_dChi_mul hg).norm
      ((dChi_continuous.mul hg).mul hs).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul (dChi x * g x)]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  exact h.div_const _

theorem integrable_cosPart {g : Spatial → ℝ} (hg : Continuous g) (n : ℕ) :
    Integrable (fun x => chi x * g x * oscillatoryCos (n + 1) x) volume := by
  have hc := continuous_oscillatoryCos (n + 1)
  refine Integrable.mono' (integrable_chi_mul hg).norm
    ((chi_continuous.mul hg).mul hc).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul (chi x * g x)]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (by rw [Real.norm_eq_abs]; unfold oscillatoryCos; exact Real.abs_cos_le_one _)

theorem norm_sinPart_le {g : Spatial → ℝ} (n : ℕ) (x : Spatial) :
    ‖dChi x * g x * Real.sin (waveNumber n * x 0) / waveNumber n‖
      ≤ ‖dChi x * g x‖ / waveNumber n := by
  have hw := waveNumber_pos n
  have h1 : |dChi x * g x| * |Real.sin (waveNumber n * x 0)| ≤ |dChi x * g x| :=
    mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have h2 : |dChi x * g x| * |Real.sin (waveNumber n * x 0)| / waveNumber n
      ≤ |dChi x * g x| / waveNumber n := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hw.le)
  simpa only [Real.norm_eq_abs, abs_div, abs_of_pos hw, abs_mul] using h2

theorem tendsto_integral_endpointWave_mul {g : Spatial → ℝ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∫ x, endpointWave n x * g x) atTop (𝓝 0) := by
  have hcg := integrable_chi_mul hg
  have hdg := integrable_dChi_mul hg
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ x, ‖dChi x * g x‖ := ⟨_, rfl⟩
  have hbound : ∀ n : ℕ,
      ‖∫ x, dChi x * g x * Real.sin (waveNumber n * x 0) / waveNumber n‖
        ≤ M * (waveNumber n)⁻¹ := by
    intro n
    calc ‖∫ x, dChi x * g x * Real.sin (waveNumber n * x 0) / waveNumber n‖
        ≤ ∫ x, ‖dChi x * g x * Real.sin (waveNumber n * x 0) / waveNumber n‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖dChi x * g x‖ / waveNumber n :=
          integral_mono (integrable_sinPart hg n).norm (hdg.norm.div_const _)
            (fun x => norm_sinPart_le n x)
      _ = M * (waveNumber n)⁻¹ := by rw [integral_div, hM, div_eq_mul_inv]
  have hT : Tendsto (fun n : ℕ => M * (waveNumber n)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_waveNumber_atTop).const_mul M
  have hA : Tendsto (fun n : ℕ =>
      ∫ x, dChi x * g x * Real.sin (waveNumber n * x 0) / waveNumber n) atTop (𝓝 0) :=
    squeeze_zero_norm hbound hT
  have hB : Tendsto (fun n : ℕ => ∫ x, chi x * g x * oscillatoryCos (n + 1) x)
      atTop (𝓝 0) :=
    (tendsto_integral_mul_oscillatoryCos (f := fun x => chi x * g x) hcg).comp
      (tendsto_add_atTop_nat 1)
  have hsum := hA.add hB
  rw [add_zero] at hsum
  have key : ∀ n : ℕ,
      (∫ x, dChi x * g x * Real.sin (waveNumber n * x 0) / waveNumber n)
        + (∫ x, chi x * g x * oscillatoryCos (n + 1) x)
        = ∫ x, endpointWave n x * g x := by
    intro n
    rw [← integral_add (integrable_sinPart hg n) (integrable_cosPart hg n)]
    congr 1
    funext x
    exact (endpointWave_mul_eq n g x).symm
  exact hsum.congr key

theorem endpointWave_eq_zero_outside (n : ℕ) {x : Spatial} (hx : x ∉ disk) :
    endpointWave n x = 0 := by
  by_contra h
  exact hx (chi_tsupport_subset_disk
    (support_endpointWave_subset n (Function.mem_support.2 h)))

theorem integral_diskVolume_eq (F : Spatial → ℝ) (h : ∀ x, x ∉ disk → F x = 0) :
    ∫ x, F x ∂diskVolume = ∫ x, F x := by
  show ∫ x, F x ∂(volume.restrict disk) = _
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => h x hx)

theorem integral_endpointWave_disk (n : ℕ) :
    ∫ x, endpointWave n x ∂diskVolume = 0 :=
  (integral_diskVolume_eq (endpointWave n)
    (fun x hx => endpointWave_eq_zero_outside n hx)).trans (integral_endpointWave n)

theorem fderiv_cos_e1 (n : ℕ) (x : Spatial) :
    fderiv ℝ (fun y : Spatial => Real.cos (waveNumber n * y 0)) x e1
      = -(waveNumber n * Real.sin (waveNumber n * x 0)) := by
  have hp : HasFDerivAt (fun y : Spatial => y 0) coord0 x := coord0.hasFDerivAt
  have hc : HasFDerivAt (fun y : Spatial => Real.cos (waveNumber n * y 0))
      ((-Real.sin (waveNumber n * x 0)) • (waveNumber n • coord0)) x :=
    (hp.const_mul (waveNumber n)).cos
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.smul_apply, coord0_e1, smul_eq_mul]
  ring

theorem integral_cos_mul_endpointWave (n : ℕ) :
    ∫ x, endpointWave n x * Real.cos (waveNumber n * x 0)
      = ∫ x, chi x * (Real.sin (waveNumber n * x 0)) ^ 2 := by
  have hk := waveNumber_ne_zero n
  have hG : Continuous fun x : Spatial => Real.cos (waveNumber n * x 0) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_coord)
  have hs : Continuous fun x : Spatial => -(waveNumber n * Real.sin (waveNumber n * x 0)) :=
    (continuous_const.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_coord))).neg
  have h1 : Integrable (fun x => primitiveWave n x * Real.cos (waveNumber n * x 0)) volume :=
    ((primitiveWave_continuous n).mul hG).integrable_of_hasCompactSupport
      (hasCompactSupport_mul_left' (primitiveWave n)
        (fun x => Real.cos (waveNumber n * x 0)) (primitiveWave_compact n))
  have h2 : Integrable (fun x => endpointWave n x * Real.cos (waveNumber n * x 0)) volume :=
    ((endpointWave_continuous n).mul hG).integrable_of_hasCompactSupport
      (hasCompactSupport_mul_left' (endpointWave n)
        (fun x => Real.cos (waveNumber n * x 0)) (endpointWave_compact n))
  have h3' : Integrable (fun x => primitiveWave n x
      * -(waveNumber n * Real.sin (waveNumber n * x 0))) volume :=
    ((primitiveWave_continuous n).mul hs).integrable_of_hasCompactSupport
      (hasCompactSupport_mul_left' (primitiveWave n)
        (fun x => -(waveNumber n * Real.sin (waveNumber n * x 0))) (primitiveWave_compact n))
  have h3 : Integrable (fun x => primitiveWave n x
      * fderiv ℝ (fun y : Spatial => Real.cos (waveNumber n * y 0)) x e1) volume := by
    simp only [fderiv_cos_e1]
    exact h3'
  have hg : ∀ x ∈ tsupport chi,
      DifferentiableAt ℝ (fun y : Spatial => Real.cos (waveNumber n * y 0)) x :=
    fun x _ => (Real.contDiff_cos.comp (contDiff_const.mul contDiff_coord)).differentiable
      (by simp) x
  have h : ∫ x, endpointWave n x * Real.cos (waveNumber n * x 0)
      = - ∫ x, primitiveWave n x
          * fderiv ℝ (fun y : Spatial => Real.cos (waveNumber n * y 0)) x e1 :=
    integral_endpointWave_mul_eq n (fun y : Spatial => Real.cos (waveNumber n * y 0))
      h1 h2 h3 hg
  have hpt : ∀ x : Spatial, primitiveWave n x
      * fderiv ℝ (fun y : Spatial => Real.cos (waveNumber n * y 0)) x e1
      = -(chi x * (Real.sin (waveNumber n * x 0)) ^ 2) := by
    intro x
    rw [fderiv_cos_e1]
    unfold primitiveWave
    rw [div_mul_eq_mul_div, div_eq_iff hk]
    ring
  have hint : ∫ x, primitiveWave n x
      * fderiv ℝ (fun y : Spatial => Real.cos (waveNumber n * y 0)) x e1
      = ∫ x, -(chi x * (Real.sin (waveNumber n * x 0)) ^ 2) := by
    congr 1
    funext x
    exact hpt x
  rw [h, hint, integral_neg, neg_neg]

theorem tendsto_integral_cos_mul_endpointWave_disk :
    Tendsto (fun n : ℕ =>
        ∫ x, endpointWave n x * Real.cos (waveNumber n * x 0) ∂diskVolume)
      atTop (𝓝 ((∫ x, chi x) / 2)) := by
  have hh : Tendsto (fun n : ℕ =>
      ∫ x, chi x * (Real.sin (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * (x 0))) ^ 2)
      atTop (𝓝 ((∫ x, chi x) / 2)) :=
    tendsto_chi_sin_sq.comp (tendsto_add_atTop_nat 1)
  refine hh.congr (fun n => ?_)
  have e1 : ∫ x, endpointWave n x * Real.cos (waveNumber n * x 0) ∂diskVolume
      = ∫ x, endpointWave n x * Real.cos (waveNumber n * x 0) :=
    integral_diskVolume_eq (fun x => endpointWave n x * Real.cos (waveNumber n * x 0))
      (fun x hx => by rw [endpointWave_eq_zero_outside n hx, zero_mul])
  rw [e1, integral_cos_mul_endpointWave]
  congr 1
  funext x
  have e : 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x 0 = waveNumber n * x 0 := by
    unfold waveNumber
    push_cast
    ring
  rw [e]

theorem integral_chi_half_pos : 0 < (∫ x, chi x) / 2 :=
  half_pos chi_integral_pos

theorem exists_uniform_endpointWave_bound :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : Spatial, |endpointWave n x| ≤ 2 := by
  obtain ⟨L, hL⟩ := dChi_bound
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hev := tendsto_waveNumber_atTop.eventually (eventually_ge_atTop L)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact ⟨N, fun n hn x => abs_endpointWave_le_two hL0 hL n (hN n hn) x⟩

#print axioms tendsto_integral_endpointWave_mul
#print axioms integral_endpointWave_disk
#print axioms integral_cos_mul_endpointWave
#print axioms tendsto_integral_cos_mul_endpointWave_disk

end MatrixTransport
