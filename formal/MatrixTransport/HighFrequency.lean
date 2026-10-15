import Mathlib
import MatrixTransport.Bump

open MeasureTheory Filter Topology

namespace MatrixTransport

noncomputable def frequencyVector (n : ℕ) : Spatial := (n : ℝ) • e1

noncomputable def oscillatoryCos (n : ℕ) (x : Spatial) : ℝ :=
  Real.cos (2 * Real.pi * (n : ℝ) * (x 0))

theorem norm_e1 : ‖e1‖ = 1 := by
  simp [e1]

theorem norm_frequencyVector (n : ℕ) : ‖frequencyVector n‖ = n := by
  simp [frequencyVector, norm_smul, norm_e1]

theorem tendsto_frequencyVector :
    Tendsto frequencyVector atTop (cocompact Spatial) := by
  have h : Tendsto (fun n : ℕ => ‖frequencyVector n‖) atTop atTop := by
    simp only [norm_frequencyVector]
    exact tendsto_natCast_atTop_atTop
  rw [← Metric.cobounded_eq_cocompact]
  exact tendsto_norm_atTop_iff_cobounded.1 h

theorem inner_frequencyVector (v : Spatial) (n : ℕ) :
    inner ℝ v (frequencyVector n) = (n : ℝ) * v 0 := by
  simp [frequencyVector, e1, inner_smul_right, EuclideanSpace.inner_single_right]

theorem re_phase_smul (f : Spatial → ℝ) (n : ℕ) (v : Spatial) :
    (Real.fourierChar (-(inner ℝ v (frequencyVector n))) • (f v : ℂ)).re
      = f v * oscillatoryCos n v := by
  rw [inner_frequencyVector, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
    Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [Complex.exp_ofReal_mul_I_re]
  simp only [oscillatoryCos]
  have h : 2 * Real.pi * (-((n : ℝ) * v 0)) = -(2 * Real.pi * (n : ℝ) * v 0) := by ring
  rw [h, Real.cos_neg, mul_comm]

theorem tendsto_integral_mul_oscillatoryCos {f : Spatial → ℝ} (hf : Integrable f volume) :
    Tendsto (fun n : ℕ => ∫ x, f x * oscillatoryCos n x) atTop (𝓝 0) := by
  have hf' : Integrable (fun x => (f x : ℂ)) volume := hf.ofReal
  have hRL := (tendsto_integral_exp_inner_smul_cocompact (fun x => (f x : ℂ))).comp
    tendsto_frequencyVector
  have hre : Tendsto (fun n : ℕ =>
      (∫ v, Real.fourierChar (-(inner ℝ v (frequencyVector n))) • (f v : ℂ)).re)
      atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto 0).comp hRL
    have h0 : Complex.re 0 = 0 := Complex.zero_re
    rw [h0] at h
    exact h
  have key : ∀ n : ℕ,
      (∫ v, Real.fourierChar (-(inner ℝ v (frequencyVector n))) • (f v : ℂ)).re
        = ∫ x, f x * oscillatoryCos n x := by
    intro n
    have hint : Integrable
        (fun v => Real.fourierChar (-(inner ℝ v (frequencyVector n))) • (f v : ℂ))
        volume :=
      (Real.fourierIntegral_convergent_iff (frequencyVector n)).2 hf'
    have h1 := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at h1
    rw [← h1]
    congr 1
    funext v
    exact re_phase_smul f n v
  exact hre.congr key

theorem continuous_oscillatoryCos (n : ℕ) : Continuous (oscillatoryCos n) := by
  have hc : Continuous (fun x : Spatial => x 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Spatial →L[ℝ] ℝ).continuous
  unfold oscillatoryCos
  exact Real.continuous_cos.comp (continuous_const.mul hc)

theorem integrable_chi_mul_cos (m : ℕ) :
    Integrable (fun x => chi x * oscillatoryCos m x) volume := by
  refine Integrable.mono' chi_integrable
    (chi_continuous.aestronglyMeasurable.mul
      (continuous_oscillatoryCos m).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (chi_nonneg x)]
  exact mul_le_of_le_one_right (chi_nonneg x) (by unfold oscillatoryCos; exact Real.abs_cos_le_one _)

theorem chi_sin_sq_pointwise (n : ℕ) (x : Spatial) :
    chi x * (Real.sin (2 * Real.pi * (n : ℝ) * (x 0))) ^ 2
      = chi x / 2 - (chi x * oscillatoryCos (2 * n) x) / 2 := by
  unfold oscillatoryCos
  have h := Real.cos_two_mul (2 * Real.pi * (n : ℝ) * x 0)
  have h2 := Real.sin_sq_add_cos_sq (2 * Real.pi * (n : ℝ) * x 0)
  have hs : (Real.sin (2 * Real.pi * (n : ℝ) * x 0)) ^ 2
      = 1 - (Real.cos (2 * Real.pi * (n : ℝ) * x 0)) ^ 2 := by linarith
  push_cast
  have e : 2 * Real.pi * (2 * (n : ℝ)) * x 0 = 2 * (2 * Real.pi * (n : ℝ) * x 0) := by ring
  rw [e, h, hs]
  ring

theorem tendsto_chi_sin_sq :
    Tendsto (fun n : ℕ => ∫ x, chi x * (Real.sin (2 * Real.pi * (n : ℝ) * (x 0))) ^ 2)
      atTop (𝓝 ((∫ x, chi x) / 2)) := by
  have hcos := tendsto_integral_mul_oscillatoryCos chi_integrable
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => (by show n ≤ 2 * n; omega)) tendsto_id
  have h3 : Tendsto (fun n : ℕ => ∫ x, chi x * oscillatoryCos (2 * n) x) atTop (𝓝 0) :=
    hcos.comp h2
  have h4 := (tendsto_const_nhds (x := (∫ x, chi x) / 2)).sub (h3.div_const 2)
  have h5 : (∫ x, chi x) / 2 - 0 / 2 = (∫ x, chi x) / 2 := by ring
  rw [h5] at h4
  have key : ∀ n : ℕ,
      (∫ x, chi x) / 2 - (∫ x, chi x * oscillatoryCos (2 * n) x) / 2
        = ∫ x, chi x * (Real.sin (2 * Real.pi * (n : ℝ) * (x 0))) ^ 2 := by
    intro n
    have e : (fun x : Spatial => chi x * (Real.sin (2 * Real.pi * (n : ℝ) * (x 0))) ^ 2)
        = fun x => chi x / 2 - (chi x * oscillatoryCos (2 * n) x) / 2 :=
      funext (chi_sin_sq_pointwise n)
    rw [e, integral_sub (chi_integrable.div_const 2)
      ((integrable_chi_mul_cos (2 * n)).div_const 2), integral_div, integral_div]
  exact h4.congr key

end MatrixTransport
