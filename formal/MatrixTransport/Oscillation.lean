import Mathlib
import MatrixTransport.HighFrequency

open MeasureTheory Filter Topology
open scoped ContDiff

namespace MatrixTransport

noncomputable def waveNumber (n : ℕ) : ℝ := 2 * Real.pi * ((n : ℝ) + 1)

noncomputable def primitiveWave (n : ℕ) (x : Spatial) : ℝ :=
  chi x * Real.sin (waveNumber n * x 0) / waveNumber n

noncomputable def endpointWave (n : ℕ) (x : Spatial) : ℝ :=
  dChi x * Real.sin (waveNumber n * x 0) / waveNumber n
    + chi x * Real.cos (waveNumber n * x 0)

noncomputable abbrev coord0 : Spatial →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)

theorem coord0_e1 : coord0 e1 = 1 := by
  first
    | simp [e1]
    | (show e1 0 = 1; simp [e1])

theorem continuous_coord : Continuous (fun x : Spatial => x 0) := coord0.continuous

theorem contDiff_coord : ContDiff ℝ ∞ (fun x : Spatial => x 0) := coord0.contDiff

theorem waveNumber_pos (n : ℕ) : 0 < waveNumber n := by
  have := Real.pi_pos
  unfold waveNumber
  positivity

theorem waveNumber_ne_zero (n : ℕ) : waveNumber n ≠ 0 := (waveNumber_pos n).ne'

theorem tendsto_waveNumber_atTop : Tendsto waveNumber atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h2 := h1.const_mul_atTop (by have := Real.pi_pos; positivity : (0 : ℝ) < 2 * Real.pi)
  exact h2

theorem primitiveWave_contDiff (n : ℕ) : ContDiff ℝ ∞ (primitiveWave n) := by
  unfold primitiveWave
  exact (chi_contDiff.mul
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_coord))).div_const _

theorem primitiveWave_continuous (n : ℕ) : Continuous (primitiveWave n) :=
  (primitiveWave_contDiff n).continuous

theorem primitiveWave_differentiable (n : ℕ) : Differentiable ℝ (primitiveWave n) :=
  (primitiveWave_contDiff n).differentiable (by simp)

theorem support_primitiveWave_subset (n : ℕ) :
    Function.support (primitiveWave n) ⊆ Function.support chi := by
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h
  apply hx
  simp [primitiveWave, h]

theorem tsupport_primitiveWave_subset (n : ℕ) : tsupport (primitiveWave n) ⊆ tsupport chi :=
  closure_mono (support_primitiveWave_subset n)

theorem primitiveWave_compact (n : ℕ) : HasCompactSupport (primitiveWave n) := by
  have hc : IsCompact (tsupport chi) := chi_compact
  have : IsCompact (tsupport (primitiveWave n)) :=
    IsCompact.of_isClosed_subset hc (isClosed_tsupport _) (tsupport_primitiveWave_subset n)
  exact this

theorem support_endpointWave_subset (n : ℕ) :
    Function.support (endpointWave n) ⊆ tsupport chi := by
  intro x hx
  by_contra hxc
  apply hx
  have h1 : chi x = 0 := by
    by_contra h
    exact hxc (subset_tsupport chi h)
  have h2 : dChi x = 0 := by
    by_contra h
    exact hxc (dChi_tsupport_subset (subset_tsupport dChi h))
  simp [endpointWave, h1, h2]

theorem tsupport_endpointWave_subset (n : ℕ) : tsupport (endpointWave n) ⊆ tsupport chi :=
  closure_minimal (support_endpointWave_subset n) (isClosed_tsupport _)

theorem endpointWave_continuous (n : ℕ) : Continuous (endpointWave n) := by
  have harg : Continuous (fun x : Spatial => waveNumber n * x 0) :=
    continuous_const.mul continuous_coord
  unfold endpointWave
  exact ((dChi_continuous.mul (Real.continuous_sin.comp harg)).div_const _).add
    (chi_continuous.mul (Real.continuous_cos.comp harg))

theorem endpointWave_compact (n : ℕ) : HasCompactSupport (endpointWave n) := by
  have hc : IsCompact (tsupport chi) := chi_compact
  have : IsCompact (tsupport (endpointWave n)) :=
    IsCompact.of_isClosed_subset hc (isClosed_tsupport _) (tsupport_endpointWave_subset n)
  exact this

theorem integrable_primitiveWave (n : ℕ) : Integrable (primitiveWave n) volume :=
  (primitiveWave_continuous n).integrable_of_hasCompactSupport (primitiveWave_compact n)

theorem integrable_endpointWave (n : ℕ) : Integrable (endpointWave n) volume :=
  (endpointWave_continuous n).integrable_of_hasCompactSupport (endpointWave_compact n)

theorem fderiv_primitiveWave_e1 (n : ℕ) (x : Spatial) :
    fderiv ℝ (primitiveWave n) x e1 = endpointWave n x := by
  have hw := waveNumber_ne_zero n
  have hc : HasFDerivAt chi (fderiv ℝ chi x) x :=
    (chi_contDiff.differentiable (by simp) x).hasFDerivAt
  have hp : HasFDerivAt (fun y : Spatial => y 0) coord0 x :=
    coord0.hasFDerivAt
  have hs := (hp.const_mul (waveNumber n)).sin
  have hm := hc.mul hs
  have hd := hm.const_smul ((waveNumber n)⁻¹)
  have hfun : (fun y : Spatial => (waveNumber n)⁻¹ •
      (chi y * Real.sin (waveNumber n * y 0))) = primitiveWave n := by
    funext y
    simp [primitiveWave, div_eq_mul_inv, smul_eq_mul, mul_comm]
  change HasFDerivAt (fun y : Spatial => (waveNumber n)⁻¹ •
    (chi y * Real.sin (waveNumber n * y 0))) _ x at hd
  rw [hfun] at hd
  have h1 : fderiv ℝ (primitiveWave n) x = _ := hd.fderiv
  rw [h1]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, coord0_e1,
    smul_eq_mul, ContinuousLinearMap.coe_add', ContinuousLinearMap.coe_smul', Pi.add_apply,
    Pi.smul_apply]
  unfold endpointWave dChi
  have hinv : (waveNumber n)⁻¹ * waveNumber n = 1 := inv_mul_cancel₀ hw
  linear_combination (chi x * Real.cos (waveNumber n * x 0)) * hinv

theorem abs_endpointWave_le {L : ℝ} (hL : 0 ≤ L) (hd : ∀ x, |dChi x| ≤ L) (n : ℕ)
    (x : Spatial) : |endpointWave n x| ≤ 1 + L / waveNumber n := by
  have hw := waveNumber_pos n
  have h1 : |dChi x * Real.sin (waveNumber n * x 0) / waveNumber n| ≤ L / waveNumber n := by
    rw [abs_div, abs_of_pos hw, abs_mul]
    have h : |dChi x| * |Real.sin (waveNumber n * x 0)| ≤ L :=
      calc |dChi x| * |Real.sin (waveNumber n * x 0)| ≤ L * 1 :=
            mul_le_mul (hd x) (Real.abs_sin_le_one _) (abs_nonneg _) hL
        _ = L := mul_one L
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h (inv_nonneg.2 hw.le)
  have h2 : |chi x * Real.cos (waveNumber n * x 0)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (chi_nonneg x)]
    calc chi x * |Real.cos (waveNumber n * x 0)| ≤ 1 * 1 :=
          mul_le_mul (chi_le_one x) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h3 := abs_add_le (dChi x * Real.sin (waveNumber n * x 0) / waveNumber n)
    (chi x * Real.cos (waveNumber n * x 0))
  unfold endpointWave
  linarith

theorem abs_endpointWave_le_two {L : ℝ} (hL : 0 ≤ L) (hd : ∀ x, |dChi x| ≤ L) (n : ℕ)
    (hLw : L ≤ waveNumber n) (x : Spatial) : |endpointWave n x| ≤ 2 := by
  have h := abs_endpointWave_le hL hd n x
  have h' : L / waveNumber n ≤ 1 := (div_le_one (waveNumber_pos n)).2 hLw
  linarith

theorem abs_primitiveWave_le (n : ℕ) (x : Spatial) :
    |primitiveWave n x| ≤ chi x / waveNumber n := by
  have hw := waveNumber_pos n
  unfold primitiveWave
  rw [abs_div, abs_of_pos hw, abs_mul, abs_of_nonneg (chi_nonneg x)]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (chi_nonneg x) (Real.abs_sin_le_one _)) (inv_nonneg.2 hw.le)

theorem primitiveWave_sq_le (n : ℕ) (x : Spatial) :
    primitiveWave n x ^ 2 ≤ chi x ^ 2 / waveNumber n ^ 2 := by
  have h := abs_primitiveWave_le n x
  have h2 : |primitiveWave n x| ^ 2 ≤ (chi x / waveNumber n) ^ 2 := by
    first
      | exact pow_le_pow_left₀ (abs_nonneg _) h 2
      | gcongr
  calc primitiveWave n x ^ 2 = |primitiveWave n x| ^ 2 := (sq_abs _).symm
    _ ≤ (chi x / waveNumber n) ^ 2 := h2
    _ = chi x ^ 2 / waveNumber n ^ 2 := div_pow _ _ _

theorem integral_endpointWave_mul_eq (n : ℕ) (g : Spatial → ℝ)
    (h1 : Integrable (fun x => primitiveWave n x * g x) volume)
    (h2 : Integrable (fun x => endpointWave n x * g x) volume)
    (h3 : Integrable (fun x => primitiveWave n x * fderiv ℝ g x e1) volume)
    (hg : ∀ x ∈ tsupport chi, DifferentiableAt ℝ g x) :
    ∫ x, endpointWave n x * g x = - ∫ x, primitiveWave n x * fderiv ℝ g x e1 := by
  have e : ∫ x, fderiv ℝ (primitiveWave n) x e1 * g x = ∫ x, endpointWave n x * g x := by
    simp only [fderiv_primitiveWave_e1]
  have eI : Integrable (fun x => fderiv ℝ (primitiveWave n) x e1 * g x) volume := by
    simp only [fderiv_primitiveWave_e1]
    exact h2
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := primitiveWave n) (g := g) (v := e1) eI h3 h1
    (fun x _ => primitiveWave_differentiable n x)
    (fun x hx => hg x (tsupport_primitiveWave_subset n hx))
  linarith [key, e]

theorem integral_endpointWave (n : ℕ) : ∫ x, endpointWave n x = 0 := by
  have hz : ∀ x : Spatial, fderiv ℝ (fun _ : Spatial => (1 : ℝ)) x e1 = 0 := by
    intro x
    simp
  have h := integral_endpointWave_mul_eq n (fun _ => (1 : ℝ))
    (by simpa using integrable_primitiveWave n)
    (by simpa using integrable_endpointWave n)
    (by simp [hz])
    (fun x _ => differentiableAt_const _)
  simpa [hz] using h

#print axioms fderiv_primitiveWave_e1
#print axioms integral_endpointWave_mul_eq
#print axioms integral_endpointWave

end MatrixTransport
