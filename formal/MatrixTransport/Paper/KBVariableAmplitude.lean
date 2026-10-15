import MatrixTransport.Paper.NativeSeparationRegime

/-! # The variable-amplitude KB certificate of the smooth separation proof -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.NativeSeparation
open MatrixTransport MatrixTransport.ReactionZero.ClosedDomain

/-- The oscillatory Frobenius endpoint pairing appearing in the manuscript. -/
def kbCoefficient (n : ℕ) : ℝ := ∫ x,
  Real.cos (waveNumber n * x 0) *
    frob E (MatrixTransport.density ((1 / 4 : ℝ) * endpointWave n x) - 1) ∂diskVolume

/-- The amplitude is selected separately at every oscillation index. -/
def kbAmplitude (n : ℕ) : ℝ := kbCoefficient n / (2 * Real.pi)

theorem kbCoefficient_eq_pair (n : ℕ) :
    kbCoefficient n = ∫ x, (1 / 4 : ℝ) * endpointWave n x *
      Real.cos (waveNumber n * x 0) ∂diskVolume := by
  unfold kbCoefficient
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [frob, Fin.sum_univ_two, E_zero_zero, E_zero_one, E_one_zero, E_one_one,
    Matrix.sub_apply, Matrix.one_apply, MatrixTransport.density_one_one,
    zero_mul, one_mul, zero_add, add_zero, ite_true]
  ring

/-- Integration by parts gives the literal nonnegative squared-sine integral. -/
theorem kbCoefficient_eq (n : ℕ) :
    kbCoefficient n = (1 / 4 : ℝ) * ∫ x : Spatial,
      chi x * Real.sin (waveNumber n * x 0) ^ 2 := by
  rw [kbCoefficient_eq_pair, rho_quarter_cos]
  rw [integral_diskVolume_eq _ (fun x hx ↦ by
    rw [endpointWave_eq_zero_outside n hx,zero_mul]), integral_cos_mul_endpointWave]

theorem kbCoefficient_tendsto :
    Tendsto kbCoefficient atTop (𝓝 ((1 / 8 : ℝ) * ∫ x : Spatial, chi x)) := by
  have h := tendsto_integral_cos_mul_endpointWave_disk.const_mul (1 / 4 : ℝ)
  have he : (1 / 4 : ℝ) * ((∫ x : Spatial, chi x) / 2) =
      (1 / 8 : ℝ) * ∫ x : Spatial, chi x := by ring
  rw [he] at h
  exact h.congr (fun n ↦ (rho_quarter_cos n).symm.trans (kbCoefficient_eq_pair n).symm)

theorem kbCoefficient_limit_pos : 0 < (1 / 8 : ℝ) * ∫ x : Spatial, chi x :=
  mul_pos (by norm_num) chi_integral_pos

theorem kbCoefficient_nonneg (n : ℕ) : 0 ≤ kbCoefficient n := by
  rw [kbCoefficient_eq]
  exact mul_nonneg (by norm_num) (integral_nonneg fun x ↦
    mul_nonneg (chi_nonneg x) (sq_nonneg _))

theorem kbCoefficient_le (n : ℕ) : kbCoefficient n ≤ Real.pi / 4 := by
  rw [kbCoefficient_eq]
  have hsup : ∀ x ∉ disk, chi x * Real.sin (waveNumber n * x 0) ^ 2 = 0 := by
    intro x hx
    have hz : chi x = 0 := by
      by_contra hn
      exact hx (chi_tsupport_subset_disk (subset_tsupport _ (Function.mem_support.2 hn)))
    simp [hz]
  rw [← integral_diskVolume_eq _ hsup]
  have hi : Integrable (fun x : Spatial ↦ chi x * Real.sin (waveNumber n * x 0) ^ 2)
      diskVolume :=
    (integrable_chi_mul ((Real.continuous_sin.comp
      (continuous_const.mul continuous_coord)).pow 2)).integrableOn
  have hm : (∫ x : Spatial, chi x * Real.sin (waveNumber n * x 0) ^ 2 ∂diskVolume) ≤
      ∫ _x : Spatial, (1 : ℝ) ∂diskVolume := by
    apply integral_mono hi (integrable_const _)
    intro x
    have hs := Real.abs_sin_le_one (waveNumber n * x 0)
    have hs2 : Real.sin (waveNumber n * x 0) ^ 2 ≤ 1 := by
      nlinarith [sq_abs (Real.sin (waveNumber n * x 0)),abs_nonneg (Real.sin (waveNumber n * x 0))]
    exact (mul_le_mul_of_nonneg_left hs2 (chi_nonneg x)).trans (by simpa using chi_le_one x)
  have hc := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1 / 4)
  simp only [integral_const,smul_eq_mul,mul_one,diskVolume_real_univ_eq_pi] at hc
  linarith [hc]

theorem kbAmplitude_mem (n : ℕ) : 0 ≤ kbAmplitude n ∧ kbAmplitude n ≤ 1 / 8 := by
  have hpi := Real.pi_pos
  constructor
  · exact div_nonneg (kbCoefficient_nonneg n) (by positivity)
  · unfold kbAmplitude
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h := kbCoefficient_le n
    nlinarith

/-- Scalar multiples of E retain the scalar Loewner order. -/
theorem loewner_smul_E (v w : ℝ) (h : v ≤ w) : LoewnerLE (v • E) (w • E) := by
  unfold LoewnerLE
  convert psd_diag2 0 (w - v) (le_refl 0) (sub_nonneg.2 h) using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E]

/-- The displayed HJ inequality is evaluated at the actual time and cosine of q. -/
theorem kb_hj_display (n : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 8)
    (q : MatrixTransport.Q) :
    dtPhi (certificateField n a) q.val + (1 / 2 : ℝ) •
        (certificateMatrix n a q.val * certificateMatrix n a q.val) =
      (-a ^ 2 + (1 / 2 : ℝ) * certificateScalar n a q.val ^ 2) • E ∧
    LoewnerLE (dtPhi (certificateField n a) q.val + (1 / 2 : ℝ) •
        (certificateMatrix n a q.val * certificateMatrix n a q.val))
      ((a ^ 2 * (-1 + (1 / 2 : ℝ) * (1 + a) ^ 2)) • E) ∧
    LoewnerLE ((a ^ 2 * (-1 + (1 / 2 : ℝ) * (1 + a) ^ 2)) • E) 0 := by
  have he : dtPhi (certificateField n a) q.val + (1 / 2 : ℝ) •
      (certificateMatrix n a q.val * certificateMatrix n a q.val) =
      (-a ^ 2 + (1 / 2 : ℝ) * certificateScalar n a q.val ^ 2) • E := by
    rw [certificateField_dtPhi]
    simp only [certificateMatrix,Matrix.smul_mul,Matrix.mul_smul,E_mul_E,smul_smul]
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  have ht := q.property.1
  have hc := Real.abs_cos_le_one (waveNumber n * q.val.2 0)
  have hcs : |certificateScalar n a q.val| ≤ a * (1 + a) := by
    unfold certificateScalar
    have h1 := abs_sub_le (a * Real.cos (waveNumber n * q.val.2 0)) 0 (a ^ 2 * q.val.1)
    simp only [sub_zero,zero_sub,abs_neg] at h1
    rw [abs_mul,abs_of_nonneg ha0] at h1
    have h2 : |a ^ 2 * q.val.1| = a ^ 2 * q.val.1 :=
      abs_of_nonneg (mul_nonneg (sq_nonneg a) ht.1)
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left hc ha0
    have h4 := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg a)
    nlinarith
  have hs : certificateScalar n a q.val ^ 2 ≤ (a * (1 + a)) ^ 2 := by
    nlinarith [sq_abs (certificateScalar n a q.val),abs_nonneg (certificateScalar n a q.val)]
  have hb : a ^ 2 * (-1 + (1 / 2 : ℝ) * (1 + a) ^ 2) ≤ 0 := by
    have hx : (1 + a) ^ 2 ≤ 2 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) (by linarith)
  refine ⟨he,?_,?_⟩
  · rw [he]
    exact loewner_smul_E _ _ (by nlinarith)
  · simpa only [zero_smul] using loewner_smul_E _ 0 hb

/-- Mean-zero oscillations preserve the endpoint's E-trace integral. -/
theorem integral_E_frob_density (n : ℕ) :
    (∫ x, frob E (MatrixTransport.density ((1 / 4 : ℝ) * endpointWave n x)) ∂diskVolume) =
      Real.pi := by
  have he : (fun x : Spatial ↦ frob E (MatrixTransport.density
      ((1 / 4 : ℝ) * endpointWave n x))) =
      fun x ↦ 1 + (1 / 4 : ℝ) * endpointWave n x := by
    funext x
    simp [frob,Fin.sum_univ_two,E_zero_zero,E_zero_one,E_one_zero,E_one_one,
      MatrixTransport.density_one_one]
  rw [he,integral_add (integrable_const _) (rho_quarter_integrable n),
    rho_quarter_mean,integral_const,diskVolume_real_univ_eq_pi]
  simp

/-- The per-index certificate has exactly the optimized endpoint pairing in the paper. -/
theorem kbVariable_endpointDifference (n : ℕ) :
    endpointDifference (fun _ ↦ MatrixTransport.density 0)
      (fun x ↦ MatrixTransport.density ((1 / 4 : ℝ) * endpointWave n x))
      (certificateField n (kbAmplitude n)) = kbCoefficient n ^ 2 / (4 * Real.pi) := by
  rw [certificateField_endpointDifference n (kbAmplitude n) _
    (rho_quarter_integrable n) (rho_quarter_mean n),← kbCoefficient_eq_pair]
  unfold kbAmplitude
  have hp := Real.pi_ne_zero
  field_simp
  ring

/-- The universal certificate bound specialized to the exact variable amplitude. -/
theorem kbVariable_lower (n : ℕ) :
    ENNReal.ofReal (kbCoefficient n ^ 2 / (4 * Real.pi)) ≤
      wbSquared KBDstar (fun _ ↦ MatrixTransport.density 0)
        (fun x ↦ MatrixTransport.density ((1 / 4 : ℝ) * endpointWave n x)) := by
  have h := certificateField_lower_bound n (kbAmplitude n)
    (fun x ↦ (1 / 4 : ℝ) * endpointWave n x)
    (rho_quarter_integrable n) (rho_quarter_mean n)
    (kbAmplitude_mem n).1 (kbAmplitude_mem n).2
  have he := kbVariable_endpointDifference n
  rw [certificateField_endpointDifference n (kbAmplitude n) _
    (rho_quarter_integrable n) (rho_quarter_mean n)] at he
  rw [he] at h
  exact h

/-- A positive lower bound follows eventually from the variable-amplitude certificates. -/
theorem exists_positive_KB_lower_variable :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal c ≤ wbSquared KBDstar (fun _ ↦ MatrixTransport.density 0)
        (fun x ↦ MatrixTransport.density ((1 / 4 : ℝ) * endpointWave n x)) := by
  let b : ℝ := (1 / 8 : ℝ) * ∫ x : Spatial, chi x
  have hb : 0 < b := kbCoefficient_limit_pos
  have hev : ∀ᶠ n : ℕ in atTop, b / 2 < kbCoefficient n :=
    kbCoefficient_tendsto.eventually (lt_mem_nhds (by change b / 2 < b; linarith))
  refine ⟨b ^ 2 / (16 * Real.pi),by positivity,?_⟩
  filter_upwards [hev] with n hn
  apply (ENNReal.ofReal_le_ofReal ?_).trans (kbVariable_lower n)
  have hprod : 0 ≤ (kbCoefficient n - b / 2) * (kbCoefficient n + b / 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hs : (b / 2) ^ 2 ≤ kbCoefficient n ^ 2 := by nlinarith
  have h := div_le_div_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
  calc
    b ^ 2 / (16 * Real.pi) = (b / 2) ^ 2 / (4 * Real.pi) := by ring
    _ ≤ _ := h

#print axioms kbCoefficient_eq
#print axioms kbCoefficient_tendsto
#print axioms kbAmplitude_mem
#print axioms kb_hj_display
#print axioms integral_E_frob_density
#print axioms kbVariable_endpointDifference
#print axioms kbVariable_lower
#print axioms exists_positive_KB_lower_variable
end LiZouTransport.NativeSeparation
