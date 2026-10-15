import Mathlib
import MatrixTransport.EndpointLimits
import MatrixTransport.KBCertificate

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MatrixTransport

theorem rho_quarter_integrable (n : ℕ) :
    Integrable (fun x : Spatial => (1 / 4 : ℝ) * endpointWave n x) diskVolume := by
  have h : Integrable (endpointWave n) diskVolume := (integrable_endpointWave n).integrableOn
  exact h.const_mul _

theorem rho_quarter_mean (n : ℕ) :
    (∫ x, (1 / 4 : ℝ) * endpointWave n x ∂diskVolume) = 0 := by
  rw [integral_const_mul, integral_endpointWave_disk, mul_zero]

theorem rho_quarter_cos (n : ℕ) :
    (∫ x, (1 / 4 : ℝ) * endpointWave n x * Real.cos (waveNumber n * x 0) ∂diskVolume)
      = (1 / 4 : ℝ) * ∫ x, endpointWave n x * Real.cos (waveNumber n * x 0) ∂diskVolume := by
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem exists_positive_KB_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal c ≤ wbSquared KBDstar (fun _ => density 0)
        (fun x => density ((1 / 4 : ℝ) * endpointWave n x)) := by
  have hI := chi_integral_pos
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (1 / 4 : ℝ) * ((∫ x, chi x) / 2) := ⟨_, rfl⟩
  have hbpos : 0 < b := by rw [hb]; linarith
  have hT : Tendsto (fun n : ℕ =>
      ∫ x, (1 / 4 : ℝ) * endpointWave n x * Real.cos (waveNumber n * x 0) ∂diskVolume)
      atTop (𝓝 b) := by
    have h := tendsto_integral_cos_mul_endpointWave_disk.const_mul (1 / 4 : ℝ)
    rw [← hb] at h
    exact h.congr (fun n => (rho_quarter_cos n).symm)
  have hev : ∀ᶠ n : ℕ in atTop, 3 / 4 * b <
      ∫ x, (1 / 4 : ℝ) * endpointWave n x * Real.cos (waveNumber n * x 0) ∂diskVolume :=
    hT.eventually (lt_mem_nhds (by linarith))
  have hpi := Real.pi_pos
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min (1 / 8 : ℝ) (b / (4 * Real.pi)) := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs]
    exact lt_min (by norm_num) (div_pos hbpos (by positivity))
  have hs8 : s ≤ 1 / 8 := by rw [hs]; exact min_le_left _ _
  have hs2 : s ≤ b / (4 * Real.pi) := by rw [hs]; exact min_le_right _ _
  have hs3 : s * (4 * Real.pi) ≤ b := (le_div_iff₀ (by positivity)).1 hs2
  have hspi : s * Real.pi ≤ b / 4 := by linarith
  refine ⟨s * b / 2, by positivity, ?_⟩
  filter_upwards [hev] with n hn
  have h1 : s * (3 / 4 * b) ≤ s * (∫ x, (1 / 4 : ℝ) * endpointWave n x
      * Real.cos (waveNumber n * x 0) ∂diskVolume) :=
    mul_le_mul_of_nonneg_left hn.le hs0.le
  have h2 : s * (s * Real.pi) ≤ s * (b / 4) :=
    mul_le_mul_of_nonneg_left hspi hs0.le
  have hsq : s ^ 2 * Real.pi = s * (s * Real.pi) := by ring
  have key : s * b / 2 ≤ s * (∫ x, (1 / 4 : ℝ) * endpointWave n x
      * Real.cos (waveNumber n * x 0) ∂diskVolume) - s ^ 2 * Real.pi := by
    rw [hsq]
    linarith
  have h := certificateField_lower_bound n s (fun x : Spatial => (1 / 4 : ℝ) * endpointWave n x)
    (rho_quarter_integrable n) (rho_quarter_mean n) hs0.le hs8
  exact (ENNReal.ofReal_le_ofReal key).trans h

theorem not_tendsto_KB_zero :
    ¬ Tendsto (fun n : ℕ => wbSquared KBDstar (fun _ => density 0)
      (fun x => density ((1 / 4 : ℝ) * endpointWave n x))) atTop (𝓝 0) := by
  intro h
  obtain ⟨c, hc, hev⟩ := exists_positive_KB_lower
  have h0 : ENNReal.ofReal c ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds h hev
  exact absurd h0 (not_le.2 (ENNReal.ofReal_pos.2 hc))

#print axioms exists_positive_KB_lower
#print axioms not_tendsto_KB_zero

end MatrixTransport
