import MatrixTransport.AffineContinuity
import MatrixTransport.EndpointLimits

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace MatrixTransport

theorem full_wbSquared_upper (n : ℕ) (eps : ℝ)
    (hb : ∀ x : Spatial, |eps * endpointWave n x| ≤ (1 / 2 : ℝ)) :
    wbSquared fullDstar (fun _ => density 0) (fun x => density (eps * endpointWave n x))
      ≤ ENNReal.ofReal (Real.pi * eps ^ 2 / waveNumber n ^ 2) :=
  (wbSquared_le_action fullDstar _ _ (affinePath n eps)
    (affinePath_continuityEquation n eps)).trans (affinePath_action_le n eps hb)

theorem eventual_full_wbSquared_upper :
    ∀ᶠ n : ℕ in Filter.atTop,
      wbSquared fullDstar (fun _ => density 0)
          (fun x => density ((1 / 4 : ℝ) * endpointWave n x))
        ≤ ENNReal.ofReal (Real.pi / 16 / waveNumber n ^ 2) := by
  obtain ⟨N, hN⟩ := exists_uniform_endpointWave_bound
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hb : ∀ x : Spatial, |(1 / 4 : ℝ) * endpointWave n x| ≤ (1 / 2 : ℝ) := by
    intro x
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have h := hN n hn x
    linarith
  exact (full_wbSquared_upper n (1 / 4) hb).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))

theorem tendsto_real_upper_bound :
    Tendsto (fun n : ℕ => Real.pi / 16 / waveNumber n ^ 2) atTop (𝓝 0) := by
  have h := ((tendsto_inv_atTop_zero.comp tendsto_waveNumber_atTop).pow 2).const_mul
    (Real.pi / 16)
  have h2 : Tendsto (fun n : ℕ => Real.pi / 16 * ((waveNumber n)⁻¹ ^ 2)) atTop
      (𝓝 (Real.pi / 16 * (0 : ℝ) ^ 2)) := h
  rw [show Real.pi / 16 * (0 : ℝ) ^ 2 = 0 by norm_num] at h2
  exact h2.congr (fun n => by ring)

theorem tendsto_ennreal_upper_bound :
    Tendsto (fun n : ℕ => ENNReal.ofReal (Real.pi / 16 / waveNumber n ^ 2)) atTop
      (𝓝 (0 : ℝ≥0∞)) := by
  have h := ENNReal.tendsto_ofReal tendsto_real_upper_bound
  rwa [ENNReal.ofReal_zero] at h

theorem tendsto_full_wbSquared_zero :
    Tendsto (fun n : ℕ => wbSquared fullDstar (fun _ => density 0)
        (fun x => density ((1 / 4 : ℝ) * endpointWave n x))) atTop (𝓝 (0 : ℝ≥0∞)) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_ennreal_upper_bound
    (Filter.Eventually.of_forall fun _ => bot_le)
    eventual_full_wbSquared_upper

end MatrixTransport

end

#print axioms MatrixTransport.full_wbSquared_upper
#print axioms MatrixTransport.eventual_full_wbSquared_upper
#print axioms MatrixTransport.tendsto_full_wbSquared_zero
