import Mathlib
import MatrixTransport.FullLimits
import MatrixTransport.KBLimits

open Filter Topology

namespace MatrixTransport

theorem no_eventual_uniform_comparison (C : ℝ) :
    ¬ (∀ᶠ n : ℕ in Filter.atTop,
      wbSquared KBDstar (fun _ => density 0)
        (fun x => density ((1/4:ℝ) * endpointWave n x))
      ≤ ENNReal.ofReal C * wbSquared fullDstar (fun _ => density 0)
        (fun x => density ((1/4:ℝ) * endpointWave n x))) := by
  intro h
  obtain ⟨c, hc, hKB⟩ := exists_positive_KB_lower
  have hmul : Tendsto
      (fun n : ℕ => ENNReal.ofReal C * wbSquared fullDstar (fun _ => density 0)
        (fun x => density ((1/4:ℝ) * endpointWave n x)))
      atTop (𝓝 (0 : ENNReal)) := by
    have h0 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C)
      tendsto_full_wbSquared_zero (Or.inr ENNReal.ofReal_ne_top)
    simpa only [mul_zero] using h0
  have hle : ENNReal.ofReal c ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hmul
      (by filter_upwards [hKB, h] with n h1 h2 using h1.trans h2)
  exact absurd (ENNReal.ofReal_pos.mpr hc) (not_lt.mpr hle)

#print axioms MatrixTransport.no_eventual_uniform_comparison

end MatrixTransport
