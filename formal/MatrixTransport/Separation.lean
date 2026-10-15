import Mathlib
import MatrixTransport.WeakStar
import MatrixTransport.KBLimits
import MatrixTransport.FullLimits
import MatrixTransport.ReactionPath

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace MatrixTransport

def separatedEndpoint (N : ℕ) (n : ℕ) : Spatial → Mat2 := waveEndpoint (n + N)

theorem exists_smooth_positive_separation :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
      (∀ n, ContDiff ℝ ∞ (separatedEndpoint N n)) ∧
      (∀ n x,
        LoewnerLE ((1 / 2 : ℝ) • (1 : Mat2)) (separatedEndpoint N n x) ∧
        LoewnerLE (separatedEndpoint N n x) ((3 / 2 : ℝ) • (1 : Mat2))) ∧
      weakStarConverges (separatedEndpoint N) baseEndpoint ∧
      Tendsto (fun n => wbSquared fullDstar baseEndpoint (separatedEndpoint N n))
        atTop (𝓝 0) ∧
      (∀ n, ENNReal.ofReal c ≤ wbSquared KBDstar baseEndpoint (separatedEndpoint N n) ∧
        wbSquared KBDstar baseEndpoint (separatedEndpoint N n)
          ≤ ENNReal.ofReal (Real.pi / 4)) ∧
      ¬ Tendsto (fun n => wbSquared KBDstar baseEndpoint (separatedEndpoint N n))
        atTop (𝓝 0) := by
  obtain ⟨c, hc, hev⟩ := exists_positive_KB_lower
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨N0, hN0⟩ := exists_uniform_endpointWave_bound
  obtain ⟨N1, hN1⟩ := exists_uniform_waveEndpoint_bounds
  obtain ⟨N, h0, h1, h2⟩ : ∃ N : ℕ, N0 ≤ N ∧ N1 ≤ N ∧ N2 ≤ N :=
    ⟨max N0 (max N1 N2), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hlow : ∀ n : ℕ, ENNReal.ofReal c ≤
      wbSquared KBDstar baseEndpoint (separatedEndpoint N n) :=
    fun n => hN2 (n + N) (by omega)
  have hup : ∀ n : ℕ, wbSquared KBDstar baseEndpoint (separatedEndpoint N n)
      ≤ ENNReal.ofReal (Real.pi / 4) := by
    intro n
    have hb : ∀ x : Spatial, |(1 / 4 : ℝ) * endpointWave (n + N) x| ≤ (1 / 2 : ℝ) := by
      intro x
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      have := hN0 (n + N) (by omega) x
      linarith
    have hcont : Continuous (fun x : Spatial => (1 / 4 : ℝ) * endpointWave (n + N) x) :=
      continuous_const.mul (endpointWave_continuous _)
    exact kbSquared_le_pi_quarter _ hcont hb
  refine ⟨N, c, hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact waveEndpoint_contDiff (n + N)
  · intro n x
    exact hN1 (n + N) (by omega) x
  · intro Φ
    have h := (waveEndpoint_weakStarConverges Φ).comp (tendsto_add_atTop_nat N)
    exact h
  · have h := tendsto_full_wbSquared_zero.comp (tendsto_add_atTop_nat N)
    exact h
  · intro n
    exact ⟨hlow n, hup n⟩
  · intro h
    have h0' : ENNReal.ofReal c ≤ 0 := ge_of_tendsto' h hlow
    exact absurd h0' (not_le.2 (ENNReal.ofReal_pos.2 hc))

#print axioms exists_smooth_positive_separation
#check @exists_smooth_positive_separation

end MatrixTransport

end
