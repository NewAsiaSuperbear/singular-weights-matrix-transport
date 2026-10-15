import MatrixTransport.PartialWeights.Regime
import MatrixTransport.PartialWeights.KernelExtinction

/-!
# The complete original-model simultaneous partial-weight regime

The actual signed Radon action, original closed-domain continuity equation and independent
transport/reaction dimensions are retained. The final certificate joins extended value
convergence, PSD attainment, all near-minimizer clusters and genuine Frobenius variation
extinction in every fixed target-kernel direction. No compactness, LSC, recovery or
variation conclusion is assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialWeights

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {n k d p q : ℕ} {Ω : Set (ClosedDomain.Space d)}
variable [Fact (IsCompact Ω)]

/-- Finite-target near-minimizers lose every rectangular forbidden transport direction. -/
theorem nearMinimizer_rightFluxFrobeniusTV_tendsto_zero (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧
      (gram (L j) - α j • gram Lstar).PosSemidef ∧
      (gram (H j) - α j • gram Hstar).PosSemidef)
    (hb : minimumValue P Lstar Hstar ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hg : ∀ j, Good P (μ j)) (η : ℕ → ℝ≥0∞) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ j, action (L j) (H j) (μ j) ≤ minimumValue P (L j) (H j) + η j)
    (A : Matrix (Fin k) (Fin p) ℝ) (hA : Lstar.transpose * A = 0) :
    Tendsto (fun j ↦ rightFluxFrobeniusTV (μ j) A) atTop (𝓝 0) := by
  have ht := nearMinimizer_energy_tendsto P L Lstar hL H Hstar hH
    α hα hconditions μ hg η hη hnear
  obtain ⟨C, hbC, hCtop⟩ := exists_between (lt_top_iff_ne_top.mpr hb)
  have hbound : ∀ᶠ j in atTop, action (L j) (H j) (μ j) ≤ C :=
    (ht.eventually (gt_mem_nhds hbC)).mono fun _ h ↦ h.le
  exact rightFluxFrobeniusTV_tendsto_zero_of_eventually_bounded
    P L Lstar hL H Hstar hH C hCtop.ne μ hg hbound A hA

/-- Finite-target near-minimizers lose every fixed forbidden full-reaction direction. -/
theorem nearMinimizer_rightReactionFrobeniusTV_tendsto_zero (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧
      (gram (L j) - α j • gram Lstar).PosSemidef ∧
      (gram (H j) - α j • gram Hstar).PosSemidef)
    (hb : minimumValue P Lstar Hstar ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hg : ∀ j, Good P (μ j)) (η : ℕ → ℝ≥0∞) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ j, action (L j) (H j) (μ j) ≤ minimumValue P (L j) (H j) + η j)
    (A : Matrix (Fin n) (Fin p) ℝ) (hA : Hstar.transpose * A = 0) :
    Tendsto (fun j ↦ PartialReaction.rightReactionFrobeniusTV (μ j) A)
      atTop (𝓝 0) := by
  have ht := nearMinimizer_energy_tendsto P L Lstar hL H Hstar hH
    α hα hconditions μ hg η hη hnear
  obtain ⟨C, hbC, hCtop⟩ := exists_between (lt_top_iff_ne_top.mpr hb)
  have hbound : ∀ᶠ j in atTop, action (L j) (H j) (μ j) ≤ C :=
    (ht.eventually (gt_mem_nhds hbC)).mono fun _ h ↦ h.le
  exact rightReactionFrobeniusTV_tendsto_zero_of_eventually_bounded
    P L H Hstar hH C hCtop.ne μ hg hbound A hA

/-- Complete simultaneous partial-weight certificate for the original finite signed Radon
problem. Infinite target values, singular weights and arbitrary dimensions are included.
Every finite-target minimizing cluster has PSD mass, and both genuine matrix variations
vanish along the whole near-minimizing sequence in every forbidden target direction. -/
theorem partial_weights_regime (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧
      (gram (L j) - α j • gram Lstar).PosSemidef ∧
      (gram (H j) - α j • gram Hstar).PosSemidef) :
    Tendsto (fun j ↦ minimumValue P (L j) (H j)) atTop
      (𝓝 (minimumValue P Lstar Hstar)) ∧
    (minimumValue P Lstar Hstar ≠ ⊤ →
      ∃ ν : Path Ω n k, Good P ν ∧ action Lstar Hstar ν = minimumValue P Lstar Hstar ∧
        ∀ B, MeasurableSet B → (MatrixPositivity.massMeasureValue ν B).PosSemidef) ∧
    (∀ (μ : ℕ → Path Ω n k), (∀ j, Good P (μ j)) →
      ∀ (η : ℕ → ℝ≥0∞), Tendsto η atTop (𝓝 0) →
      (∀ j, action (L j) (H j) (μ j) ≤ minimumValue P (L j) (H j) + η j) →
      Tendsto (fun j ↦ action (L j) (H j) (μ j)) atTop
        (𝓝 (minimumValue P Lstar Hstar)) ∧
      (minimumValue P Lstar Hstar ≠ ⊤ →
        (∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
          SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν ∧
          action Lstar Hstar ν = minimumValue P Lstar Hstar ∧
          ∀ B, MeasurableSet B → (MatrixPositivity.massMeasureValue ν B).PosSemidef) ∧
        (∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (ν : Path Ω n k),
          SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν →
          Good P ν ∧ action Lstar Hstar ν = minimumValue P Lstar Hstar ∧
          ∀ B, MeasurableSet B → (MatrixPositivity.massMeasureValue ν B).PosSemidef) ∧
        (∀ (A : Matrix (Fin k) (Fin p) ℝ), Lstar.transpose * A = 0 →
          Tendsto (fun j ↦ rightFluxFrobeniusTV (μ j) A) atTop (𝓝 0)) ∧
        (∀ (A : Matrix (Fin n) (Fin q) ℝ), Hstar.transpose * A = 0 →
          Tendsto (fun j ↦ PartialReaction.rightReactionFrobeniusTV (μ j) A)
            atTop (𝓝 0)))) := by
  refine ⟨minimumValue_tendsto_of_eventually_relative_grams
    P L Lstar hL H Hstar hH α hα hconditions,
    minimumValue_attainment P Lstar Hstar, ?_⟩
  intro μ hg η hη hnear
  refine ⟨nearMinimizer_energy_tendsto
    P L Lstar hL H Hstar hH α hα hconditions μ hg η hη hnear, ?_⟩
  intro hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨ν, φ, hφ, hw, hν, heq⟩ := nearMinimizer_subsequence
      P L Lstar hL H Hstar hH α hα hconditions hb μ hg η hη hnear
    refine ⟨ν, φ, hφ, hw, hν, heq, ?_⟩
    intro B hB
    exact MatrixPositivity.massMeasureValue_posSemidef Lstar Hstar ν hν.1
      (by rw [heq]; exact hb) B hB
  · intro φ hφ ν hw
    have hc := nearMinimizer_cluster
      P L Lstar hL H Hstar hH α hα hconditions μ hg η hη hnear φ hφ ν hw
    refine ⟨hc.1, hc.2, ?_⟩
    intro B hB
    exact MatrixPositivity.massMeasureValue_posSemidef Lstar Hstar ν hc.1.1
      (by rw [hc.2]; exact hb) B hB
  · intro A hA
    exact nearMinimizer_rightFluxFrobeniusTV_tendsto_zero
      P L Lstar hL H Hstar hH α hα hconditions hb μ hg η hη hnear A hA
  · intro A hA
    exact nearMinimizer_rightReactionFrobeniusTV_tendsto_zero
      P L Lstar hL H Hstar hH α hα hconditions hb μ hg η hη hnear A hA

#print axioms nearMinimizer_rightFluxFrobeniusTV_tendsto_zero
#print axioms nearMinimizer_rightReactionFrobeniusTV_tendsto_zero
#print axioms partial_weights_regime

end MatrixTransport.PartialWeights
