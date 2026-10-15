import MatrixTransport.PartialReaction.RelativeLimit
import MatrixTransport.PartialReaction.KernelExtinction

/-!
# Complete certificate for a relative-Gram partial reaction degeneration

The final statement retains the original problem and its genuine signed Radon paths.
The limiting weight may be nonzero and singular.  The explicit relative Gram comparison
supplies recovery; it is not asserted to be necessary for arbitrary endpoint data.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialReaction

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {n k d p : ℕ} {Ω : Set (ClosedDomain.Space d)}
variable [Fact (IsCompact Ω)]

/-- Finite-target near-minimizers lose all reaction in fixed target-kernel directions along
the entire sequence, with the actual Frobenius norm integral as variation. -/
theorem nearMinimizer_rightReactionFrobeniusTV_tendsto_zero (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧ α j ≤ 1 ∧
      (gram (H j) - α j • gram Hstar).PosSemidef)
    (hb : minimumValue P L Hstar ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hg : ∀ j, Good P (μ j)) (η : ℕ → ℝ≥0∞) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + η j)
    (A : Matrix (Fin n) (Fin p) ℝ) (hA : Hstar.transpose * A = 0) :
    Tendsto (fun j ↦ rightReactionFrobeniusTV (μ j) A) atTop (𝓝 0) := by
  have ht := nearMinimizer_energy_tendsto P L H Hstar hH α hα hconditions μ hg η hη hnear
  obtain ⟨C, hbC, hCtop⟩ := exists_between (lt_top_iff_ne_top.mpr hb)
  have hbound : ∀ᶠ j in atTop, action L (H j) (μ j) ≤ C :=
    (ht.eventually (gt_mem_nhds hbC)).mono fun _ h ↦ h.le
  exact rightReactionFrobeniusTV_tendsto_zero_of_eventually_bounded
    P L H Hstar hH C hCtop.ne μ hg hbound A hA

/-- Complete original-model partial-reaction regime under the stated relative Gram condition:
extended minimum convergence, finite PSD attainment, energy convergence, a common optimal
subsequence, every optimal weak-star cluster, and whole-sequence forbidden-reaction extinction.
Compactness, LSC, recovery and the RN/variation bridges are all proved dependencies. -/
theorem partial_reaction_regime (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧ α j ≤ 1 ∧
      (gram (H j) - α j • gram Hstar).PosSemidef) :
    Tendsto (fun j ↦ minimumValue P L (H j)) atTop (𝓝 (minimumValue P L Hstar)) ∧
    (minimumValue P L Hstar ≠ ⊤ →
      ∃ ν : Path Ω n k, Good P ν ∧ action L Hstar ν = minimumValue P L Hstar ∧
        ∀ B, MeasurableSet B → (MatrixPositivity.massMeasureValue ν B).PosSemidef) ∧
    (∀ (μ : ℕ → Path Ω n k), (∀ j, Good P (μ j)) →
      ∀ (η : ℕ → ℝ≥0∞), Tendsto η atTop (𝓝 0) →
      (∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + η j) →
      Tendsto (fun j ↦ action L (H j) (μ j)) atTop (𝓝 (minimumValue P L Hstar)) ∧
      (minimumValue P L Hstar ≠ ⊤ →
        (∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
          SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν ∧
          action L Hstar ν = minimumValue P L Hstar) ∧
        (∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (ν : Path Ω n k),
          SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν →
          Good P ν ∧ action L Hstar ν = minimumValue P L Hstar) ∧
        (∀ (A : Matrix (Fin n) (Fin p) ℝ), Hstar.transpose * A = 0 →
          Tendsto (fun j ↦ rightReactionFrobeniusTV (μ j) A) atTop (𝓝 0)))) := by
  refine ⟨minimumValue_tendsto_of_eventually_relative_gram P L H Hstar hH α hα hconditions,
    minimumValue_attainment P L Hstar, ?_⟩
  intro μ hg η hη hnear
  refine ⟨nearMinimizer_energy_tendsto P L H Hstar hH α hα hconditions μ hg η hη hnear, ?_⟩
  intro hb
  refine ⟨nearMinimizer_subsequence P L H Hstar hH α hα hconditions hb μ hg η hη hnear,
    ?_, ?_⟩
  · intro φ hφ ν hw
    exact nearMinimizer_cluster P L H Hstar hH α hα hconditions μ hg η hη hnear φ hφ ν hw
  · intro A hA
    exact nearMinimizer_rightReactionFrobeniusTV_tendsto_zero
      P L H Hstar hH α hα hconditions hb μ hg η hη hnear A hA

#print axioms partial_reaction_regime

end MatrixTransport.PartialReaction
