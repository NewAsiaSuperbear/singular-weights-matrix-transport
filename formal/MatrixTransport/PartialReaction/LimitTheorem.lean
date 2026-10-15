import MatrixTransport.PartialReaction.Compactness
import MatrixTransport.PartialReaction.JointLowerSemicontinuity

/-!
# Partial reaction degeneration for the original Radon problem

The new varying-weight lower bound is combined with the original coercivity, closed-domain C¹
continuity equation and signed-measure compactness.  The limiting action remains the original
action at the limiting weight: surviving reaction directions are retained.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialReaction

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {n k d : ℕ} {Ω : Set (ClosedDomain.Space d)}
variable [Fact (IsCompact Ω)]

/-- A bounded varying-weight sublevel has an admissible limit in the limiting sublevel.
The compactness and lower bound are derived for actual signed measures. -/
theorem bounded_subsequence (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (hE : ∀ j, action L (H j) (μ j) ≤ C) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν ∧ action L Hstar ν ≤ C := by
  obtain ⟨K, _, hHK⟩ := exists_frobeniusSq_bound H Hstar hH
  obtain ⟨ν, φ, hφ, hw, hν⟩ := sublevel_subsequence P L H K hHK C hC μ hg hE
  have he := action_le_varying_weight_liminf L (fun j ↦ H (φ j)) Hstar
    (hH.comp hφ.tendsto_atTop) _ ν hw
  have hb : atTop.liminf (fun j ↦ action L (H (φ j)) (μ (φ j))) ≤ C :=
    liminf_le_of_frequently_le' (Filter.Eventually.of_forall (fun j ↦ hE (φ j))).frequently
  exact ⟨ν, φ, hφ, hw, hν, he.trans hb⟩

/-- The extended-infimum certificate is proved using the original paths, not assumed. -/
theorem bounded_sequence_certificate (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (hE : ∀ j, action L (H (φ j)) (μ j) ≤ C) :
    ∃ ν, Good P ν ∧ action L Hstar ν ≤ C := by
  obtain ⟨ν, _, _, _, hν, he⟩ := bounded_subsequence P L (fun j ↦ H (φ j))
    Hstar (hH.comp hφ.tendsto_atTop) C hC μ hg hE
  exact ⟨ν, hν, he⟩

/-- Minimum continuity under Gram domination of the limiting weight.
The conclusion includes infinite target values; no endpoint compatibility is assumed. -/
theorem minimumValue_tendsto_of_gram_domination (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (hGram : ∀ j, (gram (H j) - gram Hstar).PosSemidef) :
    Tendsto (fun j ↦ minimumValue P L (H j)) atTop (𝓝 (minimumValue P L Hstar)) := by
  exact constrainedInfimum_tendsto (Good P) (Good P) (fun j ↦ action L (H j))
    (action L Hstar) (fun _ h ↦ h)
    (fun j μ _ ↦ action_mono_reaction L (hGram j) μ)
    (bounded_sequence_certificate P L H Hstar hH)

/-- A convergent action sequence has an optimal admissible weak-star cluster when its action
limit is the target infimum.  Joint LSC is proved, not a premise. -/
theorem optimal_cluster_of_energy_tendsto (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (henergy : Tendsto (fun j ↦ action L (H j) (μ j)) atTop (𝓝 (minimumValue P L Hstar)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (ν : Path Ω n k)
    (hw : SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν) :
    Good P ν ∧ action L Hstar ν = minimumValue P L Hstar := by
  have hν : Good P ν :=
    ⟨massSymmetric_of_signedWeakStar _ _ hw (fun j ↦ (hg (φ j)).1),
      ClosedDomain.paperContinuityEquation_of_signedWeakStar P.operator P.initial P.terminal
        _ ν hw (fun j ↦ (hg (φ j)).2)⟩
  have he := action_le_varying_weight_liminf L (fun j ↦ H (φ j)) Hstar
    (hH.comp hφ.tendsto_atTop) _ ν hw
  have hlim : atTop.liminf (fun j ↦ action L (H (φ j)) (μ (φ j))) =
      minimumValue P L Hstar := by
    simpa only [Function.comp_def] using (henergy.comp hφ.tendsto_atTop).liminf_eq
  rw [hlim] at he
  exact ⟨hν, le_antisymm he (iInf_le_of_le ν (iInf_le_of_le hν le_rfl))⟩

/-- Finite target-energy convergence implies a common original Radon minimizing subsequence. -/
theorem optimal_subsequence_of_energy_tendsto (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (hb : minimumValue P L Hstar ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hg : ∀ j, Good P (μ j))
    (henergy : Tendsto (fun j ↦ action L (H j) (μ j)) atTop (𝓝 (minimumValue P L Hstar))) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν ∧
      action L Hstar ν = minimumValue P L Hstar := by
  obtain ⟨C, hbC, hCtop⟩ := exists_between (lt_top_iff_ne_top.mpr hb)
  have hbound : ∀ᶠ j in atTop, action L (H j) (μ j) ≤ C :=
    (henergy.eventually (gt_mem_nhds hbC)).mono fun _ h ↦ h.le
  obtain ⟨K, _, hHK⟩ := exists_frobeniusSq_bound H Hstar hH
  obtain ⟨ν, φ, hφ, hw, _⟩ := eventually_sublevel_subsequence P L H K hHK C hCtop.ne μ hg hbound
  have hc := optimal_cluster_of_energy_tendsto P L H Hstar hH μ hg henergy φ hφ ν hw
  exact ⟨ν, φ, hφ, hw, hc.1, hc.2⟩

#print axioms minimumValue_tendsto_of_gram_domination
#print axioms optimal_subsequence_of_energy_tendsto

end MatrixTransport.PartialReaction
