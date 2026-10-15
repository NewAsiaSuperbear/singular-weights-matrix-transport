import MatrixTransport.PartialReaction.LimitTheorem
import MatrixTransport.PartialReaction.WeightScaling

/-!
# The relative-Gram partial reaction limit

The comparison constant may vary and converge to one.  This includes active eigenvalues
approaching their limits from either side in a fixed eigenbasis.  Arbitrary rotations are not
asserted to satisfy the comparison.
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

/-- The original minimum values converge under relative Gram domination tending to equality.
This includes the infinite target case and derives all compactness and recovery ingredients. -/
theorem minimumValue_tendsto_of_relative_gram (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hαpos : ∀ j, 0 < α j) (hαle : ∀ j, α j ≤ 1)
    (hα : Tendsto α atTop (𝓝 1))
    (hGram : ∀ j, (gram (H j) - α j • gram Hstar).PosSemidef) :
    Tendsto (fun j ↦ minimumValue P L (H j)) atTop (𝓝 (minimumValue P L Hstar)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c, hac, hcb⟩ := exists_between ha
    exact (eventually_le_constrainedInfimum (Good P) (Good P) (fun j ↦ action L (H j))
      (action L Hstar) (bounded_sequence_certificate P L H Hstar hH) hcb).mono
      fun j hj ↦ hac.trans_le hj
  · intro c hc
    have hb : minimumValue P L Hstar ≠ ⊤ := ne_of_lt (hc.trans_le le_top)
    obtain ⟨ν, hg, heq, _⟩ := minimumValue_attainment P L Hstar hb
    have hinv : Tendsto (fun j ↦ (1 : ℝ) / α j) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).div hα (by norm_num : (1 : ℝ) ≠ 0)
      change Tendsto (fun j ↦ (1 : ℝ) / α j) atTop (𝓝 ((1 : ℝ) / 1)) at h
      simpa only [one_div_one] using h
    have hfactor : Tendsto (fun j ↦ ENNReal.ofReal ((1 : ℝ) / α j)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, ENNReal.ofReal_one] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hinv
    have hupper : Tendsto
        (fun j ↦ ENNReal.ofReal ((1 : ℝ) / α j) * minimumValue P L Hstar)
        atTop (𝓝 (minimumValue P L Hstar)) := by
      simpa only [one_mul] using ENNReal.Tendsto.mul_const hfactor (Or.inr hb)
    filter_upwards [hupper.eventually (gt_mem_nhds hc)] with j hj
    have hmin : minimumValue P L (H j) ≤ action L (H j) ν :=
      iInf_le_of_le ν (iInf_le_of_le hg le_rfl)
    have hrec := action_le_inv_mul_of_relative_gram L (H j) Hstar
      (α j) (hαpos j) (hαle j) (hGram j) ν
    rw [heq] at hrec
    exact (hmin.trans hrec).trans_lt hj

/-- Finite prefixes of the relative comparison can be discarded. -/
theorem minimumValue_tendsto_of_eventually_relative_gram (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧ α j ≤ 1 ∧
      (gram (H j) - α j • gram Hstar).PosSemidef) :
    Tendsto (fun j ↦ minimumValue P L (H j)) atTop (𝓝 (minimumValue P L Hstar)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hconditions
  let σ : ℕ → ℕ := fun j ↦ j + N
  have hσ : StrictMono σ := fun a b hab ↦ Nat.add_lt_add_right hab N
  have hs (j : ℕ) := hN (σ j) (by dsimp [σ]; omega)
  have ht := minimumValue_tendsto_of_relative_gram P L (fun j ↦ H (σ j)) Hstar
    (hH.comp hσ.tendsto_atTop) (fun j ↦ α (σ j))
    (fun j ↦ (hs j).1) (fun j ↦ (hs j).2.1) (hα.comp hσ.tendsto_atTop)
    (fun j ↦ (hs j).2.2)
  exact (tendsto_add_atTop_iff_nat N).1 ht

/-- Actual vanishing-gap near-minimizer actions converge to the original singular target value. -/
theorem nearMinimizer_energy_tendsto (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧ α j ≤ 1 ∧
      (gram (H j) - α j • gram Hstar).PosSemidef)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (η : ℕ → ℝ≥0∞) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + η j) :
    Tendsto (fun j ↦ action L (H j) (μ j)) atTop (𝓝 (minimumValue P L Hstar)) := by
  have hv := minimumValue_tendsto_of_eventually_relative_gram P L H Hstar hH α hα hconditions
  have hupper : Tendsto (fun j ↦ minimumValue P L (H j) + η j)
      atTop (𝓝 (minimumValue P L Hstar)) := by simpa only [add_zero] using hv.add hη
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hv hupper
  · intro j
    exact iInf_le_of_le (μ j) (iInf_le_of_le (hg j) le_rfl)
  · exact hnear

/-- Every existing weak-star cluster of finite-target near-minimizers is genuinely optimal. -/
theorem nearMinimizer_cluster (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧ α j ≤ 1 ∧
      (gram (H j) - α j • gram Hstar).PosSemidef)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (η : ℕ → ℝ≥0∞) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + η j)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (ν : Path Ω n k)
    (hw : SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν) :
    Good P ν ∧ action L Hstar ν = minimumValue P L Hstar := by
  exact optimal_cluster_of_energy_tendsto P L H Hstar hH μ hg
    (nearMinimizer_energy_tendsto P L H Hstar hH α hα hconditions μ hg η hη hnear) φ hφ ν hw

/-- Finite-target near-minimizers have a common original Radon minimizing subsequence. -/
theorem nearMinimizer_subsequence (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧ α j ≤ 1 ∧
      (gram (H j) - α j • gram Hstar).PosSemidef)
    (hb : minimumValue P L Hstar ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hg : ∀ j, Good P (μ j)) (η : ℕ → ℝ≥0∞) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ j, action L (H j) (μ j) ≤ minimumValue P L (H j) + η j) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν ∧
      action L Hstar ν = minimumValue P L Hstar := by
  exact optimal_subsequence_of_energy_tendsto P L H Hstar hH hb μ hg
    (nearMinimizer_energy_tendsto P L H Hstar hH α hα hconditions μ hg η hη hnear)

#print axioms minimumValue_tendsto_of_eventually_relative_gram
#print axioms nearMinimizer_subsequence

end MatrixTransport.PartialReaction
