import MatrixTransport.PartialWeights.Compactness
import MatrixTransport.PartialWeights.WeightComparison

/-!
# Minimum-value and minimizing-path stability with both weights varying

The original signed Radon path problem is retained. Both weights may be singular. The
actual joint lower bound, actual original-equation compactness and the proved two-Gram
comparison give extended minimum convergence and optimal weak-star subsequences.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialWeights

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {n k d : ℕ} {Ω : Set (ClosedDomain.Space d)}
variable [Fact (IsCompact Ω)]

/-- Extended original minimum continuity under positive relative domination of both Grams. -/
theorem minimumValue_tendsto_of_relative_grams (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hαpos : ∀ j, 0 < α j) (hα : Tendsto α atTop (𝓝 1))
    (hGL : ∀ j, (gram (L j) - α j • gram Lstar).PosSemidef)
    (hGH : ∀ j, (gram (H j) - α j • gram Hstar).PosSemidef) :
    Tendsto (fun j ↦ minimumValue P (L j) (H j)) atTop
      (𝓝 (minimumValue P Lstar Hstar)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c, hac, hcb⟩ := exists_between ha
    exact (eventually_le_constrainedInfimum (Good P) (Good P)
      (fun j ↦ action (L j) (H j)) (action Lstar Hstar)
      (bounded_sequence_certificate P L Lstar hL H Hstar hH) hcb).mono
      fun j hj ↦ hac.trans_le hj
  · intro c hc
    have hb : minimumValue P Lstar Hstar ≠ ⊤ := ne_of_lt (hc.trans_le le_top)
    obtain ⟨ν, hg, heq, _⟩ := minimumValue_attainment P Lstar Hstar hb
    have hinv : Tendsto (fun j ↦ (1 : ℝ) / α j) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).div hα (by norm_num : (1 : ℝ) ≠ 0)
      change Tendsto (fun j ↦ (1 : ℝ) / α j) atTop (𝓝 ((1 : ℝ) / 1)) at h
      simpa only [one_div_one] using h
    have hfactor : Tendsto (fun j ↦ ENNReal.ofReal ((1 : ℝ) / α j)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, ENNReal.ofReal_one] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hinv
    have hupper : Tendsto
        (fun j ↦ ENNReal.ofReal ((1 : ℝ) / α j) * minimumValue P Lstar Hstar)
        atTop (𝓝 (minimumValue P Lstar Hstar)) := by
      simpa only [one_mul] using ENNReal.Tendsto.mul_const hfactor (Or.inr hb)
    filter_upwards [hupper.eventually (gt_mem_nhds hc)] with j hj
    have hmin : minimumValue P (L j) (H j) ≤ action (L j) (H j) ν :=
      iInf_le_of_le ν (iInf_le_of_le hg le_rfl)
    have hrec := action_le_inv_mul_of_relative_grams
      (L j) Lstar (H j) Hstar (α j) (hαpos j) (hGL j) (hGH j) ν
    rw [heq] at hrec
    exact (hmin.trans hrec).trans_lt hj

/-- A finite prefix of exceptions to relative domination may be discarded. -/
theorem minimumValue_tendsto_of_eventually_relative_grams (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧
      (gram (L j) - α j • gram Lstar).PosSemidef ∧
      (gram (H j) - α j • gram Hstar).PosSemidef) :
    Tendsto (fun j ↦ minimumValue P (L j) (H j)) atTop
      (𝓝 (minimumValue P Lstar Hstar)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hconditions
  let σ : ℕ → ℕ := fun j ↦ j + N
  have hσ : StrictMono σ := fun a b hab ↦ Nat.add_lt_add_right hab N
  have hs (j : ℕ) := hN (σ j) (by dsimp [σ]; omega)
  have ht := minimumValue_tendsto_of_relative_grams P (fun j ↦ L (σ j)) Lstar
    (hL.comp hσ.tendsto_atTop) (fun j ↦ H (σ j)) Hstar
    (hH.comp hσ.tendsto_atTop) (fun j ↦ α (σ j))
    (fun j ↦ (hs j).1) (hα.comp hσ.tendsto_atTop)
    (fun j ↦ (hs j).2.1) (fun j ↦ (hs j).2.2)
  exact (tendsto_add_atTop_iff_nat N).1 ht

/-- Vanishing-gap original path actions converge, also when the target value is infinite. -/
theorem nearMinimizer_energy_tendsto (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧
      (gram (L j) - α j • gram Lstar).PosSemidef ∧
      (gram (H j) - α j • gram Hstar).PosSemidef)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (η : ℕ → ℝ≥0∞) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ j, action (L j) (H j) (μ j) ≤ minimumValue P (L j) (H j) + η j) :
    Tendsto (fun j ↦ action (L j) (H j) (μ j)) atTop
      (𝓝 (minimumValue P Lstar Hstar)) := by
  have hv := minimumValue_tendsto_of_eventually_relative_grams
    P L Lstar hL H Hstar hH α hα hconditions
  have hupper : Tendsto (fun j ↦ minimumValue P (L j) (H j) + η j)
      atTop (𝓝 (minimumValue P Lstar Hstar)) := by
    simpa only [add_zero] using hv.add hη
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hv hupper
  · intro j
    exact iInf_le_of_le (μ j) (iInf_le_of_le (hg j) le_rfl)
  · exact hnear

/-- Every existing weak-star cluster of target-energy paths is an original target minimizer. -/
theorem optimal_cluster_of_energy_tendsto (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (henergy : Tendsto (fun j ↦ action (L j) (H j) (μ j)) atTop
      (𝓝 (minimumValue P Lstar Hstar)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (ν : Path Ω n k)
    (hw : SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν) :
    Good P ν ∧ action Lstar Hstar ν = minimumValue P Lstar Hstar := by
  have hν : Good P ν :=
    ⟨massSymmetric_of_signedWeakStar _ _ hw (fun j ↦ (hg (φ j)).1),
      ClosedDomain.paperContinuityEquation_of_signedWeakStar P.operator P.initial P.terminal
        _ ν hw (fun j ↦ (hg (φ j)).2)⟩
  have he := action_le_varying_weights_liminf (fun j ↦ L (φ j)) Lstar
    (hL.comp hφ.tendsto_atTop) (fun j ↦ H (φ j)) Hstar
    (hH.comp hφ.tendsto_atTop) _ ν hw
  have hlim : atTop.liminf (fun j ↦ action (L (φ j)) (H (φ j)) (μ (φ j))) =
      minimumValue P Lstar Hstar := by
    simpa only [Function.comp_def] using (henergy.comp hφ.tendsto_atTop).liminf_eq
  rw [hlim] at he
  exact ⟨hν, le_antisymm he (iInf_le_of_le ν (iInf_le_of_le hν le_rfl))⟩

/-- Finite target-energy convergence gives a common actual original-path minimizing subsequence. -/
theorem optimal_subsequence_of_energy_tendsto (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar)) (hb : minimumValue P Lstar Hstar ≠ ⊤)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (henergy : Tendsto (fun j ↦ action (L j) (H j) (μ j)) atTop
      (𝓝 (minimumValue P Lstar Hstar))) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν ∧
      action Lstar Hstar ν = minimumValue P Lstar Hstar := by
  obtain ⟨C, hbC, hCtop⟩ := exists_between (lt_top_iff_ne_top.mpr hb)
  have hbound : ∀ᶠ j in atTop, action (L j) (H j) (μ j) ≤ C :=
    (henergy.eventually (gt_mem_nhds hbC)).mono fun _ h ↦ h.le
  obtain ⟨KL, _, hLK⟩ := PartialReaction.exists_frobeniusSq_bound L Lstar hL
  obtain ⟨KH, _, hHK⟩ := PartialReaction.exists_frobeniusSq_bound H Hstar hH
  obtain ⟨ν, φ, hφ, hw, _⟩ :=
    eventually_sublevel_subsequence P L H KL KH hLK hHK C hCtop.ne μ hg hbound
  have hc := optimal_cluster_of_energy_tendsto P L Lstar hL H Hstar hH
    μ hg henergy φ hφ ν hw
  exact ⟨ν, φ, hφ, hw, hc.1, hc.2⟩

/-- Every weak-star cluster of vanishing-gap paths is genuinely optimal. -/
theorem nearMinimizer_cluster (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 1))
    (hconditions : ∀ᶠ j in atTop, 0 < α j ∧
      (gram (L j) - α j • gram Lstar).PosSemidef ∧
      (gram (H j) - α j • gram Hstar).PosSemidef)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (η : ℕ → ℝ≥0∞) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ j, action (L j) (H j) (μ j) ≤ minimumValue P (L j) (H j) + η j)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (ν : Path Ω n k)
    (hw : SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν) :
    Good P ν ∧ action Lstar Hstar ν = minimumValue P Lstar Hstar := by
  exact optimal_cluster_of_energy_tendsto P L Lstar hL H Hstar hH μ hg
    (nearMinimizer_energy_tendsto P L Lstar hL H Hstar hH
      α hα hconditions μ hg η hη hnear) φ hφ ν hw

/-- Finite-target vanishing-gap paths have a common original Radon minimizing subsequence. -/
theorem nearMinimizer_subsequence (P : Problem Ω n k)
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
    (hnear : ∀ j, action (L j) (H j) (μ j) ≤ minimumValue P (L j) (H j) + η j) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν ∧
      action Lstar Hstar ν = minimumValue P Lstar Hstar := by
  exact optimal_subsequence_of_energy_tendsto P L Lstar hL H Hstar hH hb μ hg
    (nearMinimizer_energy_tendsto P L Lstar hL H Hstar hH
      α hα hconditions μ hg η hη hnear)

#print axioms minimumValue_tendsto_of_eventually_relative_grams
#print axioms nearMinimizer_energy_tendsto
#print axioms nearMinimizer_cluster
#print axioms nearMinimizer_subsequence

end MatrixTransport.PartialWeights
