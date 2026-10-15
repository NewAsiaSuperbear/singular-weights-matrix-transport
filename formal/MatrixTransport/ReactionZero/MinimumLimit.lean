import Mathlib

/-!
# Extended minimum-value bookkeeping

This is a generic final-combination lemma. Its bounded-sequence certificate must be proved
for the actual Radon action by the concrete coercivity, compactness and lower-semicontinuity
modules; assuming that certificate alone is not formal acceptance of the paper's problem.
The order argument includes infinite limiting values and needs no minimizer-attainment premise.
-/

set_option autoImplicit false

open Filter Topology
open scoped ENNReal

namespace MatrixTransport.ReactionZero

variable {P : Type*}

noncomputable def constrainedInfimum (admissible : P → Prop) (energy : P → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ p, ⨅ (_ : admissible p), energy p

/-- A recovery inequality supplies the upper bound on all minimum values. -/
theorem constrainedInfimum_le_balanced (good balanced : P → Prop)
    (energy : ℕ → P → ℝ≥0∞) (limitEnergy : P → ℝ≥0∞)
    (hgood : ∀ p, balanced p → good p)
    (hrecovery : ∀ j p, balanced p → energy j p ≤ limitEnergy p) (j : ℕ) :
    constrainedInfimum good (energy j) ≤ constrainedInfimum balanced limitEnergy := by
  unfold constrainedInfimum
  refine le_iInf fun p ↦ le_iInf fun hp ↦ ?_
  exact (iInf_le_of_le p (iInf_le_of_le (hgood p hp) le_rfl)).trans (hrecovery j p hp)

/-- Uniformly bounded low-energy subsequences cannot persist strictly below the balanced
infimum when the concrete path theory supplies the stated bounded-sequence certificate. -/
theorem eventually_le_constrainedInfimum (good balanced : P → Prop)
    (energy : ℕ → P → ℝ≥0∞) (limitEnergy : P → ℝ≥0∞)
    (hcertificate : ∀ (C : ℝ≥0∞), C ≠ ⊤ → ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (u : ℕ → P), (∀ j, good (u j)) → (∀ j, energy (φ j) (u j) ≤ C) →
        ∃ p, balanced p ∧ limitEnergy p ≤ C)
    {C : ℝ≥0∞} (hC : C < constrainedInfimum balanced limitEnergy) :
    ∀ᶠ j in atTop, C ≤ constrainedInfimum good (energy j) := by
  classical
  by_contra hnot
  have hfreq : ∃ᶠ j in atTop, constrainedInfimum good (energy j) < C := by
    simpa only [not_eventually, not_le] using hnot
  obtain ⟨φ, hφ, hlow⟩ := extraction_of_frequently_atTop hfreq
  have hchoose : ∀ j, ∃ p, good p ∧ energy (φ j) p < C := by
    intro j
    have hj := hlow j
    simp only [constrainedInfimum, iInf_lt_iff] at hj
    obtain ⟨p, hp, he⟩ := hj
    exact ⟨p, hp, he⟩
  choose u hu henergy using hchoose
  have hfinite : C ≠ ⊤ := ne_of_lt (hC.trans_le le_top)
  obtain ⟨p, hp, he⟩ := hcertificate C hfinite φ hφ u hu (fun j ↦ (henergy j).le)
  have hb : constrainedInfimum balanced limitEnergy ≤ limitEnergy p :=
    iInf_le_of_le p (iInf_le_of_le hp le_rfl)
  exact (not_le_of_gt hC) (hb.trans he)

/-- Minimum values converge in the extended nonnegative reals, including divergence to infinity.
No compatibility or finite balanced-cost assumption is introduced. -/
theorem constrainedInfimum_tendsto (good balanced : P → Prop)
    (energy : ℕ → P → ℝ≥0∞) (limitEnergy : P → ℝ≥0∞)
    (hgood : ∀ p, balanced p → good p)
    (hrecovery : ∀ j p, balanced p → energy j p ≤ limitEnergy p)
    (hcertificate : ∀ (C : ℝ≥0∞), C ≠ ⊤ → ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (u : ℕ → P), (∀ j, good (u j)) → (∀ j, energy (φ j) (u j) ≤ C) →
        ∃ p, balanced p ∧ limitEnergy p ≤ C) :
    Tendsto (fun j ↦ constrainedInfimum good (energy j)) atTop
      (𝓝 (constrainedInfimum balanced limitEnergy)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c, hac, hcb⟩ := exists_between ha
    exact (eventually_le_constrainedInfimum good balanced energy limitEnergy hcertificate hcb).mono
      fun j hj ↦ hac.trans_le hj
  · intro c hc
    exact Filter.Eventually.of_forall fun j ↦
      (constrainedInfimum_le_balanced good balanced energy limitEnergy hgood hrecovery j).trans_lt hc

#print axioms constrainedInfimum_tendsto

end MatrixTransport.ReactionZero
