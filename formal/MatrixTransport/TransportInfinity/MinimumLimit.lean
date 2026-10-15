import MatrixTransport.ReactionZero.MinimumLimit

/-!
# A value limit from finite-domain preservation and pointwise recovery

The limit is restricted to paths with finite baseline action.  It is not replaced by an
unrestricted free-flux action whose range compatibility might be different.  No compactness,
attainment or lower-semicontinuity certificate is needed for this value argument.
-/

set_option autoImplicit false

open Filter Topology Set
open scoped ENNReal

namespace MatrixTransport.TransportInfinity

open MatrixTransport.ReactionZero

variable {U : Type*}

/-- The admissible paths with genuinely finite baseline action. -/
def finiteBaseline (good : U → Prop) (baseline : U → ℝ≥0∞) (u : U) : Prop :=
  good u ∧ baseline u ≠ ⊤

/-- Preserving the actual finite-action domain and recovering each finite path proves
extended minimum convergence.  These algebraic premises are instantiated by the original
weighted action in the final transport-infinity theorem. -/
theorem constrainedInfimum_tendsto_of_finite_domain
    (good : U → Prop) (baseline limitEnergy : U → ℝ≥0∞) (energy : ℕ → U → ℝ≥0∞)
    (hfinite : ∀ᶠ j in atTop, ∀ u, good u → (energy j u ≠ ⊤ ↔ baseline u ≠ ⊤))
    (hlower : ∀ᶠ j in atTop, ∀ u, good u → baseline u ≠ ⊤ → limitEnergy u ≤ energy j u)
    (hrecovery : ∀ u, good u → baseline u ≠ ⊤ →
      Tendsto (fun j ↦ energy j u) atTop (𝓝 (limitEnergy u))) :
    Tendsto (fun j ↦ constrainedInfimum good (energy j)) atTop
      (𝓝 (constrainedInfimum (finiteBaseline good baseline) limitEnergy)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hfinite, hlower] with j hj hlow
    have hbound : constrainedInfimum (finiteBaseline good baseline) limitEnergy ≤
        constrainedInfimum good (energy j) := by
      unfold constrainedInfimum
      refine le_iInf fun u ↦ le_iInf fun hu ↦ ?_
      by_cases he : energy j u = ⊤
      · rw [he]
        exact le_top
      · have hb := (hj u hu).1 he
        exact (iInf_le_of_le u (iInf_le_of_le (show finiteBaseline good baseline u from ⟨hu, hb⟩)
          le_rfl)).trans (hlow u hu hb)
    exact ha.trans_le hbound
  · intro c hc
    have hchoose := hc
    simp only [constrainedInfimum, iInf_lt_iff] at hchoose
    obtain ⟨u, hu, huc⟩ := hchoose
    have ht := hrecovery u hu.1 hu.2
    filter_upwards [ht.eventually (gt_mem_nhds huc)] with j hj
    exact (iInf_le_of_le u (iInf_le_of_le hu.1 le_rfl)).trans_lt hj

#print axioms constrainedInfimum_tendsto_of_finite_domain

end MatrixTransport.TransportInfinity
