import MatrixTransport.ReactionZero.LimitTheorem
import Mathlib.Topology.Order.LiminfLimsup

/-! Independent liminf and varying-infimum choices used in the lower-bound proof. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set
open scoped ENNReal

namespace LiZouTransport.InfimumProofBridges
open MatrixTransport.ReactionZero

/-- A genuine strictly increasing subsequence realizes the extended-real liminf. -/
theorem exists_strictMono_liminf (v : ℕ → ℝ≥0∞) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j ↦ v (φ j)) atTop (𝓝 (atTop.liminf v)) := by
  obtain ⟨x, hx, hxt⟩ := exists_seq_tendsto_liminf (u := v) (f := atTop)
  obtain ⟨ψ, hψ, hxψ⟩ := strictMono_subseq_of_tendsto_atTop hxt
  exact ⟨x ∘ ψ, hxψ, hx.comp hψ.tendsto_atTop⟩

/-- At a finite liminf, a strictly increasing realizing subsequence has only finite values. -/
theorem exists_strictMono_finite_liminf (v : ℕ → ℝ≥0∞) (hf : atTop.liminf v ≠ ⊤) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ j, v (φ j) ≠ ⊤) ∧
      Tendsto (fun j ↦ v (φ j)) atTop (𝓝 (atTop.liminf v)) := by
  obtain ⟨φ, hφ, ht⟩ := exists_strictMono_liminf v
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually
    (gt_mem_nhds (lt_top_iff_ne_top.mpr hf)))
  refine ⟨fun j ↦ φ (j + N), fun i j hij ↦ hφ (Nat.add_lt_add_right hij N),
    fun j ↦ ne_of_lt (hN (j + N) (Nat.le_add_left N j)), ?_⟩
  exact ht.comp (tendsto_add_atTop_nat N)

/-- Infimum approximation with an actual admissible witness and a positive real error. -/
theorem exists_approximate_minimizer {X : Type*} (good : X → Prop) (energy : X → ℝ≥0∞)
    (hf : constrainedInfimum good energy ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : X, good x ∧ energy x ≤ constrainedInfimum good energy + ENNReal.ofReal δ := by
  have ht : constrainedInfimum good energy <
      constrainedInfimum good energy + ENNReal.ofReal δ :=
    ENNReal.lt_add_right hf (ENNReal.ofReal_pos.mpr hδ).ne'
  simp only [constrainedInfimum, iInf_lt_iff] at ht
  obtain ⟨x, hx, he⟩ := ht
  exact ⟨x, hx, he.le⟩

/-- Diagonal approximate minimizers for varying functionals, without a value-limit theorem. -/
theorem varying_approximate_minimizers {X : Type*} (good : ℕ → X → Prop)
    (energy : ℕ → X → ℝ≥0∞) {ℓ : ℝ≥0∞}
    (hf : ∀ j, constrainedInfimum (good j) (energy j) ≠ ⊤)
    (hv : Tendsto (fun j ↦ constrainedInfimum (good j) (energy j)) atTop (𝓝 ℓ)) :
    ∃ u : ℕ → X, (∀ j, good j (u j)) ∧
      (∀ j, energy j (u j) ≤ constrainedInfimum (good j) (energy j) +
        ENNReal.ofReal (1 / ((j : ℝ) + 1))) ∧
      Tendsto (fun j ↦ energy j (u j)) atTop (𝓝 ℓ) := by
  have hex : ∀ j : ℕ, ∃ x : X, good j x ∧
      energy j x ≤ constrainedInfimum (good j) (energy j) +
        ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    exact exists_approximate_minimizer (good j) (energy j) (hf j) (by positivity)
  choose u hu he using hex
  refine ⟨u, hu, he, ?_⟩
  have hδ : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (1 / ((j : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hup : Tendsto (fun j ↦ constrainedInfimum (good j) (energy j) +
      ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 ℓ) := by
    simpa only [add_zero] using hv.add hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hv hup
  · intro j
    unfold constrainedInfimum
    exact iInf_le_of_le (u j) (iInf_le_of_le (hu j) le_rfl)
  · exact he

/-- A finite limit gives a finite uniform bound on a tail of the chosen energies. -/
theorem varying_approximate_minimizers_bounded_tail {X : Type*}
    (good : ℕ → X → Prop) (energy : ℕ → X → ℝ≥0∞) {ℓ : ℝ≥0∞} (hℓ : ℓ ≠ ⊤)
    (hf : ∀ j, constrainedInfimum (good j) (energy j) ≠ ⊤)
    (hv : Tendsto (fun j ↦ constrainedInfimum (good j) (energy j)) atTop (𝓝 ℓ)) :
    ∃ u : ℕ → X, (∀ j, good j (u j)) ∧
      Tendsto (fun j ↦ energy j (u j)) atTop (𝓝 ℓ) ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ j in atTop, energy j (u j) ≤ C := by
  obtain ⟨u, hu, _, ht⟩ := varying_approximate_minimizers good energy hf hv
  refine ⟨u, hu, ht, ℓ + 1, ENNReal.add_ne_top.mpr ⟨hℓ, by norm_num⟩, ?_⟩
  have hlt : ℓ < ℓ + 1 := ENNReal.lt_add_right hℓ (by norm_num)
  exact (ht.eventually (gt_mem_nhds hlt)).mono fun _ hj ↦ hj.le

end LiZouTransport.InfimumProofBridges

#print axioms LiZouTransport.InfimumProofBridges.exists_strictMono_liminf
#print axioms LiZouTransport.InfimumProofBridges.exists_strictMono_finite_liminf
#print axioms LiZouTransport.InfimumProofBridges.exists_approximate_minimizer
#print axioms LiZouTransport.InfimumProofBridges.varying_approximate_minimizers
#print axioms LiZouTransport.InfimumProofBridges.varying_approximate_minimizers_bounded_tail
