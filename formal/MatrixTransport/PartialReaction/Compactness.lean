import MatrixTransport.ReactionZero.LimitTheorem

/-!
# Compactness and attainment with bounded, possibly singular reaction weights

The original closed-domain continuity equation and actual signed Radon paths are retained.
Only an explicit upper bound on the reaction weights is needed for compactness.  In particular,
this file does not assume a positive lower eigenvalue or the vanishing of the whole weight.
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

/-- Matrix convergence gives an explicit finite bound on all squared Frobenius weights. -/
theorem exists_frobeniusSq_bound
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j, frobeniusSq (H j) ≤ K := by
  have ht := continuous_frobeniusSq.continuousAt.tendsto.comp hH
  have hd : Tendsto (fun j ↦ |frobeniusSq (H j) - frobeniusSq Hstar|)
      atTop (𝓝 0) := by
    simpa using (ht.sub (tendsto_const_nhds (x := frobeniusSq Hstar))).abs
  obtain ⟨B, hB, hb⟩ := exists_nonneg_bound_of_tendsto_zero
    (fun j ↦ |frobeniusSq (H j) - frobeniusSq Hstar|) (fun _ ↦ abs_nonneg _) hd
  refine ⟨B + frobeniusSq Hstar, add_nonneg hB (frobeniusSq_nonneg _), ?_⟩
  intro j
  have hj := (le_abs_self (frobeniusSq (H j) - frobeniusSq Hstar)).trans (hb j)
  linarith

/-- Bounded actions and bounded weights give a common genuine signed weak-star subsequence.
Admissibility is derived from the full C¹ equation and symmetry closure. -/
theorem sublevel_subsequence (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (K : ℝ) (hHK : ∀ j, frobeniusSq (H j) ≤ K)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hgood : ∀ j, Good P (μ j)) (hE : ∀ j, action L (H j) (μ j) ≤ C) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν := by
  let m0 := ClosedDomain.endpointMass P.initial
  have hm0 : 0 ≤ m0 := ClosedDomain.endpointMass_nonneg _ P.initial_positive
  have hwM : Measurable (ClosedDomain.timeWeight : ClosedDomain.Q Ω → ℝ) :=
    ClosedDomain.timeWeight.continuous.measurable
  have hw : ∀ x : ClosedDomain.Q Ω, 0 ≤ ClosedDomain.timeWeight x ∧
      ClosedDomain.timeWeight x ≤ 1 :=
    fun x ↦ ⟨ClosedDomain.timeWeight_nonneg x, ClosedDomain.timeWeight_le_one x⟩
  have hEof : ∀ j, action L (H j) (μ j) ≤ ENNReal.ofReal C.toReal := by
    intro j
    simpa only [ENNReal.ofReal_toReal hC] using hE j
  let B := Real.toNNReal (PathCoercivity.coordinateTVBound C.toReal
    (2 * m0 + 2 * K * C.toReal) (frobeniusSq L) K)
  have hTV : ∀ j c, ((μ j c).totalVariation univ) ≤ (B : ℝ≥0∞) := by
    intro j c
    exact PathCoercivity.coordinateTV_le_on_sublevel L (H j) (μ j) (hgood j).1
      C.toReal K ENNReal.toReal_nonneg (hEof j) (hHK j)
      ClosedDomain.timeWeight hwM hw m0 hm0 (time_identity P (μ j) (hgood j)) c
  obtain ⟨ν, φ, hφ, hweak⟩ := signedMeasureFamily_subsequence B μ hTV
  have hνgood : Good P ν :=
    ⟨massSymmetric_of_signedWeakStar _ _ hweak (fun j ↦ (hgood (φ j)).1),
      ClosedDomain.paperContinuityEquation_of_signedWeakStar P.operator P.initial P.terminal
        _ ν hweak (fun j ↦ (hgood (φ j)).2)⟩
  exact ⟨ν, φ, hφ, hweak, hνgood⟩

/-- Discarding a finite prefix preserves bounded-action compactness and the original CE. -/
theorem eventually_sublevel_subsequence (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (K : ℝ) (hHK : ∀ j, frobeniusSq (H j) ≤ K)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hgood : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, action L (H j) (μ j) ≤ C) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hE
  let σ : ℕ → ℕ := fun j ↦ j + N
  have hσ : StrictMono σ := fun a b hab ↦ Nat.add_lt_add_right hab N
  obtain ⟨ν, φ, hφ, hw, hg⟩ := sublevel_subsequence P L (fun j ↦ H (σ j)) K
    (fun j ↦ hHK (σ j)) C hC (fun j ↦ μ (σ j)) (fun j ↦ hgood (σ j))
    (fun j ↦ hN (σ j) (by dsimp [σ]; omega))
  exact ⟨ν, σ ∘ φ, hσ.comp hφ, hw, hg⟩

/-- Every finite original minimum with any fixed weight is attained, including singular weights.
No attainment, compactness, PSD mass, or lower-semicontinuity premise is assumed. -/
theorem minimumValue_attainment (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hb : minimumValue P L Hstar ≠ ⊤) :
    ∃ ν : Path Ω n k, Good P ν ∧ action L Hstar ν = minimumValue P L Hstar ∧
      ∀ B, MeasurableSet B → (MatrixPositivity.massMeasureValue ν B).PosSemidef := by
  obtain ⟨μ, hg, ht⟩ := minimizing_sequence (Good P) (action L Hstar) hb
  obtain ⟨C, hbC, hCtop⟩ := exists_between (lt_top_iff_ne_top.mpr hb)
  have hbound : ∀ᶠ j in atTop, action L Hstar (μ j) ≤ C :=
    (ht.eventually (gt_mem_nhds hbC)).mono fun _ h ↦ h.le
  obtain ⟨ν, φ, hφ, hw, hν⟩ := eventually_sublevel_subsequence P L (fun _ ↦ Hstar)
    (frobeniusSq Hstar) (fun _ ↦ le_rfl) C hCtop.ne μ hg hbound
  have he := WeightedSet.action_le_liminf L Hstar _ ν hw
  have hlim : atTop.liminf (fun j ↦ action L Hstar (μ (φ j))) = minimumValue P L Hstar := by
    simpa only [Function.comp_def, minimumValue] using (ht.comp hφ.tendsto_atTop).liminf_eq
  rw [hlim] at he
  have heq : action L Hstar ν = minimumValue P L Hstar :=
    le_antisymm he (iInf_le_of_le ν (iInf_le_of_le hν le_rfl))
  refine ⟨ν, hν, heq, ?_⟩
  intro B hB
  exact MatrixPositivity.massMeasureValue_posSemidef L Hstar ν hν.1
    (by rw [heq]; exact hb) B hB

#print axioms minimumValue_attainment

end MatrixTransport.PartialReaction
