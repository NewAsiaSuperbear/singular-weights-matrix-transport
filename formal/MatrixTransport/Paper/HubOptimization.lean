import MatrixTransport.TransportInfinity.LimitTheorem

/-!
# Scalar duration allocation for the three-piece hub recovery

Positive durations are obtained by adding `η/3` to each square root of a segment cost.
The construction also covers zero-cost segments. The approximation helpers below take
explicit cost bounds as premises; they do not assume or assert an unproved continuity equation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace LiZouTransport.HubScalar

/-- Positive duration allocation for one segment. -/
def duration (c S η : ℝ) : ℝ := (Real.sqrt c + η / 3) / (S + η)

theorem duration_pos {c S η : ℝ} (hS : 0 ≤ S) (hη : 0 < η) :
    0 < duration c S η := by
  unfold duration
  exact div_pos (by positivity) (by positivity)

theorem duration_cost_le {c S η : ℝ} (hc : 0 ≤ c) (hS : 0 ≤ S) (hη : 0 < η) :
    c / duration c S η ≤ Real.sqrt c * (S + η) := by
  have hd : 0 < Real.sqrt c + η / 3 := by positivity
  unfold duration
  rw [div_div_eq_mul_div, div_le_iff₀ hd]
  have hs := Real.sq_sqrt hc
  have hnon : 0 ≤ Real.sqrt c * (S + η) * (η / 3) := by positivity
  nlinarith

/-- Allocation of three positive durations, including when some segment costs vanish. -/
theorem exists_three_durations {c0 c1 c2 η : ℝ}
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (hη : 0 < η) :
    ∃ r0 r1 r2 : ℝ, 0 < r0 ∧ 0 < r1 ∧ 0 < r2 ∧ r0 + r1 + r2 = 1 ∧
      c0 / r0 + c1 / r1 + c2 / r2 ≤
        (Real.sqrt c0 + Real.sqrt c1 + Real.sqrt c2 + η) ^ 2 := by
  let S := Real.sqrt c0 + Real.sqrt c1 + Real.sqrt c2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hden : S + η ≠ 0 := ne_of_gt (by positivity)
  refine ⟨duration c0 S η, duration c1 S η, duration c2 S η,
    duration_pos hS hη, duration_pos hS hη, duration_pos hS hη, ?_, ?_⟩
  · unfold duration
    field_simp
    dsimp [S]
    ring
  · have hsum := add_le_add (add_le_add (duration_cost_le h0 hS hη)
      (duration_cost_le h1 hS hη)) (duration_cost_le h2 hS hη)
    change _ ≤ (S + η) ^ 2
    have he : Real.sqrt c0 * (S + η) + Real.sqrt c1 * (S + η) +
        Real.sqrt c2 * (S + η) = S * (S + η) := by dsimp [S]; ring
    rw [he] at hsum
    exact hsum.trans (by nlinarith)

/-- Remove the scalar tolerance from extended-real upper bounds. -/
theorem le_of_forall_positive_square {v : ℝ≥0∞} {S : ℝ}
    (h : ∀ η : ℝ, 0 < η → v ≤ ENNReal.ofReal ((S + η) ^ 2)) :
    v ≤ ENNReal.ofReal (S ^ 2) := by
  let δ : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun j ↦ ENNReal.ofReal ((S + δ j) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (S ^ 2))) := by
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero] using ((tendsto_const_nhds (x := S)).add hδ).pow 2
  exact ge_of_tendsto' ht (fun j ↦ h (δ j) (by dsimp [δ]; positivity))

/-- Apply duration approximants to an infimum, retaining the actual admissible predicate. -/
theorem constrainedInfimum_le_square_of_approximants {X : Type*}
    (good : X → Prop) (energy : X → ℝ≥0∞) (S : ℝ)
    (h : ∀ η : ℝ, 0 < η → ∃ μ : X, good μ ∧
      energy μ ≤ ENNReal.ofReal ((S + η) ^ 2)) :
    MatrixTransport.ReactionZero.constrainedInfimum good energy ≤ ENNReal.ofReal (S ^ 2) := by
  apply le_of_forall_positive_square
  intro η hη
  obtain ⟨μ, hμ, hE⟩ := h η hη
  exact (iInf_le_of_le μ (iInf_le_of_le hμ le_rfl)).trans hE

/-- A helper identifying the finite-baseline free-transport target from a proved ray sandwich.
The target here is the existing `freeTransportValue`, with its finite-baseline restriction. -/
theorem freeTransportValue_eq_of_ray_sandwich {d n k : ℕ}
    {Ω : Set (MatrixTransport.ReactionZero.ClosedDomain.Space d)}
    (P : MatrixTransport.ReactionZero.Limit.Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    {E B : ℝ} (hE : 0 ≤ E)
    (hlower : ∀ t : ℝ, 0 < t → ENNReal.ofReal E ≤
      MatrixTransport.ReactionZero.Limit.minimumValue P (t • L) H)
    (hupper : ∀ t : ℝ, 0 < t →
      MatrixTransport.ReactionZero.Limit.minimumValue P (t • L) H ≤
        ENNReal.ofReal ((Real.sqrt E + B / t) ^ 2)) :
    MatrixTransport.TransportInfinity.freeTransportValue P L H = ENNReal.ofReal E := by
  let t : ℕ → ℝ := fun j ↦ (j : ℝ) + 1
  have ht : Tendsto t atTop atTop :=
    tendsto_atTop_mono (fun j ↦ by dsimp [t]; linarith)
      (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ ↦ (j : ℝ)) atTop atTop)
  have hp : ∀ j, 0 < t j := fun j ↦ by dsimp [t]; positivity
  have hi : Tendsto (fun j ↦ (1 : ℝ) / t j) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hB : Tendsto (fun j ↦ B / t j) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using hi.const_mul B
  have hu : Tendsto (fun j ↦ ENNReal.ofReal ((Real.sqrt E + B / t j) ^ 2))
      atTop (𝓝 (ENNReal.ofReal E)) := by
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero, Real.sq_sqrt hE] using
      ((tendsto_const_nhds (x := Real.sqrt E)).add hB).pow 2
  have hv : Tendsto (fun j ↦ MatrixTransport.ReactionZero.Limit.minimumValue P (t j • L) H)
      atTop (𝓝 (ENNReal.ofReal E)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun j ↦ hlower (t j) (hp j)) (fun j ↦ hupper (t j) (hp j))
  exact tendsto_nhds_unique
    (MatrixTransport.TransportInfinity.transport_infinity_regime P L H t ht) hv

#print axioms exists_three_durations
#print axioms le_of_forall_positive_square
#print axioms constrainedInfimum_le_square_of_approximants
#print axioms freeTransportValue_eq_of_ray_sandwich
end LiZouTransport.HubScalar
