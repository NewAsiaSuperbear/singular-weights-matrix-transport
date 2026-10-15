import MatrixTransport.ReactionZero.MeasureCompactness
import MatrixTransport.ReactionZero.DualRepresentation

/-!
# Weak closure of an actual signed-measure continuity equation

The test family consists of genuine continuous coordinate fields, and the equation uses
the original Jordan pairing of finite signed measures. The index type can be the entire
closed-domain `C¹` jet space; no countability restriction on tests is imposed.

This module proves weak closure for a specified family. The full closed-domain `C¹` test
family, general operator, and fixed endpoint pairings are constructed in `ClosedDomainTests`.
`LimitTheorem` instantiates the closure theorem for that family and the paper's continuity
equation, so every original closed-domain test is retained in the variational limit.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BigOperators

namespace MatrixTransport.ReactionZero

variable {Q ι τ : Type*} [MetricSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q] [Fintype ι]

/-- A specified family of continuous coordinate fields and fixed endpoint evaluations. -/
structure ContinuousTestFamily (Q ι τ : Type*) [TopologicalSpace Q] where
  field : τ → C(Q, ι → ℝ)
  endpoint : τ → ℝ

/-- The concrete weak equation on actual finite signed-coordinate measures. -/
def SatisfiesContinuityEquation (T : ContinuousTestFamily Q ι τ)
    (μ : ι → SignedMeasure Q) : Prop :=
  ∀ t, Duality.coordinatePair (fun _ ↦ 1) μ (T.field t) = T.endpoint t

omit [CompactSpace Q] [BorelSpace Q] in
/-- Pairing with each specified continuous vector field converges under coordinate weak-star
convergence, with no finite or countable restriction on the index type of test fields. -/
theorem coordinatePair_tendsto_of_signedWeakStar (μ : ℕ → ι → SignedMeasure Q)
    (ν : ι → SignedMeasure Q) (hμ : SignedWeakStarTendsto μ ν)
    (a : C(Q, ι → ℝ)) :
    Tendsto (fun j ↦ Duality.coordinatePair (fun _ ↦ 1) (μ j) a) atTop
      (𝓝 (Duality.coordinatePair (fun _ ↦ 1) ν a)) := by
  exact tendsto_finsetSum _ fun i _ ↦
    tendsto_const_nhds.mul (hμ i (Duality.coordinateTest a i))

omit [CompactSpace Q] [BorelSpace Q] in
/-- The continuity equation is closed under actual coordinate weak-star convergence. -/
theorem satisfiesContinuityEquation_of_signedWeakStar
    (T : ContinuousTestFamily Q ι τ) (μ : ℕ → ι → SignedMeasure Q)
    (ν : ι → SignedMeasure Q) (hμ : SignedWeakStarTendsto μ ν)
    (hCE : ∀ j, SatisfiesContinuityEquation T (μ j)) :
    SatisfiesContinuityEquation T ν := by
  intro t
  have ht := coordinatePair_tendsto_of_signedWeakStar μ ν hμ (T.field t)
  have hconst : (fun j ↦ Duality.coordinatePair (fun _ ↦ 1) (μ j) (T.field t)) =
      fun _ ↦ T.endpoint t := funext fun j ↦ hCE j t
  rw [hconst] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

#print axioms coordinatePair_tendsto_of_signedWeakStar
#print axioms satisfiesContinuityEquation_of_signedWeakStar

end MatrixTransport.ReactionZero
