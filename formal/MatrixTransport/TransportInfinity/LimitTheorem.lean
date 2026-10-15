import MatrixTransport.TransportInfinity.FluxScaling
import MatrixTransport.TransportInfinity.MinimumLimit
import MatrixTransport.ReactionZero.LimitTheorem

/-!
# The original general-operator transport-weight ray limit

Increasing the transport weight on a fixed ray removes its energetic penalty on genuinely
finite-baseline paths.  Range and integrability compatibility are retained explicitly in the
target infimum.  No flux compactness or unrestricted free-flux relaxation is asserted.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.TransportInfinity

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {n k : ℕ}

section Measures

variable {Q : Type*} [MeasurableSpace Q]

/-- Every actual finite-baseline path recovers its reaction-channel action along any
transport scaling tending to infinity, including nonmonotone scalings. -/
theorem action_tendsto_freeTransportAction
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) (μ : Coord n k → SignedMeasure Q)
    (hμ : ReactionZero.action L H μ ≠ ⊤) :
    Tendsto (fun j ↦ ReactionZero.action (t j • L) H μ) atTop
      (𝓝 (freeTransportAction L H μ)) := by
  have hinv : Tendsto (fun j ↦ (1 : ℝ) / t j) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp ht)
  have hsmall : Tendsto (fun j ↦ ENNReal.ofReal ((1 : ℝ) / t j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hinv
  have hvanish : Tendsto (fun j ↦ ENNReal.ofReal ((1 : ℝ) / t j) * ReactionZero.action L H μ)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hsmall (Or.inr hμ)
  have hupper : Tendsto
      (fun j ↦ freeTransportAction L H μ +
        ENNReal.ofReal ((1 : ℝ) / t j) * ReactionZero.action L H μ)
      atTop (𝓝 (freeTransportAction L H μ)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := freeTransportAction L H μ)).add hvanish
  have hlarge : ∀ᶠ j in atTop, 1 ≤ t j := ht.eventually (eventually_ge_atTop 1)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun j ↦
      ha.trans_le (freeTransportAction_le_action L (t j • L) H μ)
  · intro c hc
    filter_upwards [hlarge, hupper.eventually (gt_mem_nhds hc)] with j hj hcj
    exact ((action_transport_sandwich L H (t j) hj μ).2).trans_lt hcj

/-- The value theorem is valid for every admissibility predicate on actual signed measures.
All finite-domain and recovery obligations are derived from the original support action. -/
theorem constrainedValue_tendsto_freeTransport
    (good : (Coord n k → SignedMeasure Q) → Prop)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    Tendsto (fun j ↦ constrainedInfimum good (ReactionZero.action (t j • L) H)) atTop
      (𝓝 (constrainedInfimum (finiteBaseline good (ReactionZero.action L H))
        (freeTransportAction L H))) := by
  apply constrainedInfimum_tendsto_of_finite_domain good (ReactionZero.action L H)
    (freeTransportAction L H) (fun j ↦ ReactionZero.action (t j • L) H)
  · filter_upwards [ht.eventually (eventually_ge_atTop 1)] with j hj
    intro μ _
    exact action_ne_top_iff L H (t j) hj μ
  · exact Filter.Eventually.of_forall fun j μ _ _ ↦
      freeTransportAction_le_action L (t j • L) H μ
  · intro μ _ hμ
    exact action_tendsto_freeTransportAction L H t ht μ hμ

end Measures

section PaperProblem

variable {d : ℕ} {Ω : Set (ClosedDomain.Space d)}

/-- The limiting value retains the original CE and the genuine finite-baseline class. -/
def freeTransportValue (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  constrainedInfimum (finiteBaseline (Good P) (ReactionZero.action L H))
    (freeTransportAction L H)

/-- Complete extended minimum-value limit for the original general operator and arbitrary
PSD Radon endpoints along a transport-weight ray.  The operator is unchanged; neither
compactness, LSC, target attainment nor a recovery certificate is a premise. -/
theorem transport_infinity_regime (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    Tendsto (fun j ↦ minimumValue P (t j • L) H) atTop (𝓝 (freeTransportValue P L H)) :=
  constrainedValue_tendsto_freeTransport (Good P) L H t ht

end PaperProblem

#print axioms action_tendsto_freeTransportAction
#print axioms constrainedValue_tendsto_freeTransport
#print axioms transport_infinity_regime

end MatrixTransport.TransportInfinity
