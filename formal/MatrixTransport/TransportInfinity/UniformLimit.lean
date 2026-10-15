import MatrixTransport.TransportInfinity.LimitTheorem
import MatrixTransport.PartialWeights.WeightComparison

/-!
# Uniform divergence of all transport directions

No fixed eigenvectors, monotonicity or upper bound on the transport weights is needed.
The target retains exactly the original finite-action domain at identity transport weight.
Every finite matrix has an explicit Frobenius Gram upper bound, so preservation of this
domain is proved rather than assumed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.TransportInfinity

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {n k : ℕ} {Q : Type*} [MeasurableSpace Q]

/-- Increasing the transport Gram decreases the genuine extended action. -/
theorem action_le_of_transport_gram_domination
    (L K : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hLK : (gram L - gram K).PosSemidef) (μ : Coord n k → SignedMeasure Q) :
    ReactionZero.action L H μ ≤ ReactionZero.action K H μ := by
  have h := PartialWeights.action_le_inv_mul_of_relative_grams L K H H 1
    (by norm_num) (by simpa using hLK)
    (by simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)) μ
  simpa using h

/-- An explicit finite-matrix comparison proves that a finite current action has a
finite identity-transport baseline action; no inverse matrix or range hypothesis is used. -/
theorem action_identity_le_frobenius_mul
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (μ : Coord n k → SignedMeasure Q) :
    ReactionZero.action 1 H μ ≤ ENNReal.ofReal (frobeniusSq L + 1) *
      ReactionZero.action L H μ := by
  let c : ℝ := frobeniusSq L + 1
  have hc : 0 < c := by dsimp [c]; linarith [frobeniusSq_nonneg L]
  have hcone : 1 ≤ c := by dsimp [c]; linarith [frobeniusSq_nonneg L]
  have hα : 0 < 1 / c := by positivity
  have hαone : 1 / c ≤ 1 := (div_le_one hc).mpr hcone
  have hcgram : (c • (1 : Matrix (Fin k) (Fin k) ℝ) - gram L).PosSemidef := by
    have h := (posSemidef_frobeniusSq_sub_gram L).add Matrix.PosSemidef.one
    convert h using 1
    dsimp [c]
    module
  have hL : (gram (1 : Matrix (Fin k) (Fin k) ℝ) - (1 / c) • gram L).PosSemidef := by
    have h := hcgram.smul hα.le
    have hcancel : (1 / c) * c = 1 := by field_simp
    simpa only [gram, Matrix.transpose_one, Matrix.one_mul, smul_sub, smul_smul,
      hcancel, one_smul] using h
  have hH : (gram H - (1 / c) • gram H).PosSemidef := by
    have h := (posSemidef_gram H).smul (sub_nonneg.mpr hαone)
    convert h using 1
    module
  have h := PartialWeights.action_le_inv_mul_of_relative_grams 1 L H H
    (1 / c) hα hL hH μ
  simpa only [one_div, inv_inv, c] using h

/-- At weights dominating a positive scalar identity with scalar at least one,
the true finite-action domain is exactly the identity-baseline domain. -/
theorem action_ne_top_iff_identity
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (ht : 1 ≤ t)
    (hL : (gram L - gram (t • (1 : Matrix (Fin k) (Fin k) ℝ))).PosSemidef)
    (μ : Coord n k → SignedMeasure Q) :
    ReactionZero.action L H μ ≠ ⊤ ↔ ReactionZero.action 1 H μ ≠ ⊤ := by
  constructor
  · intro h
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) h)
      (action_identity_le_frobenius_mul L H μ)
  · intro h
    exact ne_top_of_le_ne_top ((action_ne_top_iff 1 H t ht μ).2 h)
      (action_le_of_transport_gram_domination L (t • 1) H hL μ)

/-- Each finite-baseline path recovers its reaction-channel energy when every
transport direction diverges, even with arbitrary rotating eigenvectors. -/
theorem action_tendsto_freeTransportAction_of_uniform_divergence
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hL : ∀ᶠ j in atTop,
      (gram (L j) - gram (t j • (1 : Matrix (Fin k) (Fin k) ℝ))).PosSemidef)
    (μ : Coord n k → SignedMeasure Q) (hμ : ReactionZero.action 1 H μ ≠ ⊤) :
    Tendsto (fun j ↦ ReactionZero.action (L j) H μ) atTop
      (𝓝 (freeTransportAction 1 H μ)) := by
  have hupper := action_tendsto_freeTransportAction 1 H t ht μ hμ
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun j ↦
      ha.trans_le (freeTransportAction_le_action 1 (L j) H μ)
  · intro c hc
    filter_upwards [hL, hupper.eventually (gt_mem_nhds hc)] with j hj hcj
    exact (action_le_of_transport_gram_domination (L j) (t j • 1) H hj μ).trans_lt hcj

/-- The extended value limit for any admissibility predicate retains the actual
identity-baseline finite domain, with all domain and recovery premises proved. -/
theorem constrainedValue_tendsto_of_uniform_divergence
    (good : (Coord n k → SignedMeasure Q) → Prop)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hL : ∀ᶠ j in atTop,
      (gram (L j) - gram (t j • (1 : Matrix (Fin k) (Fin k) ℝ))).PosSemidef) :
    Tendsto (fun j ↦ constrainedInfimum good (ReactionZero.action (L j) H)) atTop
      (𝓝 (constrainedInfimum (finiteBaseline good (ReactionZero.action 1 H))
        (freeTransportAction 1 H))) := by
  apply constrainedInfimum_tendsto_of_finite_domain good (ReactionZero.action 1 H)
    (freeTransportAction 1 H) (fun j ↦ ReactionZero.action (L j) H)
  · filter_upwards [hL, ht.eventually (eventually_ge_atTop 1)] with j hj htj
    exact fun μ _ ↦ action_ne_top_iff_identity (L j) H (t j) htj hj μ
  · exact Filter.Eventually.of_forall fun j μ _ _ ↦
      freeTransportAction_le_action 1 (L j) H μ
  · intro μ _ hμ
    exact action_tendsto_freeTransportAction_of_uniform_divergence L H t ht hL μ hμ

variable {d : ℕ} {Ω : Set (ClosedDomain.Space d)}

/-- Original general-operator minimum theorem when all transport directions diverge.
The full original closed-domain CE, arbitrary PSD Radon endpoints, and extended values
are retained. The limit is independent of the rotating transport eigenvectors. -/
theorem uniform_transport_infinity_regime (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hL : ∀ᶠ j in atTop,
      (gram (L j) - gram (t j • (1 : Matrix (Fin k) (Fin k) ℝ))).PosSemidef) :
    Tendsto (fun j ↦ minimumValue P (L j) H) atTop (𝓝 (freeTransportValue P 1 H)) :=
  constrainedValue_tendsto_of_uniform_divergence (Good P) L H t ht hL

/-- Original vanishing-gap near-minimizer actions converge to the same extended limit. -/
theorem uniform_nearMinimizer_energy_tendsto (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hL : ∀ᶠ j in atTop,
      (gram (L j) - gram (t j • (1 : Matrix (Fin k) (Fin k) ℝ))).PosSemidef)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (η : ℕ → ℝ≥0∞) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ j, ReactionZero.action (L j) H (μ j) ≤ minimumValue P (L j) H + η j) :
    Tendsto (fun j ↦ ReactionZero.action (L j) H (μ j)) atTop
      (𝓝 (freeTransportValue P 1 H)) := by
  have hv := uniform_transport_infinity_regime P L H t ht hL
  have hu : Tendsto (fun j ↦ minimumValue P (L j) H + η j) atTop
      (𝓝 (freeTransportValue P 1 H)) := by simpa only [add_zero] using hv.add hη
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hv hu
  · intro j
    exact iInf_le_of_le (μ j) (iInf_le_of_le (hg j) le_rfl)
  · exact hnear

/-- At a finite target value, even the reaction-channel actions of near-minimizers
converge to the target. This does not assert compactness of the unpenalized fluxes. -/
theorem uniform_nearMinimizer_freeAction_tendsto (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hL : ∀ᶠ j in atTop,
      (gram (L j) - gram (t j • (1 : Matrix (Fin k) (Fin k) ℝ))).PosSemidef)
    (hb : freeTransportValue P 1 H ≠ ⊤)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (η : ℕ → ℝ≥0∞) (hη : Tendsto η atTop (𝓝 0))
    (hnear : ∀ j, ReactionZero.action (L j) H (μ j) ≤ minimumValue P (L j) H + η j) :
    Tendsto (fun j ↦ freeTransportAction 1 H (μ j)) atTop
      (𝓝 (freeTransportValue P 1 H)) := by
  have he := uniform_nearMinimizer_energy_tendsto P L H t ht hL μ hg η hη hnear
  have hfinite := he.eventually (gt_mem_nhds (lt_top_iff_ne_top.mpr hb))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hL, ht.eventually (eventually_ge_atTop 1), hfinite] with j hj htj hfj
    have hbase := (action_ne_top_iff_identity (L j) H (t j) htj hj (μ j)).1
      (ne_of_lt hfj)
    have hbound : freeTransportValue P 1 H ≤ freeTransportAction 1 H (μ j) :=
      iInf_le_of_le (μ j) (iInf_le_of_le
        (show finiteBaseline (Good P) (ReactionZero.action 1 H) (μ j) from
          ⟨hg j, hbase⟩) le_rfl)
    exact ha.trans_le hbound
  · intro c hc
    filter_upwards [he.eventually (gt_mem_nhds hc)] with j hj
    exact (freeTransportAction_le_action 1 (L j) H (μ j)).trans_lt hj

#print axioms action_identity_le_frobenius_mul
#print axioms action_ne_top_iff_identity
#print axioms uniform_transport_infinity_regime
#print axioms uniform_nearMinimizer_freeAction_tendsto

end MatrixTransport.TransportInfinity
