import MatrixTransport.PartialWeights.FixedBasis

/-!
# Zero target weights without fixed-basis hypotheses

At a zero target Gram, relative domination is automatic. Thus both weights can
simultaneously tend to zero with completely arbitrary rotating eigenvectors.
The one-weight versions also follow from the genuine original-model theorem.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix

namespace MatrixTransport.PartialWeights

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {n k d p q : ℕ} {Ω : Set (ClosedDomain.Space d)}
variable [Fact (IsCompact Ω)]

/-- Complete simultaneous zero-weight limit, with arbitrary rotating bases. -/
theorem simultaneous_zero_weights_regime (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (hL : Tendsto L atTop (𝓝 0))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 0)) :
    FixedBasisConclusion P L 0 H 0 p q := by
  apply partial_weights_regime P L 0 hL H 0 hH
    (fun _ ↦ 1) tendsto_const_nhds
  refine Filter.Eventually.of_forall fun j ↦ ⟨by norm_num, ?_, ?_⟩
  · simpa only [gram_zero, smul_zero, sub_zero] using posSemidef_gram (L j)
  · simpa only [gram_zero, smul_zero, sub_zero] using posSemidef_gram (H j)

/-- The original zero-transport regime with any fixed, possibly singular reaction weight.
This is a formal strengthening of the already studied zero-transport direction. -/
theorem transport_zero_weights_regime (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (hL : Tendsto L atTop (𝓝 0))
    (H : Matrix (Fin n) (Fin n) ℝ) :
    FixedBasisConclusion P L 0 (fun _ ↦ H) H p q := by
  apply partial_weights_regime P L 0 hL (fun _ ↦ H) H tendsto_const_nhds
    (fun _ ↦ 1) tendsto_const_nhds
  refine Filter.Eventually.of_forall fun j ↦ ⟨by norm_num, ?_, ?_⟩
  · simpa only [gram_zero, smul_zero, sub_zero] using posSemidef_gram (L j)
  · simpa only [one_smul, sub_self] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)

/-- Complete reaction-zero limit without fixed or controlled reaction eigenvectors. -/
theorem reaction_zero_weights_regime (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 0)) :
    FixedBasisConclusion P (fun _ ↦ L) L H 0 p q := by
  apply partial_weights_regime P (fun _ ↦ L) L tendsto_const_nhds H 0 hH
    (fun _ ↦ 1) tendsto_const_nhds
  refine Filter.Eventually.of_forall fun j ↦ ⟨by norm_num, ?_, ?_⟩
  · simpa only [one_smul, sub_self] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin k) (Fin k) ℝ).PosSemidef)
  · simpa only [gram_zero, smul_zero, sub_zero] using posSemidef_gram (H j)

#print axioms simultaneous_zero_weights_regime
#print axioms transport_zero_weights_regime
#print axioms reaction_zero_weights_regime

end MatrixTransport.PartialWeights
