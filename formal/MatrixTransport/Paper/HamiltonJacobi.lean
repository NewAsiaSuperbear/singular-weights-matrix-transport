import MatrixTransport.ReactionZero.LimitTheorem

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Matrix BigOperators

namespace MatrixTransport.Paper

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {d n k : ℕ} {Ω : Set (ClosedDomain.Space d)} [Fact (IsCompact Ω)]

/-- Endpoint value of an actual closed-domain C¹ test. -/
def endpointValue (P : Problem Ω n k) (φ : ClosedDomain.ClosedC1Jet Ω n) : ℝ :=
  ClosedDomain.endpointPair P.terminal φ 1 ⟨zero_le_one, le_rfl⟩ -
    ClosedDomain.endpointPair P.initial φ 0 ⟨le_rfl, zero_le_one⟩

/-- A genuine Hamilton–Jacobi field bounds the action of every original Radon competitor. -/
theorem action_ge_endpoint (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (φ : ClosedDomain.ClosedC1Jet Ω n)
    (hφ : ∀ x, ClosedDomain.testField P.operator φ x ∈ ReactionZero.dualSet L H)
    (μ : Path Ω n k) (hμ : Good P μ) :
    ENNReal.ofReal (endpointValue P φ) ≤ action L H μ := by
  rw [WeightedSet.action_eq_continuousDual]
  have hce : Duality.coordinatePair (fun _ ↦ 1) μ
      (ClosedDomain.testField P.operator φ) = endpointValue P φ := hμ.2 φ
  rw [← hce]
  exact le_iSup₂ (f := fun (a : C(ClosedDomain.Q Ω, Coord n k → ℝ))
    (_ : ∀ x, a x ∈ ReactionZero.dualSet L H) ↦
      ENNReal.ofReal (Duality.coordinatePair (fun _ ↦ 1) μ a))
    (ClosedDomain.testField P.operator φ) hφ

/-- The same all-competitor certificate bounds the actual extended minimum. -/
theorem minimumValue_ge_endpoint (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (φ : ClosedDomain.ClosedC1Jet Ω n)
    (hφ : ∀ x, ClosedDomain.testField P.operator φ x ∈ ReactionZero.dualSet L H) :
    ENNReal.ofReal (endpointValue P φ) ≤ minimumValue P L H := by
  apply le_iInf
  intro μ
  apply le_iInf
  intro hμ
  exact action_ge_endpoint P L H φ hφ μ hμ

#print axioms action_ge_endpoint
#print axioms minimumValue_ge_endpoint

end MatrixTransport.Paper
