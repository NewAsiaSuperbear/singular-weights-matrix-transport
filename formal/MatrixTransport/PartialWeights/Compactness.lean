import MatrixTransport.PartialReaction.Compactness
import MatrixTransport.PartialWeights.JointWeights

/-!
# Actual path compactness with both matrix weights bounded

The original full closed-domain continuity equation gives the time identity. Genuine
pointwise action estimates then bound the mass and every signed coordinate for varying
transport and reaction weights. Compactness is derived, not a premise of the final result.
The existing fixed-weight direct method supplies PSD attainment for any singular target.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialWeights

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {n k d : ℕ} {Ω : Set (ClosedDomain.Space d)}
variable [Fact (IsCompact Ω)]

/-- Uniform action and upper bounds on both weights give an actual admissible weak-star limit. -/
theorem sublevel_subsequence (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (KL KH : ℝ) (hLK : ∀ j, frobeniusSq (L j) ≤ KL)
    (hHK : ∀ j, frobeniusSq (H j) ≤ KH)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hgood : ∀ j, Good P (μ j)) (hE : ∀ j, action (L j) (H j) (μ j) ≤ C) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν := by
  let m0 := ClosedDomain.endpointMass P.initial
  have hm0 : 0 ≤ m0 := ClosedDomain.endpointMass_nonneg _ P.initial_positive
  have hwM : Measurable (ClosedDomain.timeWeight : ClosedDomain.Q Ω → ℝ) :=
    ClosedDomain.timeWeight.continuous.measurable
  have hw : ∀ x : ClosedDomain.Q Ω, 0 ≤ ClosedDomain.timeWeight x ∧
      ClosedDomain.timeWeight x ≤ 1 :=
    fun x ↦ ⟨ClosedDomain.timeWeight_nonneg x, ClosedDomain.timeWeight_le_one x⟩
  have hEof : ∀ j, action (L j) (H j) (μ j) ≤ ENNReal.ofReal C.toReal := by
    intro j
    simpa only [ENNReal.ofReal_toReal hC] using hE j
  let B := Real.toNNReal (PathCoercivity.coordinateTVBound C.toReal
    (2 * m0 + 2 * KH * C.toReal) KL KH)
  have hTV : ∀ j c, (μ j c).totalVariation univ ≤ (B : ℝ≥0∞) := by
    intro j c
    have hfin : action (L j) (H j) (μ j) ≠ ⊤ :=
      ne_top_of_le_ne_top hC (hE j)
    have hT := PathCoercivity.pathTrace_bound_on_sublevel (L j) (H j) (μ j)
      (hgood j).1 C.toReal KH ENNReal.toReal_nonneg (hEof j) (hHK j)
      ClosedDomain.timeWeight hwM hw m0 hm0 (time_identity P (μ j) (hgood j))
    exact PathCoercivity.coordinateTV_le_bound_ennreal (L j) (H j) (μ j)
      (hgood j).1 hfin C.toReal (2 * m0 + 2 * KH * C.toReal) KL KH
      (ENNReal.toReal_mono hC (hE j)) hT (hLK j) (hHK j) c
  obtain ⟨ν, φ, hφ, hweak⟩ := signedMeasureFamily_subsequence B μ hTV
  have hν : Good P ν :=
    ⟨massSymmetric_of_signedWeakStar _ _ hweak (fun j ↦ (hgood (φ j)).1),
      ClosedDomain.paperContinuityEquation_of_signedWeakStar P.operator P.initial P.terminal
        _ ν hweak (fun j ↦ (hgood (φ j)).2)⟩
  exact ⟨ν, φ, hφ, hweak, hν⟩

/-- A finite prefix may be discarded before applying the actual two-weight sublevel bound. -/
theorem eventually_sublevel_subsequence (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (KL KH : ℝ) (hLK : ∀ j, frobeniusSq (L j) ≤ KL)
    (hHK : ∀ j, frobeniusSq (H j) ≤ KH)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hgood : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, action (L j) (H j) (μ j) ≤ C) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hE
  let σ : ℕ → ℕ := fun j ↦ j + N
  have hσ : StrictMono σ := fun a b hab ↦ Nat.add_lt_add_right hab N
  obtain ⟨ν, φ, hφ, hw, hg⟩ := sublevel_subsequence P
    (fun j ↦ L (σ j)) (fun j ↦ H (σ j)) KL KH
    (fun j ↦ hLK (σ j)) (fun j ↦ hHK (σ j)) C hC
    (fun j ↦ μ (σ j)) (fun j ↦ hgood (σ j))
    (fun j ↦ hN (σ j) (by dsimp [σ]; omega))
  exact ⟨ν, σ ∘ φ, hσ.comp hφ, hw, hg⟩

/-- Every finite target minimum is attained with PSD measure mass, including singular weights. -/
theorem minimumValue_attainment (P : Problem Ω n k)
    (Lstar : Matrix (Fin k) (Fin k) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hb : minimumValue P Lstar Hstar ≠ ⊤) :
    ∃ ν : Path Ω n k, Good P ν ∧ action Lstar Hstar ν = minimumValue P Lstar Hstar ∧
      ∀ B, MeasurableSet B → (MatrixPositivity.massMeasureValue ν B).PosSemidef :=
  PartialReaction.minimumValue_attainment P Lstar Hstar hb

/-- Convergent weights and bounded actual energies have a limiting target sublevel path. -/
theorem bounded_subsequence (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hg : ∀ j, Good P (μ j)) (hE : ∀ j, action (L j) (H j) (μ j) ≤ C) :
    ∃ (ν : Path Ω n k) (φ : ℕ → ℕ), StrictMono φ ∧
      SignedWeakStarTendsto (fun j ↦ μ (φ j)) ν ∧ Good P ν ∧
      action Lstar Hstar ν ≤ C := by
  obtain ⟨KL, _, hLK⟩ := PartialReaction.exists_frobeniusSq_bound L Lstar hL
  obtain ⟨KH, _, hHK⟩ := PartialReaction.exists_frobeniusSq_bound H Hstar hH
  obtain ⟨ν, φ, hφ, hw, hν⟩ := sublevel_subsequence P L H KL KH hLK hHK C hC μ hg hE
  have he := action_le_varying_weights_liminf (fun j ↦ L (φ j)) Lstar
    (hL.comp hφ.tendsto_atTop) (fun j ↦ H (φ j)) Hstar
    (hH.comp hφ.tendsto_atTop) _ ν hw
  have hb : atTop.liminf (fun j ↦ action (L (φ j)) (H (φ j)) (μ (φ j))) ≤ C :=
    liminf_le_of_frequently_le'
      (Filter.Eventually.of_forall (fun j ↦ hE (φ j))).frequently
  exact ⟨ν, φ, hφ, hw, hν, he.trans hb⟩

/-- The generic extended-infimum certificate is discharged by the actual original path theory. -/
theorem bounded_sequence_certificate (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (hE : ∀ j, action (L (φ j)) (H (φ j)) (μ j) ≤ C) :
    ∃ ν, Good P ν ∧ action Lstar Hstar ν ≤ C := by
  obtain ⟨ν, _, _, _, hν, he⟩ := bounded_subsequence P (fun j ↦ L (φ j)) Lstar
    (hL.comp hφ.tendsto_atTop) (fun j ↦ H (φ j)) Hstar
    (hH.comp hφ.tendsto_atTop) C hC μ hg hE
  exact ⟨ν, hν, he⟩

#print axioms sublevel_subsequence
#print axioms minimumValue_attainment
#print axioms bounded_sequence_certificate

end MatrixTransport.PartialWeights
