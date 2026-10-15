import MatrixTransport.PartialReaction.Compactness
import MatrixTransport.PartialReaction.DirectionalReaction

/-!
# Extinction of reaction in fixed target-kernel directions

The final theorems retain the paper's complete closed-domain C¹ continuity equation and
arbitrary PSD Radon endpoints. The energy is bounded only eventually; matrix convergence
supplies the weight bound, and the actual affine time test supplies the mass bound.

For a fixed matrix `P` with `Hstarᵀ P = 0`, the right-reaction variation is the integral of
the actual Frobenius norm of the RN density `R P`. It is not defined to be a coordinate-TV
sum. The latter only serves as a proved upper bound for the genuine norm integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialReaction

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit

variable {n k p : ℕ}

section Measures

variable {Q : Type*} [MeasurableSpace Q]

/-- The actual signed matrix-measure product `R P`, coordinate by coordinate. -/
def rightReactionMeasure (μ : Coord n k → SignedMeasure Q)
    (P : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) (j : Fin p) : SignedMeasure Q :=
  reactionDirection μ (fun a ↦ P a j) i

/-- Actual Frobenius RN variation of the signed matrix measure `R P`. -/
def rightReactionFrobeniusTV (μ : Coord n k → SignedMeasure Q)
    (P : Matrix (Fin n) (Fin p) ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.sqrt
    (frobeniusSq (ReactionZero.reaction (ReactionZero.density μ x) * P))) ∂jointReference μ

theorem reactionDirectionDensity_column (μ : Coord n k → SignedMeasure Q)
    (P : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) (j : Fin p) (x : Q) :
    reactionDirectionDensity μ (fun a ↦ P a j) i x =
      (ReactionZero.reaction (ReactionZero.density μ x) * P) i j := by
  simp only [reactionDirectionDensity, Matrix.mul_apply, ReactionZero.reaction, mul_comm]

/-- The actual product measure is represented by the multiplied original RN density. -/
theorem withDensity_rightReactionMeasure (μ : Coord n k → SignedMeasure Q)
    (P : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) (j : Fin p) :
    (jointReference μ).withDensityᵥ
      (fun x ↦ (ReactionZero.reaction (ReactionZero.density μ x) * P) i j) =
      rightReactionMeasure μ P i j := by
  simp_rw [← reactionDirectionDensity_column μ P i j]
  exact withDensity_reactionDirection μ (fun a ↦ P a j) i

theorem reactionDirectionTV_eq_lintegral_abs (μ : Coord n k → SignedMeasure Q)
    (v : Fin n → ℝ) (i : Fin n) :
    (reactionDirection μ v i).totalVariation univ =
      ∫⁻ x, ENNReal.ofReal |reactionDirectionDensity μ v i x| ∂jointReference μ := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (reactionDirection μ v i).totalVariation univ),
    reactionDirectionTV_eq_integral_abs]
  exact ofReal_integral_eq_lintegral_ofReal
    (reactionDirectionDensity_integrable μ v i).abs (ae_of_all _ fun _ ↦ abs_nonneg _)

theorem measurable_reactionDirectionDensity (μ : Coord n k → SignedMeasure Q)
    (v : Fin n → ℝ) (i : Fin n) :
    Measurable (reactionDirectionDensity μ v i) := by
  unfold reactionDirectionDensity ReactionZero.density
  exact Finset.measurable_fun_sum _ fun a _ ↦
    (measurable_rnDeriv_jointReference μ _).const_mul (v a)

/-- The norm integral is controlled by actual directional coordinate variations. -/
theorem rightReactionFrobeniusTV_le_sum_directionTV
    (μ : Coord n k → SignedMeasure Q) (P : Matrix (Fin n) (Fin p) ℝ) :
    rightReactionFrobeniusTV μ P ≤
      ∑ a : Fin n × Fin p, (rightReactionMeasure μ P a.1 a.2).totalVariation univ := by
  calc rightReactionFrobeniusTV μ P
      ≤ ∫⁻ x, ENNReal.ofReal (∑ a : Fin n × Fin p,
          |(ReactionZero.reaction (ReactionZero.density μ x) * P) a.1 a.2|)
          ∂jointReference μ :=
        lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
          (MatrixVariation.sqrt_frobeniusSq_le_sum_abs
            (ReactionZero.reaction (ReactionZero.density μ x) * P))
      _ = ∫⁻ x, ∑ a : Fin n × Fin p,
          ENNReal.ofReal |reactionDirectionDensity μ (fun b ↦ P b a.2) a.1 x|
          ∂jointReference μ := by
        congr 1
        funext x
        simp_rw [reactionDirectionDensity_column]
        exact ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ abs_nonneg _)
      _ = ∑ a : Fin n × Fin p, ∫⁻ x,
          ENNReal.ofReal |reactionDirectionDensity μ (fun b ↦ P b a.2) a.1 x|
          ∂jointReference μ :=
        lintegral_finsetSum Finset.univ fun a _ ↦
          (measurable_reactionDirectionDensity μ (fun b ↦ P b a.2) a.1).abs.ennreal_ofReal
      _ = ∑ a : Fin n × Fin p,
          (rightReactionMeasure μ P a.1 a.2).totalVariation univ := by
        unfold rightReactionMeasure
        apply Finset.sum_congr rfl
        intro a _
        exact (reactionDirectionTV_eq_lintegral_abs μ (fun b ↦ P b a.2) a.1).symm

/-- Actual coordinate product-TV limits control the actual Frobenius norm integral. -/
theorem rightReactionFrobeniusTV_tendsto_zero
    (μ : ℕ → Coord n k → SignedMeasure Q) (P : Matrix (Fin n) (Fin p) ℝ)
    (h : ∀ i j, Tendsto
      (fun a ↦ (rightReactionMeasure (μ a) P i j).totalVariation univ) atTop (𝓝 0)) :
    Tendsto (fun a ↦ rightReactionFrobeniusTV (μ a) P) atTop (𝓝 0) := by
  have hs : Tendsto (fun j ↦ ∑ a : Fin n × Fin p,
      (rightReactionMeasure (μ j) P a.1 a.2).totalVariation univ) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum Finset.univ (fun (a : Fin n × Fin p) _ ↦ h a.1 a.2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun _ ↦ bot_le) (fun j ↦ rightReactionFrobeniusTV_le_sum_directionTV (μ j) P)

end Measures

section PaperProblem

variable {d : ℕ} {Ω : Set (ClosedDomain.Space d)}

/-- Whole-sequence extinction of every fixed target-kernel direction on eventual finite
action sublevels of the original all-C¹ continuity equation. No trace/TV bound is assumed. -/
theorem reactionDirectionTV_tendsto_zero_of_eventually_bounded
    (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (μ : ℕ → Path Ω n k) (hgood : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, ReactionZero.action L (H j) (μ j) ≤ C)
    (v : Fin n → ℝ) (hv : Hstar.transpose *ᵥ v = 0) (i : Fin n) :
    Tendsto (fun j ↦ (reactionDirection (μ j) v i).totalVariation univ)
      atTop (𝓝 0) := by
  obtain ⟨K, _, hHK⟩ := exists_frobeniusSq_bound H Hstar hH
  obtain ⟨N, hN⟩ := eventually_atTop.mp hE
  let σ : ℕ → ℕ := fun a ↦ a + N
  have hσ : StrictMono σ := fun a b hab ↦ Nat.add_lt_add_right hab N
  have hbound : ∀ a, ReactionZero.action L (H (σ a)) (μ (σ a)) ≤ ENNReal.ofReal C.toReal := by
    intro a
    simpa only [ENNReal.ofReal_toReal hC] using hN (σ a) (by dsimp [σ]; omega)
  have hwM : Measurable (ClosedDomain.timeWeight : ClosedDomain.Q Ω → ℝ) :=
    ClosedDomain.timeWeight.continuous.measurable
  have hw : ∀ x : ClosedDomain.Q Ω, 0 ≤ ClosedDomain.timeWeight x ∧
      ClosedDomain.timeWeight x ≤ 1 :=
    fun x ↦ ⟨ClosedDomain.timeWeight_nonneg x, ClosedDomain.timeWeight_le_one x⟩
  have ht := reactionDirectionTV_tendsto_zero_on_sublevel L (fun a ↦ H (σ a))
    Hstar (hH.comp hσ.tendsto_atTop) (fun a ↦ μ (σ a))
    (fun a ↦ (hgood (σ a)).1) C.toReal K ENNReal.toReal_nonneg hbound
    (fun a ↦ hHK (σ a)) ClosedDomain.timeWeight hwM hw
    (ClosedDomain.endpointMass P.initial)
    (ClosedDomain.endpointMass_nonneg _ P.initial_positive)
    (fun a ↦ time_identity P (μ (σ a)) (hgood (σ a))) v hv i
  exact (tendsto_add_atTop_iff_nat N).1 ht

/-- Whole-sequence extinction of actual right-reaction Frobenius variation for every fixed
matrix whose columns lie in the target transpose-kernel. This includes the orthogonal
kernel projection, without requiring the changing weights to have a common eigenbasis. -/
theorem rightReactionFrobeniusTV_tendsto_zero_of_eventually_bounded
    (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (μ : ℕ → Path Ω n k) (hgood : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, ReactionZero.action L (H j) (μ j) ≤ C)
    (A : Matrix (Fin n) (Fin p) ℝ) (hA : Hstar.transpose * A = 0) :
    Tendsto (fun j ↦ rightReactionFrobeniusTV (μ j) A) atTop (𝓝 0) := by
  apply rightReactionFrobeniusTV_tendsto_zero
  intro i j
  have hv : Hstar.transpose *ᵥ (fun a ↦ A a j) = 0 := by
    funext b
    have hab := congrFun (congrFun hA b) j
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.zero_apply,
      Matrix.zero_apply] using hab
  exact reactionDirectionTV_tendsto_zero_of_eventually_bounded P L H Hstar hH C hC
    μ hgood hE (fun a ↦ A a j) hv i

end PaperProblem

end MatrixTransport.PartialReaction

#print axioms MatrixTransport.PartialReaction.withDensity_rightReactionMeasure
#print axioms MatrixTransport.PartialReaction.rightReactionFrobeniusTV_le_sum_directionTV
#print axioms MatrixTransport.PartialReaction.reactionDirectionTV_tendsto_zero_of_eventually_bounded
#print axioms MatrixTransport.PartialReaction.rightReactionFrobeniusTV_tendsto_zero_of_eventually_bounded
