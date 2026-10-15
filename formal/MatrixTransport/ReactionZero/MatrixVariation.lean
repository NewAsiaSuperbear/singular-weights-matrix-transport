import MatrixTransport.ReactionZero.PathCoercivity

/-!
# Frobenius total variation of the actual reaction matrix measure

The norm is explicitly the Frobenius norm `sqrt (sum of entry squares)` and never the
ambient matrix norm. The RN variation formula is bounded by the sum of the actual signed
coordinate total variations, so coordinate coercivity proves Frobenius-TV vanishing.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.ReactionZero.MatrixVariation

variable {n k : ℕ} {Q : Type*} [MeasurableSpace Q]

/-- The actual Frobenius RN total variation of the reaction matrix measure. -/
def reactionFrobeniusTV (μ : Coord n k → SignedMeasure Q) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.sqrt (frobeniusSq (reaction (density μ x)))) ∂jointReference μ

/-- The finite-dimensional Frobenius norm is at most the entrywise l1 norm. -/
theorem sqrt_frobeniusSq_le_sum_abs {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℝ) :
    Real.sqrt (frobeniusSq X) ≤ ∑ a : Fin m × Fin p, |X a.1 a.2| := by
  have hs : 0 ≤ ∑ a : Fin m × Fin p, |X a.1 a.2| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun a : Fin m × Fin p ↦ |X a.1 a.2|)
    (fun _ _ ↦ abs_nonneg _)
  have he : frobeniusSq X = ∑ a : Fin m × Fin p, |X a.1 a.2| ^ 2 := by
    simp only [frobeniusSq, Fintype.sum_prod_type, sq_abs]
  rw [← he] at hq
  exact (Real.sqrt_le_iff).2 ⟨hs, hq⟩

/-- Extended-valued coordinate RN variation identity, not just its real coercivity form. -/
theorem coordinateTV_eq_lintegral_abs (μ : Coord n k → SignedMeasure Q) (c : Coord n k) :
    (μ c).totalVariation univ =
      ∫⁻ x, ENNReal.ofReal |density μ x c| ∂jointReference μ := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (μ c).totalVariation univ),
    PathCoercivity.coordinateTV_eq_integral_abs]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_rnDeriv_jointReference μ c).abs
    (ae_of_all _ fun _ ↦ abs_nonneg _)

/-- Genuine Frobenius variation is controlled by the actual coordinate variation aggregate. -/
theorem reactionFrobeniusTV_le_reactionTotalTV (μ : Coord n k → SignedMeasure Q) :
    reactionFrobeniusTV μ ≤ PathCoercivity.reactionTotalTV μ := by
  calc reactionFrobeniusTV μ
      ≤ ∫⁻ x, ENNReal.ofReal (∑ a : Fin n × Fin n, |reaction (density μ x) a.1 a.2|)
          ∂jointReference μ :=
        lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
          (sqrt_frobeniusSq_le_sum_abs (reaction (density μ x)))
      _ = ∫⁻ x, ∑ a : Fin n × Fin n,
          ENNReal.ofReal |reaction (density μ x) a.1 a.2| ∂jointReference μ := by
        congr 1
        funext x
        exact ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ abs_nonneg _)
      _ = ∑ a : Fin n × Fin n, ∫⁻ x,
          ENNReal.ofReal |reaction (density μ x) a.1 a.2| ∂jointReference μ :=
        lintegral_finsetSum Finset.univ fun a _ ↦
          ((measurable_rnDeriv_jointReference μ (Sum.inr (Sum.inr a))).abs).ennreal_ofReal
      _ = PathCoercivity.reactionTotalTV μ := by
        unfold PathCoercivity.reactionTotalTV
        apply Finset.sum_congr rfl
        intro a _
        exact (coordinateTV_eq_lintegral_abs μ (Sum.inr (Sum.inr a))).symm

/-- Vanishing coordinate TV gives the original reaction Frobenius total-variation limit. -/
theorem reactionFrobeniusTV_tendsto_zero (μ : ℕ → Coord n k → SignedMeasure Q)
    (h : ∀ i j, Tendsto
      (fun a ↦ (μ a (Sum.inr (Sum.inr (i, j)))).totalVariation univ) atTop (𝓝 0)) :
    Tendsto (fun a ↦ reactionFrobeniusTV (μ a)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (PathCoercivity.reactionTotalTV_tendsto_zero μ h) (fun _ ↦ bot_le)
    (fun a ↦ reactionFrobeniusTV_le_reactionTotalTV (μ a))

#print axioms sqrt_frobeniusSq_le_sum_abs
#print axioms coordinateTV_eq_lintegral_abs
#print axioms reactionFrobeniusTV_le_reactionTotalTV
#print axioms reactionFrobeniusTV_tendsto_zero

end MatrixTransport.ReactionZero.MatrixVariation
