import MatrixTransport.PartialWeights.KernelExtinction

/-!
# Explicit dimension-independent Frobenius variation rates

The pointwise estimate retains the exact mass diagonal in each row before summing. It
therefore introduces no dimension factor. The integrated rate concerns the actual norm
integral of the multiplied matrix-measure density, with its integrability proved from the
genuine RN coordinate representation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialWeights

open MatrixTransport.ReactionZero
open MatrixTransport.PartialReaction

variable {n k p : ℕ}

theorem sum_column_directionSq {m p : ℕ} (K : Matrix (Fin m) (Fin m) ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) :
    (∑ j, directionSq K (fun a ↦ A a j)) = frobeniusSq (K.transpose * A) := by
  unfold directionSq frobeniusSq
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem sum_row_column_direction_bound {m p : ℕ}
    (g : Fin n → ℝ) (K : Matrix (Fin m) (Fin m) ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (E : ℝ) :
    (∑ i, ∑ j, 2 * E * (g i * directionSq K (fun a ↦ A a j))) =
      2 * E * ((∑ i, g i) * frobeniusSq (K.transpose * A)) := by
  rw [← sum_column_directionSq K A]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Exact diagonal coefficient for each rectangular flux-product entry. -/
theorem flux_product_entry_sq_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (a : Coord n k → ℝ)
    (hfin : ReactionZero.cost L H a ≠ ⊤) (A : Matrix (Fin k) (Fin p) ℝ)
    (i : Fin n) (j : Fin p) :
    (ReactionZero.flux a * A) i j ^ 2 ≤
      2 * (ReactionZero.cost L H a).toReal *
        (ReactionZero.mass a i i * directionSq L (fun b ↦ A b j)) := by
  have h := flux_pairing_sq_le L H a hfin (rowFluxDirection i (fun b ↦ A b j))
  rw [frob_rowFluxDirection, frob_gram_rowFluxDirection] at h
  simpa only [ReactionZero.flux, Matrix.mul_apply, mul_comm] using h

/-- Exact diagonal coefficient for each full reaction-product entry. -/
theorem reaction_product_entry_sq_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (a : Coord n k → ℝ)
    (hfin : ReactionZero.cost L H a ≠ ⊤) (A : Matrix (Fin n) (Fin p) ℝ)
    (i : Fin n) (j : Fin p) :
    (ReactionZero.reaction a * A) i j ^ 2 ≤
      2 * (ReactionZero.cost L H a).toReal *
        (ReactionZero.mass a i i * directionSq H (fun b ↦ A b j)) := by
  have h := reaction_pairing_sq_le L H a hfin (rowDirection i (fun b ↦ A b j))
  rw [frob_rowDirection, frob_gram_rowDirection] at h
  simpa only [ReactionZero.reaction, Matrix.mul_apply, mul_comm] using h

/-- Dimension-independent pointwise Frobenius estimate for the full rectangular product. -/
theorem flux_product_frobeniusSq_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (a : Coord n k → ℝ)
    (hfin : ReactionZero.cost L H a ≠ ⊤) (A : Matrix (Fin k) (Fin p) ℝ) :
    frobeniusSq (ReactionZero.flux a * A) ≤
      2 * (ReactionZero.cost L H a).toReal *
        ((ReactionZero.mass a).trace * frobeniusSq (L.transpose * A)) := by
  calc frobeniusSq (ReactionZero.flux a * A)
      ≤ ∑ i, ∑ j, 2 * (ReactionZero.cost L H a).toReal *
          (ReactionZero.mass a i i * directionSq L (fun b ↦ A b j)) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
          flux_product_entry_sq_le L H a hfin A i j
      _ = _ := by
        simpa only [Matrix.trace, Matrix.diag] using sum_row_column_direction_bound
          (fun i ↦ ReactionZero.mass a i i) L A (ReactionZero.cost L H a).toReal

/-- Dimension-independent pointwise Frobenius estimate for the full reaction product. -/
theorem reaction_product_frobeniusSq_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (a : Coord n k → ℝ)
    (hfin : ReactionZero.cost L H a ≠ ⊤) (A : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusSq (ReactionZero.reaction a * A) ≤
      2 * (ReactionZero.cost L H a).toReal *
        ((ReactionZero.mass a).trace * frobeniusSq (H.transpose * A)) := by
  calc frobeniusSq (ReactionZero.reaction a * A)
      ≤ ∑ i, ∑ j, 2 * (ReactionZero.cost L H a).toReal *
          (ReactionZero.mass a i i * directionSq H (fun b ↦ A b j)) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
          reaction_product_entry_sq_le L H a hfin A i j
      _ = _ := by
        simpa only [Matrix.trace, Matrix.diag] using sum_row_column_direction_bound
          (fun i ↦ ReactionZero.mass a i i) H A (ReactionZero.cost L H a).toReal

section Measures

variable {Q : Type*} [MeasurableSpace Q]

/-- Integrability of the actual Frobenius norm follows from finite-coordinate integrability;
it is not added as an analytic hypothesis in the concrete RN rates below. -/
theorem integrable_sqrt_frobeniusSq {m p : ℕ} (ρ : Measure Q)
    (X : Q → Matrix (Fin m) (Fin p) ℝ)
    (hM : ∀ i j, Measurable (fun x ↦ X x i j))
    (hI : ∀ i j, Integrable (fun x ↦ X x i j) ρ) :
    Integrable (fun x ↦ Real.sqrt (frobeniusSq (X x))) ρ := by
  have hXM : Measurable X := Measurable.of_eval fun i ↦ Measurable.of_eval fun j ↦ hM i j
  have hNM : Measurable (fun x ↦ Real.sqrt (frobeniusSq (X x))) :=
    Real.continuous_sqrt.measurable.comp (continuous_frobeniusSq.measurable.comp hXM)
  have hs : Integrable (fun x ↦ ∑ a : Fin m × Fin p, |X x a.1 a.2|) ρ :=
    integrable_finsetSum _ fun a _ ↦ (hI a.1 a.2).abs
  apply hs.mono' hNM.aestronglyMeasurable
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact MatrixVariation.sqrt_frobeniusSq_le_sum_abs (X x)

theorem flux_product_norm_integrable (μ : Coord n k → SignedMeasure Q)
    (A : Matrix (Fin k) (Fin p) ℝ) :
    Integrable (fun x ↦ Real.sqrt
      (frobeniusSq (ReactionZero.flux (ReactionZero.density μ x) * A))) (jointReference μ) := by
  apply integrable_sqrt_frobeniusSq
  · intro i j
    simp_rw [← fluxDirectionDensity_column μ A i j]
    exact measurable_fluxDirectionDensity μ (fun b ↦ A b j) i
  · intro i j
    simp_rw [← fluxDirectionDensity_column μ A i j]
    exact fluxDirectionDensity_integrable μ (fun b ↦ A b j) i

theorem reaction_product_norm_integrable (μ : Coord n k → SignedMeasure Q)
    (A : Matrix (Fin n) (Fin p) ℝ) :
    Integrable (fun x ↦ Real.sqrt
      (frobeniusSq (ReactionZero.reaction (ReactionZero.density μ x) * A)))
      (jointReference μ) := by
  apply integrable_sqrt_frobeniusSq
  · intro i j
    simp_rw [← reactionDirectionDensity_column μ A i j]
    exact measurable_reactionDirectionDensity μ (fun b ↦ A b j) i
  · intro i j
    simp_rw [← reactionDirectionDensity_column μ A i j]
    exact reactionDirectionDensity_integrable μ (fun b ↦ A b j) i

theorem rightFluxFrobeniusTV_eq_ofReal_integral (μ : Coord n k → SignedMeasure Q)
    (A : Matrix (Fin k) (Fin p) ℝ) :
    rightFluxFrobeniusTV μ A = ENNReal.ofReal (∫ x, Real.sqrt
      (frobeniusSq (ReactionZero.flux (ReactionZero.density μ x) * A)) ∂jointReference μ) := by
  exact (ofReal_integral_eq_lintegral_ofReal (flux_product_norm_integrable μ A)
    (ae_of_all _ fun _ ↦ Real.sqrt_nonneg _)).symm

theorem rightReactionFrobeniusTV_eq_ofReal_integral (μ : Coord n k → SignedMeasure Q)
    (A : Matrix (Fin n) (Fin p) ℝ) :
    rightReactionFrobeniusTV μ A = ENNReal.ofReal (∫ x, Real.sqrt
      (frobeniusSq (ReactionZero.reaction (ReactionZero.density μ x) * A))
      ∂jointReference μ) := by
  exact (ofReal_integral_eq_lintegral_ofReal (reaction_product_norm_integrable μ A)
    (ae_of_all _ fun _ ↦ Real.sqrt_nonneg _)).symm

theorem rightFluxFrobeniusTV_ne_top (μ : Coord n k → SignedMeasure Q)
    (A : Matrix (Fin k) (Fin p) ℝ) : rightFluxFrobeniusTV μ A ≠ ⊤ := by
  rw [rightFluxFrobeniusTV_eq_ofReal_integral]
  exact ENNReal.ofReal_ne_top

theorem rightReactionFrobeniusTV_ne_top (μ : Coord n k → SignedMeasure Q)
    (A : Matrix (Fin n) (Fin p) ℝ) : rightReactionFrobeniusTV μ A ≠ ⊤ := by
  rw [rightReactionFrobeniusTV_eq_ofReal_integral]
  exact ENNReal.ofReal_ne_top

theorem rightFluxFrobeniusTV_toReal_eq_integral (μ : Coord n k → SignedMeasure Q)
    (A : Matrix (Fin k) (Fin p) ℝ) :
    (rightFluxFrobeniusTV μ A).toReal = ∫ x, Real.sqrt
      (frobeniusSq (ReactionZero.flux (ReactionZero.density μ x) * A)) ∂jointReference μ := by
  rw [rightFluxFrobeniusTV_eq_ofReal_integral,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ Real.sqrt_nonneg _)]

theorem rightReactionFrobeniusTV_toReal_eq_integral (μ : Coord n k → SignedMeasure Q)
    (A : Matrix (Fin n) (Fin p) ℝ) :
    (rightReactionFrobeniusTV μ A).toReal = ∫ x, Real.sqrt
      (frobeniusSq (ReactionZero.reaction (ReactionZero.density μ x) * A))
      ∂jointReference μ := by
  rw [rightReactionFrobeniusTV_eq_ofReal_integral,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ Real.sqrt_nonneg _)]

/-- The actual full flux norm integral has a dimension-independent square estimate. -/
theorem rightFluxFrobeniusTV_sq_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : MassSymmetric μ) (hfin : ReactionZero.action L H μ ≠ ⊤)
    (A : Matrix (Fin k) (Fin p) ℝ) :
    (rightFluxFrobeniusTV μ A).toReal ^ 2 ≤
      2 * (ReactionZero.action L H μ).toReal *
        (PathCoercivity.pathTrace μ * frobeniusSq (L.transpose * A)) := by
  rw [rightFluxFrobeniusTV_toReal_eq_integral]
  have hb : ∀ᵐ x ∂jointReference μ, Real.sqrt
      (frobeniusSq (ReactionZero.flux (ReactionZero.density μ x) * A)) ^ 2 ≤
      2 * (ReactionZero.cost L H (ReactionZero.density μ x)).toReal *
        ((ReactionZero.mass (ReactionZero.density μ x)).trace *
          frobeniusSq (L.transpose * A)) := by
    filter_upwards [PathCoercivity.ae_cost_ne_top L H μ hfin] with x hx
    rw [Real.sq_sqrt (frobeniusSq_nonneg _)]
    exact flux_product_frobeniusSq_le L H (ReactionZero.density μ x) hx A
  have h := PathCoercivity.integral_abs_square_bound (flux_product_norm_integrable μ A)
    (PathCoercivity.integrable_mass_trace μ)
    (PathCoercivity.integrable_cost_toReal L H μ hfin) (frobeniusSq_nonneg (L.transpose * A))
    ((PathCoercivity.ae_mass_posSemidef L H μ hsym hfin).mono fun _ hx ↦
      trace_nonneg_of_posSemidef hx) (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg) hb
  have ha : ∀ x, |Real.sqrt (frobeniusSq
      (ReactionZero.flux (ReactionZero.density μ x) * A))| =
      Real.sqrt (frobeniusSq (ReactionZero.flux (ReactionZero.density μ x) * A)) :=
    fun _ ↦ abs_of_nonneg (Real.sqrt_nonneg _)
  simpa only [ha, PathCoercivity.integral_cost_toReal L H μ hfin,
    PathCoercivity.pathTrace] using h

/-- The actual full reaction norm integral has a dimension-independent square estimate. -/
theorem rightReactionFrobeniusTV_sq_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : MassSymmetric μ) (hfin : ReactionZero.action L H μ ≠ ⊤)
    (A : Matrix (Fin n) (Fin p) ℝ) :
    (rightReactionFrobeniusTV μ A).toReal ^ 2 ≤
      2 * (ReactionZero.action L H μ).toReal *
        (PathCoercivity.pathTrace μ * frobeniusSq (H.transpose * A)) := by
  rw [rightReactionFrobeniusTV_toReal_eq_integral]
  have hb : ∀ᵐ x ∂jointReference μ, Real.sqrt
      (frobeniusSq (ReactionZero.reaction (ReactionZero.density μ x) * A)) ^ 2 ≤
      2 * (ReactionZero.cost L H (ReactionZero.density μ x)).toReal *
        ((ReactionZero.mass (ReactionZero.density μ x)).trace *
          frobeniusSq (H.transpose * A)) := by
    filter_upwards [PathCoercivity.ae_cost_ne_top L H μ hfin] with x hx
    rw [Real.sq_sqrt (frobeniusSq_nonneg _)]
    exact reaction_product_frobeniusSq_le L H (ReactionZero.density μ x) hx A
  have h := PathCoercivity.integral_abs_square_bound (reaction_product_norm_integrable μ A)
    (PathCoercivity.integrable_mass_trace μ)
    (PathCoercivity.integrable_cost_toReal L H μ hfin) (frobeniusSq_nonneg (H.transpose * A))
    ((PathCoercivity.ae_mass_posSemidef L H μ hsym hfin).mono fun _ hx ↦
      trace_nonneg_of_posSemidef hx) (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg) hb
  have ha : ∀ x, |Real.sqrt (frobeniusSq
      (ReactionZero.reaction (ReactionZero.density μ x) * A))| =
      Real.sqrt (frobeniusSq (ReactionZero.reaction (ReactionZero.density μ x) * A)) :=
    fun _ ↦ abs_of_nonneg (Real.sqrt_nonneg _)
  simpa only [ha, PathCoercivity.integral_cost_toReal L H μ hfin,
    PathCoercivity.pathTrace] using h

/-- The actual flux square rate on a finite energy/trace sublevel. -/
theorem rightFluxFrobeniusTV_sq_le_on_sublevel (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : MassSymmetric μ) (E T : ℝ) (hE0 : 0 ≤ E)
    (hE : ReactionZero.action L H μ ≤ ENNReal.ofReal E)
    (hT : PathCoercivity.pathTrace μ ≤ T) (A : Matrix (Fin k) (Fin p) ℝ) :
    (rightFluxFrobeniusTV μ A).toReal ^ 2 ≤ 2 * E * T * frobeniusSq (L.transpose * A) := by
  have hfin : ReactionZero.action L H μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE
  have hET := mul_le_mul (ENNReal.toReal_le_of_le_ofReal hE0 hE) hT
    (PathCoercivity.pathTrace_nonneg L H μ hsym hfin) hE0
  calc (rightFluxFrobeniusTV μ A).toReal ^ 2
      ≤ 2 * (ReactionZero.action L H μ).toReal *
          (PathCoercivity.pathTrace μ * frobeniusSq (L.transpose * A)) :=
        rightFluxFrobeniusTV_sq_le L H μ hsym hfin A
      _ = 2 * ((ReactionZero.action L H μ).toReal * PathCoercivity.pathTrace μ) *
          frobeniusSq (L.transpose * A) := by ring
      _ ≤ 2 * (E * T) * frobeniusSq (L.transpose * A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hET (by norm_num))
          (frobeniusSq_nonneg _)
      _ = _ := by ring

/-- The actual reaction square rate on a finite energy/trace sublevel. -/
theorem rightReactionFrobeniusTV_sq_le_on_sublevel (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : MassSymmetric μ) (E T : ℝ) (hE0 : 0 ≤ E)
    (hE : ReactionZero.action L H μ ≤ ENNReal.ofReal E)
    (hT : PathCoercivity.pathTrace μ ≤ T) (A : Matrix (Fin n) (Fin p) ℝ) :
    (rightReactionFrobeniusTV μ A).toReal ^ 2 ≤ 2 * E * T * frobeniusSq (H.transpose * A) := by
  have hfin : ReactionZero.action L H μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE
  have hET := mul_le_mul (ENNReal.toReal_le_of_le_ofReal hE0 hE) hT
    (PathCoercivity.pathTrace_nonneg L H μ hsym hfin) hE0
  calc (rightReactionFrobeniusTV μ A).toReal ^ 2
      ≤ 2 * (ReactionZero.action L H μ).toReal *
          (PathCoercivity.pathTrace μ * frobeniusSq (H.transpose * A)) :=
        rightReactionFrobeniusTV_sq_le L H μ hsym hfin A
      _ = 2 * ((ReactionZero.action L H μ).toReal * PathCoercivity.pathTrace μ) *
          frobeniusSq (H.transpose * A) := by ring
      _ ≤ 2 * (E * T) * frobeniusSq (H.transpose * A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hET (by norm_num))
          (frobeniusSq_nonneg _)
      _ = _ := by ring

end Measures

end MatrixTransport.PartialWeights

#print axioms MatrixTransport.PartialWeights.flux_product_frobeniusSq_le
#print axioms MatrixTransport.PartialWeights.reaction_product_frobeniusSq_le
#print axioms MatrixTransport.PartialWeights.flux_product_norm_integrable
#print axioms MatrixTransport.PartialWeights.rightFluxFrobeniusTV_sq_le_on_sublevel
#print axioms MatrixTransport.PartialWeights.rightReactionFrobeniusTV_sq_le_on_sublevel
