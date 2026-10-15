import MatrixTransport.ReactionZero.PathCoercivity

/-!
# Actual reaction variation in a fixed direction

The signed measure is the genuine finite linear combination of reaction coordinate measures.
Its density against the original joint reference is proved by linearity of `withDensityᵥ`,
and its total variation is computed from that density. The weight coefficient is exactly
the squared Euclidean length of `Hᵀ v`, so only fixed kernel directions vanish in a partial
reaction degeneration.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialReaction

open MatrixTransport.ReactionZero

variable {n k : ℕ}

def directionSq (H : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ a, (H.transpose *ᵥ v) a ^ 2

theorem directionSq_nonneg (H : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    0 ≤ directionSq H v :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem continuous_directionSq (v : Fin n → ℝ) :
    Continuous (fun H : Matrix (Fin n) (Fin n) ℝ ↦ directionSq H v) := by
  unfold directionSq
  exact continuous_finsetSum _ fun a _ ↦
    ((continuous_apply a).comp
      (continuous_id.matrix_transpose.matrix_mulVec continuous_const)).pow 2

def rowDirection (i : Fin n) (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b ↦ if a = i then v b else 0

theorem rowDirection_mul_apply (i : Fin n) (v : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    (rowDirection i v * H) a b = if a = i then (H.transpose *ᵥ v) b else 0 := by
  by_cases h : a = i <;>
    simp [rowDirection, Matrix.mul_apply, Matrix.mulVec, dotProduct, h, mul_comm]

theorem frob_rowDirection (i : Fin n) (v : Fin n → ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ) :
    ReactionZero.frob (rowDirection i v) R = ∑ a, v a * R i a := by
  unfold ReactionZero.frob
  rw [Finset.sum_eq_single i]
  · simp [rowDirection]
  · intro a _ ha
    simp [rowDirection, ha]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem frob_gram_rowDirection (i : Fin n) (v : Fin n → ℝ)
    (H G : Matrix (Fin n) (Fin n) ℝ) :
    ReactionZero.frob (gram (rowDirection i v * H)) G = G i i * directionSq H v := by
  have key : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (a c : Fin n),
      gram X a c = ∑ b, X a b * X c b := by
    intro X a c
    simp [gram, Matrix.mul_apply]
  have hg : ∀ a c, gram (rowDirection i v * H) a c =
      if a = i ∧ c = i then directionSq H v else 0 := by
    intro a c
    rw [key]
    simp only [rowDirection_mul_apply]
    by_cases ha : a = i <;> by_cases hc : c = i <;>
      simp [ha, hc, directionSq, pow_two]
  unfold ReactionZero.frob
  simp only [hg]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp only [ite_true, and_self, mul_comm]
    · intro c _ hc
      simp [hc]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · intro a _ ha
    simp [ha]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem reaction_direction_sq_le_trace (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (a : Coord n k → ℝ)
    (hsym : (ReactionZero.mass a).IsHermitian)
    (hfin : ReactionZero.cost L H a ≠ ⊤) (v : Fin n → ℝ) (i : Fin n) :
    (∑ b, v b * ReactionZero.reaction a i b) ^ 2 ≤
      2 * (ReactionZero.cost L H a).toReal *
        ((ReactionZero.mass a).trace * directionSq H v) := by
  have h := reaction_pairing_sq_le L H a hfin (rowDirection i v)
  rw [frob_rowDirection, frob_gram_rowDirection] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mass_diag_le_trace L H a hsym hfin i)
      (directionSq_nonneg H v)) (by positivity))

section Measures

variable {Q : Type*} [MeasurableSpace Q]

/-- The actual i-th coordinate of the matrix signed measure `R v`. -/
def reactionDirection (μ : Coord n k → SignedMeasure Q) (v : Fin n → ℝ)
    (i : Fin n) : SignedMeasure Q :=
  ∑ a, v a • μ (Sum.inr (Sum.inr (i, a)))

def reactionDirectionDensity (μ : Coord n k → SignedMeasure Q) (v : Fin n → ℝ)
    (i : Fin n) (x : Q) : ℝ :=
  ∑ a, v a * ReactionZero.density μ x (Sum.inr (Sum.inr (i, a)))

theorem reactionDirectionDensity_integrable (μ : Coord n k → SignedMeasure Q)
    (v : Fin n → ℝ) (i : Fin n) :
    Integrable (reactionDirectionDensity μ v i) (jointReference μ) := by
  apply integrable_finsetSum
  intro a _
  exact (integrable_rnDeriv_jointReference μ _).const_mul (v a)

theorem withDensity_finiteSum {ι : Type*} [Fintype ι] (ρ : Measure Q)
    (f : ι → Q → ℝ) (hf : ∀ i, Integrable (f i) ρ) :
    ρ.withDensityᵥ (fun x ↦ ∑ i, f i x) = ∑ i, ρ.withDensityᵥ (f i) := by
  classical
  have hs : ∀ s : Finset ι, ρ.withDensityᵥ (fun x ↦ ∑ i ∈ s, f i x) =
      ∑ i ∈ s, ρ.withDensityᵥ (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      change ρ.withDensityᵥ (0 : Q → ℝ) = 0
      exact withDensityᵥ_zero
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [withDensityᵥ_add' (hf i) (integrable_finsetSum s fun a _ ↦ hf a), ih]
  simpa using hs Finset.univ

/-- A proved RN representation of the genuine signed linear combination, not an assumption. -/
theorem withDensity_reactionDirection (μ : Coord n k → SignedMeasure Q)
    (v : Fin n → ℝ) (i : Fin n) :
    (jointReference μ).withDensityᵥ (reactionDirectionDensity μ v i) =
      reactionDirection μ v i := by
  change (jointReference μ).withDensityᵥ
    (fun x ↦ ∑ a, v a * ReactionZero.density μ x (Sum.inr (Sum.inr (i, a)))) = _
  rw [withDensity_finiteSum]
  · unfold reactionDirection
    apply Finset.sum_congr rfl
    intro a _
    have hs : (jointReference μ).withDensityᵥ
        (fun x ↦ v a * ReactionZero.density μ x (Sum.inr (Sum.inr (i, a)))) =
        v a • (jointReference μ).withDensityᵥ
          (fun x ↦ ReactionZero.density μ x (Sum.inr (Sum.inr (i, a)))) := by
      simpa only [smul_eq_mul] using
        (withDensityᵥ_smul' (μ := jointReference μ)
          (fun x ↦ ReactionZero.density μ x (Sum.inr (Sum.inr (i, a)))) (v a))
    exact hs.trans (congrArg (fun s : SignedMeasure Q ↦ v a • s)
      (withDensityᵥ_rnDeriv_jointReference μ (Sum.inr (Sum.inr (i, a)))))
  · intro a
    exact (integrable_rnDeriv_jointReference μ _).const_mul (v a)

theorem reactionDirectionTV_eq_integral_abs (μ : Coord n k → SignedMeasure Q)
    (v : Fin n → ℝ) (i : Fin n) :
    ((reactionDirection μ v i).totalVariation univ).toReal =
      ∫ x, |reactionDirectionDensity μ v i x| ∂jointReference μ := by
  rw [SignedMeasure.totalVariation_eq_variation]
  have h := Measure.variation_withDensityᵥ (reactionDirectionDensity_integrable μ v i)
  rw [withDensity_reactionDirection] at h
  rw [h, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simpa only [Real.norm_eq_abs] using
    (integral_norm_eq_lintegral_enorm
      (reactionDirectionDensity_integrable μ v i).aestronglyMeasurable).symm

/-- The actual directional reaction variation satisfies the sharp weight-direction estimate. -/
theorem reactionDirectionTV_sq_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : ReactionZero.action L H μ ≠ ⊤) (v : Fin n → ℝ) (i : Fin n) :
    ((reactionDirection μ v i).totalVariation univ).toReal ^ 2 ≤
      2 * (ReactionZero.action L H μ).toReal *
        (PathCoercivity.pathTrace μ * directionSq H v) := by
  rw [reactionDirectionTV_eq_integral_abs]
  have h := PathCoercivity.integral_abs_square_bound
    (reactionDirectionDensity_integrable μ v i)
    (PathCoercivity.integrable_mass_trace μ)
    (PathCoercivity.integrable_cost_toReal L H μ hfin)
    (directionSq_nonneg H v)
    ((PathCoercivity.ae_mass_posSemidef L H μ hsym hfin).mono fun _ hx ↦
      trace_nonneg_of_posSemidef hx)
    (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
    ((PathCoercivity.ae_cost_ne_top L H μ hfin).mono fun x hx ↦
      reaction_direction_sq_le_trace L H (ReactionZero.density μ x)
        (PathCoercivity.mass_density_isHermitian μ hsym x) hx v i)
  simpa only [PathCoercivity.integral_cost_toReal L H μ hfin,
    PathCoercivity.pathTrace, reactionDirectionDensity, ReactionZero.reaction] using h

/-- Uniform energy and trace bounds supply an explicit directional reaction TV bound. -/
theorem reactionDirectionTV_le_sqrt (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : ReactionZero.action L H μ ≠ ⊤) (C M : ℝ)
    (hE : (ReactionZero.action L H μ).toReal ≤ C)
    (hT : PathCoercivity.pathTrace μ ≤ M) (v : Fin n → ℝ) (i : Fin n) :
    ((reactionDirection μ v i).totalVariation univ).toReal ≤
      Real.sqrt (directionSq H v) * Real.sqrt (2 * C * M) := by
  apply reaction_bound_of_square ENNReal.toReal_nonneg (Real.sqrt_nonneg _)
    ENNReal.toReal_nonneg (PathCoercivity.pathTrace_nonneg L H μ hsym hfin) hE hT
  rw [Real.sq_sqrt (directionSq_nonneg H v)]
  convert reactionDirectionTV_sq_le L H μ hsym hfin v i using 1
  ring

/-- Every fixed direction in the target transpose-kernel has vanishing reaction variation.
The matrices need neither share eigenvectors nor be positive definite. -/
theorem reactionDirectionTV_toReal_tendsto_zero
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (μ : ℕ → Coord n k → SignedMeasure Q)
    (hsym : ∀ a i j, μ a (Sum.inl (i, j)) = μ a (Sum.inl (j, i)))
    (hfin : ∀ a, ReactionZero.action L (H a) (μ a) ≠ ⊤) (C M : ℝ)
    (hE : ∀ a, (ReactionZero.action L (H a) (μ a)).toReal ≤ C)
    (hT : ∀ a, PathCoercivity.pathTrace (μ a) ≤ M)
    (v : Fin n → ℝ) (hv : Hstar.transpose *ᵥ v = 0) (i : Fin n) :
    Tendsto (fun a ↦ ((reactionDirection (μ a) v i).totalVariation univ).toReal)
      atTop (𝓝 0) := by
  have hd : Tendsto (fun a ↦ directionSq (H a) v) atTop (𝓝 0) := by
    simpa only [Function.comp_def, directionSq, hv, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero] using (continuous_directionSq v).tendsto Hstar |>.comp hH
  have hsq : Tendsto (fun a ↦ Real.sqrt (directionSq (H a) v)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hd
  have hb : Tendsto (fun a ↦ Real.sqrt (directionSq (H a) v) *
      Real.sqrt (2 * C * M)) atTop (𝓝 0) := by
    simpa using hsq.mul_const (Real.sqrt (2 * C * M))
  exact squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg)
    (fun a ↦ reactionDirectionTV_le_sqrt L (H a) (μ a) (hsym a) (hfin a) C M
      (hE a) (hT a) v i) hb

theorem reactionDirectionTV_tendsto_zero
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (μ : ℕ → Coord n k → SignedMeasure Q)
    (hsym : ∀ a i j, μ a (Sum.inl (i, j)) = μ a (Sum.inl (j, i)))
    (hfin : ∀ a, ReactionZero.action L (H a) (μ a) ≠ ⊤) (C M : ℝ)
    (hE : ∀ a, (ReactionZero.action L (H a) (μ a)).toReal ≤ C)
    (hT : ∀ a, PathCoercivity.pathTrace (μ a) ≤ M)
    (v : Fin n → ℝ) (hv : Hstar.transpose *ᵥ v = 0) (i : Fin n) :
    Tendsto (fun a ↦ (reactionDirection (μ a) v i).totalVariation univ)
      atTop (𝓝 0) :=
  (ENNReal.tendsto_toReal_zero_iff (fun _ ↦ measure_ne_top _ _)).1
    (reactionDirectionTV_toReal_tendsto_zero L H Hstar hH μ hsym hfin C M hE hT v hv i)

/-- The directional rate on an actual time-CE sublevel derives its trace bound from the
continuity equation; no variation or trace bound is inserted as a premise. -/
theorem reactionDirectionTV_le_on_sublevel (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (C K : ℝ) (hC : 0 ≤ C) (hE : ReactionZero.action L H μ ≤ ENNReal.ofReal C)
    (hH : frobeniusSq H ≤ K) (w : Q → ℝ)
    (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (m0 : ℝ) (hm0 : 0 ≤ m0)
    (hCE : PathCoercivity.pathTrace μ =
      m0 + ∑ a, signedPair (μ (Sum.inr (Sum.inr (a, a)))) w)
    (v : Fin n → ℝ) (i : Fin n) :
    ((reactionDirection μ v i).totalVariation univ).toReal ≤
      Real.sqrt (directionSq H v) * Real.sqrt (2 * C * (2 * m0 + 2 * K * C)) := by
  exact reactionDirectionTV_le_sqrt L H μ hsym
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE) C (2 * m0 + 2 * K * C)
    (ENNReal.toReal_le_of_le_ofReal hC hE)
    (PathCoercivity.pathTrace_bound_on_sublevel L H μ hsym C K hC hE hH
      w hwM hw m0 hm0 hCE) v i

/-- Fixed transpose-kernel directions vanish on bounded action sublevels satisfying the
actual time-CE identity, with the required trace bound proved from that identity. -/
theorem reactionDirectionTV_tendsto_zero_on_sublevel
    (L : Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (μ : ℕ → Coord n k → SignedMeasure Q)
    (hsym : ∀ a i j, μ a (Sum.inl (i, j)) = μ a (Sum.inl (j, i)))
    (C K : ℝ) (hC : 0 ≤ C)
    (hE : ∀ a, ReactionZero.action L (H a) (μ a) ≤ ENNReal.ofReal C)
    (hBound : ∀ a, frobeniusSq (H a) ≤ K)
    (w : Q → ℝ) (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (m0 : ℝ) (hm0 : 0 ≤ m0)
    (hCE : ∀ a, PathCoercivity.pathTrace (μ a) =
      m0 + ∑ b, signedPair (μ a (Sum.inr (Sum.inr (b, b)))) w)
    (v : Fin n → ℝ) (hv : Hstar.transpose *ᵥ v = 0) (i : Fin n) :
    Tendsto (fun a ↦ (reactionDirection (μ a) v i).totalVariation univ)
      atTop (𝓝 0) := by
  exact reactionDirectionTV_tendsto_zero L H Hstar hH μ hsym
    (fun a ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hE a)) C
    (2 * m0 + 2 * K * C)
    (fun a ↦ ENNReal.toReal_le_of_le_ofReal hC (hE a))
    (fun a ↦ PathCoercivity.pathTrace_bound_on_sublevel L (H a) (μ a) (hsym a)
      C K hC (hE a) (hBound a) w hwM hw m0 hm0 (hCE a)) v hv i

end Measures

end MatrixTransport.PartialReaction

#print axioms MatrixTransport.PartialReaction.withDensity_reactionDirection
#print axioms MatrixTransport.PartialReaction.reactionDirectionTV_sq_le
#print axioms MatrixTransport.PartialReaction.reactionDirectionTV_tendsto_zero
#print axioms MatrixTransport.PartialReaction.reactionDirectionTV_tendsto_zero_on_sublevel
