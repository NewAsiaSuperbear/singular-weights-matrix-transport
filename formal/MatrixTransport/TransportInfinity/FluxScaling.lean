import MatrixTransport.ReactionZero.WeightedAction

/-!
# Exact flux scaling for the original weighted support action

All statements concern the original finite-coordinate support action and its genuine signed
measure RN integral. The base transport weight may be singular. No inverse transport matrix,
PSD mass hypothesis, or analytic compactness assumption is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.TransportInfinity

open MatrixTransport.ReactionZero

variable {n k : ℕ}

/-- Scale only the full flux coordinates of a primal or dual triple. -/
def fluxScale (s : ℝ) (v : Coord n k → ℝ) : Coord n k → ℝ :=
  ReactionZero.pack (ReactionZero.mass v) (s • ReactionZero.flux v) (ReactionZero.reaction v)

/-- Retain the original mass and reaction coordinates, dropping the flux density. -/
def dropFlux (v : Coord n k → ℝ) : Coord n k → ℝ := fluxScale 0 v

@[simp] theorem mass_fluxScale (s : ℝ) (v : Coord n k → ℝ) :
    ReactionZero.mass (fluxScale s v) = ReactionZero.mass v := rfl

@[simp] theorem flux_fluxScale (s : ℝ) (v : Coord n k → ℝ) :
    ReactionZero.flux (fluxScale s v) = s • ReactionZero.flux v := rfl

@[simp] theorem reaction_fluxScale (s : ℝ) (v : Coord n k → ℝ) :
    ReactionZero.reaction (fluxScale s v) = ReactionZero.reaction v := rfl

@[simp] theorem fluxScale_one (v : Coord n k → ℝ) : fluxScale 1 v = v := by
  simp only [fluxScale, one_smul, ReactionZero.pack_unpack]

theorem fluxScale_comp (s t : ℝ) (v : Coord n k → ℝ) :
    fluxScale s (fluxScale t v) = fluxScale (s * t) v := by
  simp only [fluxScale, ReactionZero.mass_pack, ReactionZero.flux_pack,
    ReactionZero.reaction_pack, smul_smul]

theorem weightedPair_fluxScale (s : ℝ) (a v : Coord n k → ℝ) :
    weightedPair (fun _ ↦ 1) (fluxScale s a) v =
      weightedPair (fun _ ↦ 1) a (fluxScale s v) := by
  rw [ReactionZero.weightedPair_expand, ReactionZero.weightedPair_expand]
  simp only [mass_fluxScale, flux_fluxScale, reaction_fluxScale, Matrix.smul_apply, smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact transport scaling of the full quadratic dual test set. -/
theorem mem_dualSet_scaled_iff (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (a : Coord n k → ℝ) :
    a ∈ ReactionZero.dualSet (t • L) H ↔ fluxScale t a ∈ ReactionZero.dualSet L H := by
  simp only [ReactionZero.dualSet, Set.mem_ofPred_eq, mass_fluxScale, flux_fluxScale,
    reaction_fluxScale, Matrix.smul_mul, Matrix.mul_smul]

/-- The original local cost at `t L` equals the base local cost with flux density divided
by `t`. This holds for every nonzero scalar and all extended-valued costs. -/
theorem cost_scaled_eq (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (ht : t ≠ 0) (v : Coord n k → ℝ) :
    ReactionZero.cost (t • L) H v = ReactionZero.cost L H (fluxScale (1 / t) v) := by
  apply le_antisymm
  · apply iSup₂_le
    intro a ha
    have hm := (mem_dualSet_scaled_iff L H t a).mp ha
    have hp : weightedPair (fun _ ↦ 1) (fluxScale t a) (fluxScale (1 / t) v) =
        weightedPair (fun _ ↦ 1) a v := by
      rw [weightedPair_fluxScale, fluxScale_comp]
      simp [ht]
    rw [← hp]
    exact cost_fenchel L H (fluxScale (1 / t) v) (fluxScale t a) hm
  · apply iSup₂_le
    intro a ha
    have hm : fluxScale (1 / t) a ∈ ReactionZero.dualSet (t • L) H := by
      apply (mem_dualSet_scaled_iff L H t _).mpr
      simpa only [fluxScale_comp, one_div, mul_inv_cancel₀ ht, fluxScale_one] using ha
    rw [← weightedPair_fluxScale]
    exact cost_fenchel (t • L) H v (fluxScale (1 / t) a) hm

/-- Dropping a dual flux preserves admissibility at any transport weight. -/
theorem dropFlux_mem_dualSet (L K : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (a : Coord n k → ℝ)
    (ha : a ∈ ReactionZero.dualSet L H) :
    dropFlux a ∈ ReactionZero.dualSet K H := by
  obtain ⟨hs, hp⟩ := ha
  refine ⟨by simpa [dropFlux] using hs, ?_⟩
  change (-ReactionZero.mass a - (1 / 2 : ℝ) • ReactionZero.gram
      (((0 : ℝ) • ReactionZero.flux a) * K) -
      (1 / 2 : ℝ) • ReactionZero.gram (ReactionZero.reaction a * H)).PosSemidef
  have heq : -ReactionZero.mass a - (1 / 2 : ℝ) • ReactionZero.gram
      (((0 : ℝ) • ReactionZero.flux a) * K) -
        (1 / 2 : ℝ) • ReactionZero.gram (ReactionZero.reaction a * H) =
      (-ReactionZero.mass a - (1 / 2 : ℝ) • ReactionZero.gram (ReactionZero.flux a * L) -
        (1 / 2 : ℝ) • ReactionZero.gram (ReactionZero.reaction a * H)) +
        (1 / 2 : ℝ) • ReactionZero.gram (ReactionZero.flux a * L) := by
    simp only [zero_smul, Matrix.zero_mul, ReactionZero.gram, Matrix.transpose_zero, smul_zero]
    module
  rw [heq]
  exact hp.add ((posSemidef_gram (ReactionZero.flux a * L)).smul (by norm_num))

/-- The flux-free cost does not depend on which finite transport weight is used. -/
theorem cost_dropFlux_eq (L K : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) :
    ReactionZero.cost L H (dropFlux v) = ReactionZero.cost K H (dropFlux v) := by
  have hle (L K : Matrix (Fin k) (Fin k) ℝ) :
      ReactionZero.cost L H (dropFlux v) ≤ ReactionZero.cost K H (dropFlux v) := by
    apply iSup₂_le
    intro a ha
    have hp : weightedPair (fun _ ↦ 1) (dropFlux a) (dropFlux v) =
        weightedPair (fun _ ↦ 1) a (dropFlux v) := by
      unfold dropFlux
      rw [weightedPair_fluxScale, fluxScale_comp]
      simp
    rw [← hp]
    exact cost_fenchel K H (dropFlux v) (dropFlux a) (dropFlux_mem_dualSet L K H a ha)
  exact le_antisymm (hle L K) (hle K L)

/-- The original current-weight cost always dominates its flux-free density cost. -/
theorem cost_dropFlux_le (L K : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) :
    ReactionZero.cost L H (dropFlux v) ≤ ReactionZero.cost K H v := by
  apply iSup₂_le
  intro a ha
  change ENNReal.ofReal (weightedPair (fun _ ↦ 1) a (fluxScale 0 v)) ≤ _
  rw [← weightedPair_fluxScale]
  exact cost_fenchel K H v (dropFlux a) (dropFlux_mem_dualSet L K H a ha)

theorem weightedPair_add_right {ι : Type*} [Fintype ι]
    (coeff : ι → ℝ) (a u v : ι → ℝ) :
    weightedPair coeff a (u + v) = weightedPair coeff a u + weightedPair coeff a v := by
  unfold weightedPair
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Support-cost subadditivity is proved directly from the original support supremum. -/
theorem cost_add_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (u v : Coord n k → ℝ) :
    ReactionZero.cost L H (u + v) ≤ ReactionZero.cost L H u + ReactionZero.cost L H v := by
  apply iSup₂_le
  intro a ha
  rw [weightedPair_add_right]
  exact ENNReal.ofReal_add_le.trans
    (add_le_add (cost_fenchel L H u a ha) (cost_fenchel L H v a ha))

theorem fluxScale_convexCombination (s : ℝ) (v : Coord n k → ℝ) :
    fluxScale s v = (1 - s) • dropFlux v + s • v := by
  funext c
  rcases c with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ <;>
    simp [fluxScale, dropFlux, ReactionZero.pack, ReactionZero.mass,
      ReactionZero.flux, ReactionZero.reaction, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    <;> ring

/-- The upper cost bound for a convexly suppressed flux density. -/
theorem cost_fluxScale_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (hs : 0 ≤ s) (hsone : s ≤ 1)
    (v : Coord n k → ℝ) :
    ReactionZero.cost L H (fluxScale s v) ≤
      ReactionZero.cost L H (dropFlux v) + ENNReal.ofReal s * ReactionZero.cost L H v := by
  rw [fluxScale_convexCombination]
  have h := cost_add_le L H ((1 - s) • dropFlux v) (s • v)
  rw [cost_smul_nonneg L H _ (sub_nonneg.mpr hsone), cost_smul_nonneg L H _ hs] at h
  apply h.trans
  apply add_le_add
  · calc
      ENNReal.ofReal (1 - s) * ReactionZero.cost L H (dropFlux v)
          ≤ 1 * ReactionZero.cost L H (dropFlux v) := by
        exact mul_le_mul_left
          ((ENNReal.ofReal_le_ofReal (by linarith : 1 - s ≤ 1)).trans_eq ENNReal.ofReal_one) _
      _ = _ := one_mul _
  · rfl

/-- The original local scaled cost lies between its flux-free cost and the explicit
baseline-cost comparison, including infinite costs. -/
theorem cost_scaled_sandwich (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (ht : 1 ≤ t) (v : Coord n k → ℝ) :
    ReactionZero.cost L H (dropFlux v) ≤ ReactionZero.cost (t • L) H v ∧
    ReactionZero.cost (t • L) H v ≤
      ReactionZero.cost L H (dropFlux v) + ENNReal.ofReal (1 / t) * ReactionZero.cost L H v := by
  refine ⟨cost_dropFlux_le L (t • L) H v, ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  rw [cost_scaled_eq L H t htpos.ne']
  exact cost_fluxScale_le L H (1 / t) (by positivity) (by
    exact (div_le_one htpos).mpr ht) v

theorem gram_smul {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℝ) (α : ℝ) :
    ReactionZero.gram (α • X) = (α * α) • ReactionZero.gram X := by
  simp only [ReactionZero.gram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]

/-- Scaling a base dual triple by `α` preserves admissibility at `t L` when both resulting
quadratic slacks are nonnegative. This is a concrete finite-domain estimate. -/
theorem smul_mem_dualSet_transport (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (t α : ℝ)
    (hα : 0 ≤ α) (hαone : α ≤ 1) (hαt : α * t ^ 2 ≤ 1)
    (a : Coord n k → ℝ) (ha : a ∈ ReactionZero.dualSet L H) :
    α • a ∈ ReactionZero.dualSet (t • L) H := by
  obtain ⟨hs, hp⟩ := ha
  refine ⟨?_, ?_⟩
  · change (α • ReactionZero.mass a).IsHermitian
    exact hs.smul (by rfl : IsSelfAdjoint α)
  · have hm : ReactionZero.mass (α • a) = α • ReactionZero.mass a := rfl
    have hf : ReactionZero.flux (α • a) = α • ReactionZero.flux a := rfl
    have hr : ReactionZero.reaction (α • a) = α • ReactionZero.reaction a := rfl
    have heq : -ReactionZero.mass (α • a) -
          (1 / 2 : ℝ) • ReactionZero.gram (ReactionZero.flux (α • a) * (t • L)) -
          (1 / 2 : ℝ) • ReactionZero.gram (ReactionZero.reaction (α • a) * H) =
        α • (-ReactionZero.mass a - (1 / 2 : ℝ) • ReactionZero.gram
          (ReactionZero.flux a * L) - (1 / 2 : ℝ) • ReactionZero.gram
          (ReactionZero.reaction a * H)) +
        (α * (1 - α * t ^ 2) / 2) • ReactionZero.gram (ReactionZero.flux a * L) +
        (α * (1 - α) / 2) • ReactionZero.gram (ReactionZero.reaction a * H) := by
      rw [hm, hf, hr]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, gram_smul]
      module
    rw [heq]
    exact ((hp.smul hα).add
      ((posSemidef_gram (ReactionZero.flux a * L)).smul (by positivity))).add
        ((posSemidef_gram (ReactionZero.reaction a * H)).smul (by positivity))

/-- The finite baseline is controlled by the actual large-transport-weight cost. -/
theorem baseline_cost_le_scaled (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (ht : 1 ≤ t) (v : Coord n k → ℝ) :
    ReactionZero.cost L H v ≤ ENNReal.ofReal (t ^ 2) * ReactionZero.cost (t • L) H v := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
  have hαone : (1 : ℝ) / t ^ 2 ≤ 1 := by
    apply (div_le_one ht2).mpr
    nlinarith
  have hαt : ((1 : ℝ) / t ^ 2) * t ^ 2 ≤ 1 := by
    rw [div_mul_cancel₀ 1 ht2.ne']
  apply iSup₂_le
  intro a ha
  have hm := smul_mem_dualSet_transport L H t (1 / t ^ 2)
    (by positivity) hαone hαt a ha
  have hs := cost_fenchel (t • L) H v ((1 / t ^ 2) • a) hm
  have hp : weightedPair (fun _ ↦ 1) ((1 / t ^ 2) • a) v =
      (1 / t ^ 2) * weightedPair (fun _ ↦ 1) a v := by
    unfold weightedPair
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hp, ENNReal.ofReal_mul (by positivity : 0 ≤ (1 : ℝ) / t ^ 2)] at hs
  calc ENNReal.ofReal (weightedPair (fun _ ↦ 1) a v)
      = ENNReal.ofReal (t ^ 2) *
          (ENNReal.ofReal (1 / t ^ 2) * ENNReal.ofReal (weightedPair (fun _ ↦ 1) a v)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg t)]
        simp [ht2.ne']
      _ ≤ _ := mul_le_mul_right hs _

section Measures

variable {Q : Type*} [MeasurableSpace Q]

/-- The flux-free action density is evaluated against the **original** path's joint RN
reference. No changed-reference or projected-measure identity is postulated. -/
def freeTransportAction (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q) : ℝ≥0∞ :=
  ∫⁻ x, ReactionZero.cost L H (dropFlux (ReactionZero.density μ x)) ∂jointReference μ

theorem measurable_dropFlux_density (μ : Coord n k → SignedMeasure Q) :
    Measurable (fun x ↦ dropFlux (ReactionZero.density μ x)) := by
  apply measurable_pi_iff.mpr
  intro c
  rcases c with a | a | a
  · exact measurable_rnDeriv_jointReference μ (Sum.inl a)
  · change Measurable (fun x ↦ (0 : ℝ) *
      (μ (Sum.inr (Sum.inl a))).rnDeriv (jointReference μ) x)
    exact measurable_const.mul (measurable_rnDeriv_jointReference μ (Sum.inr (Sum.inl a)))
  · exact measurable_rnDeriv_jointReference μ (Sum.inr (Sum.inr a))

theorem measurable_freeTransport_integrand (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q) :
    Measurable (fun x ↦ ReactionZero.cost L H (dropFlux (ReactionZero.density μ x))) :=
  (measurable_cost L H).comp (measurable_dropFlux_density μ)

/-- Exact integrated flux scaling, retaining the original path and reference measure. -/
theorem action_scaled_eq (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (ht : t ≠ 0)
    (μ : Coord n k → SignedMeasure Q) :
    ReactionZero.action (t • L) H μ =
      ∫⁻ x, ReactionZero.cost L H (fluxScale (1 / t) (ReactionZero.density μ x))
        ∂jointReference μ := by
  unfold ReactionZero.action
  congr 1
  funext x
  exact cost_scaled_eq L H t ht (ReactionZero.density μ x)

theorem freeTransportAction_eq (L K : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q) :
    freeTransportAction L H μ = freeTransportAction K H μ := by
  unfold freeTransportAction
  congr 1
  funext x
  exact cost_dropFlux_eq L K H (ReactionZero.density μ x)

/-- The actual flux-free RN action is a lower bound at every finite transport weight. -/
theorem freeTransportAction_le_action (L K : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q) :
    freeTransportAction L H μ ≤ ReactionZero.action K H μ :=
  lintegral_mono fun x ↦ cost_dropFlux_le L K H (ReactionZero.density μ x)

/-- The exact measure-action sandwich needed for the free-transport ray limit. -/
theorem action_transport_sandwich (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (ht : 1 ≤ t)
    (μ : Coord n k → SignedMeasure Q) :
    freeTransportAction L H μ ≤ ReactionZero.action (t • L) H μ ∧
    ReactionZero.action (t • L) H μ ≤ freeTransportAction L H μ +
      ENNReal.ofReal (1 / t) * ReactionZero.action L H μ := by
  refine ⟨freeTransportAction_le_action L (t • L) H μ, ?_⟩
  calc ReactionZero.action (t • L) H μ
      ≤ ∫⁻ x, ReactionZero.cost L H (dropFlux (ReactionZero.density μ x)) +
          ENNReal.ofReal (1 / t) * ReactionZero.cost L H (ReactionZero.density μ x)
          ∂jointReference μ :=
        lintegral_mono fun x ↦ (cost_scaled_sandwich L H t ht (ReactionZero.density μ x)).2
      _ = _ := by
        rw [lintegral_add_left (measurable_freeTransport_integrand L H μ),
          lintegral_const_mul _ (measurable_cost_density L H μ)]
        rfl

/-- A current finite ray-weight action controls the genuine baseline action. -/
theorem baseline_action_le_scaled (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (ht : 1 ≤ t)
    (μ : Coord n k → SignedMeasure Q) :
    ReactionZero.action L H μ ≤ ENNReal.ofReal (t ^ 2) * ReactionZero.action (t • L) H μ := by
  calc ReactionZero.action L H μ
      ≤ ∫⁻ x, ENNReal.ofReal (t ^ 2) *
          ReactionZero.cost (t • L) H (ReactionZero.density μ x) ∂jointReference μ :=
        lintegral_mono fun x ↦ baseline_cost_le_scaled L H t ht (ReactionZero.density μ x)
      _ = _ := lintegral_const_mul _ (measurable_cost_density (t • L) H μ)

/-- Every finite positive large transport scaling has exactly the same finite-action
domain as the baseline; this is proved for the actual signed-measure action. -/
theorem action_ne_top_iff (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (ht : 1 ≤ t)
    (μ : Coord n k → SignedMeasure Q) :
    ReactionZero.action (t • L) H μ ≠ ⊤ ↔ ReactionZero.action L H μ ≠ ⊤ := by
  constructor
  · intro h
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h)
      (baseline_action_le_scaled L H t ht μ)
  · intro h
    have hF : freeTransportAction L H μ ≠ ⊤ :=
      ne_top_of_le_ne_top h (freeTransportAction_le_action L L H μ)
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨hF, ENNReal.mul_ne_top ENNReal.ofReal_ne_top h⟩)
      (action_transport_sandwich L H t ht μ).2

theorem action_eq_top_iff (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (ht : 1 ≤ t)
    (μ : Coord n k → SignedMeasure Q) :
    ReactionZero.action (t • L) H μ = ⊤ ↔ ReactionZero.action L H μ = ⊤ := by
  simpa only [not_not] using not_congr (action_ne_top_iff L H t ht μ)

end Measures

end MatrixTransport.TransportInfinity

#print axioms MatrixTransport.TransportInfinity.cost_scaled_eq
#print axioms MatrixTransport.TransportInfinity.cost_dropFlux_le
#print axioms MatrixTransport.TransportInfinity.action_transport_sandwich
#print axioms MatrixTransport.TransportInfinity.baseline_action_le_scaled
#print axioms MatrixTransport.TransportInfinity.action_ne_top_iff
