import MatrixTransport.ReactionZero.MassScaling
import MatrixTransport.EntrywiseBures.ReactionPiece

/-!
# Exact scaling, flux reversal and injective time pushforwards of actual paths

The formulas use the original signed-coordinate action with its recomputed joint RN
reference. Density representations and exact support homogeneity prove the identities.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.EntrywiseBures

open MatrixTransport.ReactionZero

section Push

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem pushSigned_comp {T : X → Y} {S : Y → Z}
    (hT : Measurable T) (hS : Measurable S) (μ : SignedMeasure X) :
    pushSigned S (pushSigned T μ) = pushSigned (S ∘ T) μ := by
  ext B hB
  rw [pushSigned_apply hS _ hB, pushSigned_apply hT _ (hS hB),
    pushSigned_apply (hS.comp hT) _ hB]
  rfl

theorem pushSigned_id (μ : SignedMeasure X) : pushSigned id μ = μ := by
  ext B hB
  rw [pushSigned_apply measurable_id _ hB]
  rfl

theorem pushPath_comp {ι : Type*} {T : X → Y} {S : Y → Z}
    (hT : Measurable T) (hS : Measurable S) (μ : ι → SignedMeasure X) :
    pushPath S (pushPath T μ) = pushPath (S ∘ T) μ := by
  funext c
  exact pushSigned_comp hT hS (μ c)

theorem pushSigned_smul {T : X → Y} (hT : Measurable T) (r : ℝ) (μ : SignedMeasure X) :
    pushSigned T (r • μ) = r • pushSigned T μ := by
  ext B hB
  rw [pushSigned_apply hT _ hB, _root_.smul_apply,
    _root_.smul_apply, pushSigned_apply hT _ hB]

theorem pushSigned_neg {T : X → Y} (hT : Measurable T) (μ : SignedMeasure X) :
    pushSigned T (-μ) = -pushSigned T μ := by
  ext B hB
  rw [pushSigned_apply hT _ hB]
  simp only [VectorMeasure.neg_apply]
  rw [pushSigned_apply hT _ hB]

end Push

section Action

variable {X Y : Type*} [MeasurableSpace X] [MetricSpace X] [CompactSpace X] [BorelSpace X]
  [MeasurableSpace Y] [MetricSpace Y] [CompactSpace Y] [BorelSpace Y] {n k : ℕ}

theorem action_pushPath_eq_of_leftInverse
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    {T : X → Y} {S : Y → X} (hT : Continuous T) (hS : Continuous S)
    (hST : Function.LeftInverse S T) (μ : Coord n k → SignedMeasure X) :
    action L H (pushPath T μ) = action L H μ := by
  apply le_antisymm (action_pushPath_le L H hT μ)
  have h := action_pushPath_le L H hS (pushPath T μ)
  rw [pushPath_comp hT.measurable hS.measurable] at h
  have he : S ∘ T = id := funext hST
  rw [he] at h
  have hi : pushPath id μ = μ := funext fun c ↦ pushSigned_id (μ c)
  rwa [hi] at h

def scaleMassPath (r : ℝ) (μ : Coord n k → SignedMeasure X) : Coord n k → SignedMeasure X
  | Sum.inl a => r • μ (Sum.inl a)
  | Sum.inr a => μ (Sum.inr a)

def scaleMassDensity (r : ℝ) (v : Coord n k → ℝ) : Coord n k → ℝ
  | Sum.inl a => r * v (Sum.inl a)
  | Sum.inr a => v (Sum.inr a)

theorem scaleMassDensity_eq_pack (r : ℝ) (v : Coord n k → ℝ) :
    scaleMassDensity r v = pack (r • ReactionZero.mass v) (ReactionZero.flux v) (ReactionZero.reaction v) := by
  funext c
  rcases c with a | a | a <;> rfl

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
theorem scaleMassPath_eq_density (r : ℝ) (μ : Coord n k → SignedMeasure X) :
    scaleMassPath r μ = fun c ↦ (jointReference μ).withDensityᵥ
      (fun x ↦ scaleMassDensity r (ReactionZero.density μ x) c) := by
  funext c
  rcases c with a | a
  · change r • μ (Sum.inl a) = (jointReference μ).withDensityᵥ
      (fun x ↦ r * (μ (Sum.inl a)).rnDeriv (jointReference μ) x)
    have h := withDensityᵥ_smul' (μ := jointReference μ)
      (fun x ↦ (μ (Sum.inl a)).rnDeriv (jointReference μ) x) r
    simp only [smul_eq_mul] at h
    rw [h, withDensityᵥ_rnDeriv_jointReference]
  · exact (withDensityᵥ_rnDeriv_jointReference μ (Sum.inr a)).symm

theorem action_scaleMassPath (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure X)
    {r : ℝ} (hr : 0 < r) :
    action L H (scaleMassPath r μ) = ENNReal.ofReal r⁻¹ * action L H μ := by
  have hM : ∀ c, Measurable (fun x ↦ scaleMassDensity r (ReactionZero.density μ x) c) := by
    intro c
    rcases c with a | a
    · exact (measurable_rnDeriv_jointReference μ _).const_mul r
    · exact measurable_rnDeriv_jointReference μ _
  have hI : ∀ c, Integrable (fun x ↦ scaleMassDensity r (ReactionZero.density μ x) c)
      (jointReference μ) := by
    intro c
    rcases c with a | a
    · exact (integrable_rnDeriv_jointReference μ _).const_mul r
    · exact integrable_rnDeriv_jointReference μ _
  rw [scaleMassPath_eq_density r μ, action_densityPath L H _ hM hI]
  calc
    (∫⁻ x, cost L H (fun c ↦ scaleMassDensity r (ReactionZero.density μ x) c) ∂jointReference μ) =
        ∫⁻ x, ENNReal.ofReal r⁻¹ * cost L H (ReactionZero.density μ x) ∂jointReference μ := by
      apply lintegral_congr
      intro x
      rw [scaleMassDensity_eq_pack, cost_pack_smul_mass _ _ _ _ _ hr, pack_unpack]
    _ = _ := lintegral_const_mul _ (measurable_cost_density L H μ)

def reverseFluxPath (μ : Coord n k → SignedMeasure X) : Coord n k → SignedMeasure X
  | Sum.inl a => μ (Sum.inl a)
  | Sum.inr (Sum.inl a) => -μ (Sum.inr (Sum.inl a))
  | Sum.inr (Sum.inr a) => μ (Sum.inr (Sum.inr a))

def reverseFluxDensity (v : Coord n k → ℝ) : Coord n k → ℝ :=
  pack (ReactionZero.mass v) (-ReactionZero.flux v) (ReactionZero.reaction v)

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
theorem reverseFluxPath_eq_density (μ : Coord n k → SignedMeasure X) :
    reverseFluxPath μ = fun c ↦ (jointReference μ).withDensityᵥ
      (fun x ↦ reverseFluxDensity (ReactionZero.density μ x) c) := by
  funext c
  rcases c with a | a | a
  · exact (withDensityᵥ_rnDeriv_jointReference μ _).symm
  · change -μ (Sum.inr (Sum.inl a)) = (jointReference μ).withDensityᵥ
      (fun x ↦ -(μ (Sum.inr (Sum.inl a))).rnDeriv (jointReference μ) x)
    rw [withDensityᵥ_neg', withDensityᵥ_rnDeriv_jointReference]
  · exact (withDensityᵥ_rnDeriv_jointReference μ _).symm

theorem action_reverseFluxPath (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure X) :
    action L H (reverseFluxPath μ) = action L H μ := by
  have hM : ∀ c, Measurable (fun x ↦ reverseFluxDensity (ReactionZero.density μ x) c) := by
    intro c
    rcases c with a | a | a
    · exact measurable_rnDeriv_jointReference μ _
    · exact (measurable_rnDeriv_jointReference μ _).neg
    · exact measurable_rnDeriv_jointReference μ _
  have hI : ∀ c, Integrable (fun x ↦ reverseFluxDensity (ReactionZero.density μ x) c) (jointReference μ) := by
    intro c
    rcases c with a | a | a
    · exact integrable_rnDeriv_jointReference μ _
    · exact (integrable_rnDeriv_jointReference μ _).neg
    · exact integrable_rnDeriv_jointReference μ _
  rw [reverseFluxPath_eq_density μ, action_densityPath L H _ hM hI]
  apply lintegral_congr
  intro x
  rw [reverseFluxDensity, cost_pack_neg_flux, pack_unpack]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [BorelSpace Y] in
theorem scaleMassPath_pushPath (r : ℝ) {T : X → Y} (hT : Measurable T)
    (μ : Coord n k → SignedMeasure X) :
    scaleMassPath r (pushPath T μ) = pushPath T (scaleMassPath r μ) := by
  funext c
  rcases c with a | a
  · exact (pushSigned_smul hT r (μ (Sum.inl a))).symm
  · rfl

omit [MetricSpace X] [CompactSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [BorelSpace Y] in
theorem reverseFluxPath_pushPath {T : X → Y} (hT : Measurable T)
    (μ : Coord n k → SignedMeasure X) :
    reverseFluxPath (pushPath T μ) = pushPath T (reverseFluxPath μ) := by
  funext c
  rcases c with a | a | a
  · rfl
  · exact (pushSigned_neg hT (μ (Sum.inr (Sum.inl a)))).symm
  · rfl

end Action

section TimeMaps

open MatrixTransport.ReactionZero.ClosedDomain
variable {d n k : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

def timeUnscale (a r : ℝ) : C(ClosedDomain.Q Ω, ClosedDomain.Q Ω) :=
  ⟨fun p ↦ ⟨(max 0 (min 1 ((p.val.1 - a) / r)), p.val.2),
    ⟨⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩, p.property.2⟩⟩,
    ((continuous_const.max (continuous_const.min
      (((continuous_fst.comp continuous_subtype_val).sub continuous_const).div_const r))).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

omit [Fact (IsCompact Ω)] in
theorem timeUnscale_leftInverse {a r : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    Function.LeftInverse (timeUnscale (Ω := Ω) a r) (timeScale a r ha hab hr) := by
  intro p
  apply Subtype.ext
  apply Prod.ext
  · change max 0 (min 1 ((a + r * p.val.1 - a) / r)) = p.val.1
    have he : (a + r * p.val.1 - a) / r = p.val.1 := by field_simp; ring
    rw [he, min_eq_right p.property.1.2, max_eq_right p.property.1.1]
  · rfl

def compressPath (μ : Coord n k → SignedMeasure (ClosedDomain.Q Ω)) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    Coord n k → SignedMeasure (ClosedDomain.Q Ω) :=
  pushPath (timeScale a r ha hab hr) (scaleMassPath r μ)

theorem action_compressPath (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure (ClosedDomain.Q Ω))
    (a r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    action L H (compressPath μ a r ha hab hr) = ENNReal.ofReal r⁻¹ * action L H μ := by
  rw [compressPath, action_pushPath_eq_of_leftInverse L H
    (timeScale a r ha hab hr).continuous (timeUnscale a r).continuous
    (timeUnscale_leftInverse ha hab hr), action_scaleMassPath L H μ hr]

def reverseTime : C(ClosedDomain.Q Ω, ClosedDomain.Q Ω) :=
  ⟨fun p ↦ ⟨(1 - p.val.1, p.val.2),
    ⟨⟨by linarith [p.property.1.2], by linarith [p.property.1.1]⟩, p.property.2⟩⟩,
    ((continuous_const.sub (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

omit [Fact (IsCompact Ω)] in
theorem reverseTime_involutive : Function.Involutive (reverseTime (Ω := Ω)) := by
  intro p
  apply Subtype.ext
  apply Prod.ext
  · change 1 - (1 - p.val.1) = p.val.1
    ring
  · rfl

def reverseBalancedPath (μ : Coord n k → SignedMeasure (ClosedDomain.Q Ω)) :
    Coord n k → SignedMeasure (ClosedDomain.Q Ω) :=
  pushPath reverseTime (reverseFluxPath μ)

theorem action_reverseBalancedPath (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure (ClosedDomain.Q Ω)) :
    action L H (reverseBalancedPath μ) = action L H μ := by
  rw [reverseBalancedPath, action_pushPath_eq_of_leftInverse L H reverseTime.continuous
    reverseTime.continuous reverseTime_involutive, action_reverseFluxPath]

end TimeMaps

section Pieces

open MatrixTransport.ReactionZero.ClosedDomain
variable {d n k : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

omit [Fact (IsCompact Ω)] in
theorem scaleMassPath_lagDensity (G : HubGeometry d Ω)
    (g : Fin n × Fin n → SignedMeasure ↥Ω) (r σ : ℝ) :
    scaleMassPath r (fun c ↦ (lagRef g).withDensityᵥ (fun p ↦ lagDensity G g 1 σ p.2 c)) =
      fun c ↦ (lagRef g).withDensityᵥ (fun p ↦ lagDensity G g r σ p.2 c) := by
  funext c
  rcases c with a | a | a
  · simp only [scaleMassPath, lagDensity, ReactionZero.pack, one_smul]
    change r • (lagRef g).withDensityᵥ (fun p ↦ endpointDensity g p.2 a.1 a.2) =
      (lagRef g).withDensityᵥ (fun p ↦ r * endpointDensity g p.2 a.1 a.2)
    simpa only [smul_eq_mul] using
      (withDensityᵥ_smul' (μ := lagRef g) (fun p ↦ endpointDensity g p.2 a.1 a.2) r).symm
  · rfl
  · rfl

theorem lagPath_contraction_eq_compressPath (G : HubGeometry d Ω)
    (g : Fin n × Fin n → SignedMeasure ↥Ω) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    lagPath G g a 1 r ha (by simpa using hab) =
      compressPath (lagPath G g 0 1 1 (by norm_num) (by norm_num)) a r ha hab hr := by
  unfold lagPath compressPath
  rw [scaleMassPath_pushPath r (continuous_charMap G 0 (1 * 1) _ _).measurable,
    scaleMassPath_lagDensity, pushPath_comp
      (continuous_charMap G 0 (1 * 1) _ _).measurable (timeScale a r ha hab hr).continuous.measurable]
  congr 1
  funext p
  apply Subtype.ext
  apply Prod.ext
  · simp [timeScale, timeScalePoint, charMap, charPoint]
  · rfl

theorem lagPath_action_eq_div_duration (G : HubGeometry d Ω)
    (g : Fin n × Fin n → SignedMeasure ↥Ω)
    (L : Matrix (Fin (d * n)) (Fin (d * n)) ℝ) (H : RMat n) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    action L H (lagPath G g a 1 r ha (by simpa using hab)) =
      ENNReal.ofReal r⁻¹ * action L H (lagPath G g 0 1 1 (by norm_num) (by norm_num)) := by
  rw [lagPath_contraction_eq_compressPath G g a r ha hab hr, action_compressPath]

omit [Fact (IsCompact Ω)] in
theorem reverseFluxPath_lagDensity (G : HubGeometry d Ω)
    (g : Fin n × Fin n → SignedMeasure ↥Ω) :
    reverseFluxPath (fun c ↦ (lagRef g).withDensityᵥ (fun p ↦ lagDensity G g 1 1 p.2 c)) =
      fun c ↦ (lagRef g).withDensityᵥ (fun p ↦ lagDensity G g 1 (-1) p.2 c) := by
  funext c
  rcases c with a | a | a
  · rfl
  · simp only [reverseFluxPath, lagDensity, ReactionZero.pack,
      Matrix.smul_apply, smul_eq_mul, neg_one_mul, one_mul]
    rw [withDensityᵥ_neg']
  · rfl

theorem lagPath_unit_expansion_eq_reversal (G : HubGeometry d Ω)
    (g : Fin n × Fin n → SignedMeasure ↥Ω) :
    lagPath G g 1 (-1) 1 (by norm_num) (by norm_num) =
      reverseBalancedPath (lagPath G g 0 1 1 (by norm_num) (by norm_num)) := by
  unfold lagPath reverseBalancedPath
  rw [reverseFluxPath_pushPath (continuous_charMap G 0 (1 * 1) _ _).measurable,
    reverseFluxPath_lagDensity, pushPath_comp
      (continuous_charMap G 0 (1 * 1) _ _).measurable reverseTime.continuous.measurable]
  congr 1
  funext p
  apply Subtype.ext
  apply Prod.ext
  · simp [reverseTime, charMap, charPoint, sub_eq_add_neg]
  · rfl

theorem lagPath_expansion_eq_compressPath (G : HubGeometry d Ω)
    (g : Fin n × Fin n → SignedMeasure ↥Ω) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a - r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    lagPath G g a (-1) r ha (by simpa using hab) =
      compressPath (lagPath G g 1 (-1) 1 (by norm_num) (by norm_num)) (a - r) r hab
        (by simpa using ha) hr := by
  unfold lagPath compressPath
  rw [scaleMassPath_pushPath r (continuous_charMap G 1 ((-1) * 1) _ _).measurable,
    scaleMassPath_lagDensity, pushPath_comp
      (continuous_charMap G 1 ((-1) * 1) _ _).measurable
      (timeScale (a - r) r hab (by simpa using ha) hr).continuous.measurable]
  congr 1
  funext p
  apply Subtype.ext
  apply Prod.ext
  · change a + (-1) * r * p.1.val = a - r + r * (1 + ((-1) * 1) * p.1.val)
    ring
  · rfl

theorem lagPath_expansion_action_eq_div_duration (G : HubGeometry d Ω)
    (g : Fin n × Fin n → SignedMeasure ↥Ω)
    (L : Matrix (Fin (d * n)) (Fin (d * n)) ℝ) (H : RMat n) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a - r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    action L H (lagPath G g a (-1) r ha (by simpa using hab)) =
      ENNReal.ofReal r⁻¹ * action L H (lagPath G g 0 1 1 (by norm_num) (by norm_num)) := by
  rw [lagPath_expansion_eq_compressPath G g a r ha hab hr, action_compressPath,
    lagPath_unit_expansion_eq_reversal, action_reverseBalancedPath]

omit [Fact (IsCompact Ω)] in
theorem scaleMassPath_reactionDensity (ν : Measure ↥Ω) (H P Δ : RMat n) (r : ℝ) :
    scaleMassPath r (fun c : Coord n k ↦ (LiZouTransport.Reaction.reactionRef ν).withDensityᵥ
      (fun p ↦ LiZouTransport.Reaction.reactionDensity H P Δ 1 p c)) =
      fun c : Coord n k ↦ (LiZouTransport.Reaction.reactionRef ν).withDensityᵥ (fun p ↦ LiZouTransport.Reaction.reactionDensity H P Δ r p c) := by
  funext c
  rcases c with a | a | a
  · simp only [scaleMassPath, LiZouTransport.Reaction.reactionDensity, ReactionZero.pack, one_smul]
    change r • (LiZouTransport.Reaction.reactionRef ν).withDensityᵥ (fun p ↦ LiZouTransport.Reaction.factorMass H P Δ p.1.val a.1 a.2) =
      (LiZouTransport.Reaction.reactionRef ν).withDensityᵥ (fun p ↦ r * LiZouTransport.Reaction.factorMass H P Δ p.1.val a.1 a.2)
    simpa only [smul_eq_mul] using
      (withDensityᵥ_smul' (μ := LiZouTransport.Reaction.reactionRef ν)
        (fun p ↦ LiZouTransport.Reaction.factorMass H P Δ p.1.val a.1 a.2) r).symm
  · rfl
  · rfl

theorem reactionPath_eq_compressPath (ν : Measure ↥Ω) (H P Δ : RMat n) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    LiZouTransport.Reaction.reactionPath (k := k) ν H P Δ a r ha hab hr =
      compressPath (LiZouTransport.Reaction.reactionPath ν H P Δ 0 1 (by norm_num) (by norm_num) (by norm_num))
        a r ha hab hr := by
  unfold LiZouTransport.Reaction.reactionPath compressPath
  rw [scaleMassPath_pushPath r (LiZouTransport.Reaction.reactionMap 0 1 _ _ _).continuous.measurable,
    scaleMassPath_reactionDensity, pushPath_comp (LiZouTransport.Reaction.reactionMap 0 1 _ _ _).continuous.measurable
      (timeScale a r ha hab hr).continuous.measurable]
  congr 1
  funext p
  apply Subtype.ext
  apply Prod.ext
  · simp [LiZouTransport.Reaction.reactionMap, timeScale, timeScalePoint, Function.comp_def,
      LiZouTransport.Boundary.timeInsert]
  · rfl

theorem reactionPath_action_eq_div_duration (ν : Measure ↥Ω) (H P Δ : RMat n)
    (L : Matrix (Fin k) (Fin k) ℝ) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    action L H (LiZouTransport.Reaction.reactionPath ν H P Δ a r ha hab hr) =
      ENNReal.ofReal r⁻¹ * action L H
        (LiZouTransport.Reaction.reactionPath ν H P Δ 0 1 (by norm_num) (by norm_num) (by norm_num)) := by
  rw [reactionPath_eq_compressPath ν H P Δ a r ha hab hr, action_compressPath]

end Pieces

#print axioms action_pushPath_eq_of_leftInverse
#print axioms action_scaleMassPath
#print axioms action_reverseFluxPath
#print axioms action_compressPath
#print axioms action_reverseBalancedPath
#print axioms lagPath_action_eq_div_duration
#print axioms reactionPath_action_eq_div_duration
#print axioms lagPath_expansion_action_eq_div_duration

end MatrixTransport.EntrywiseBures
