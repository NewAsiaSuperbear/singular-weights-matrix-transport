import MatrixTransport.Paper.GeneralUniformReaction

/-! # Joint parameter limits for the original rotating-reaction minima

Sequential criteria transfer the existing exact-value limits to countably generated
parameter filters. Positivity is required only eventually, so finite prefixes do not
restrict the limiting regimes. Extended-valued limits retain the original minimum.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace LiZouTransport.RotationFilters
open MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures
open MatrixTransport.ReactionZero.Limit MatrixTransport.Paper.RotatingReaction
open LiZouTransport.RegularReaction

/-- A sequential criterion which applies a predicate only after a finite shift. -/
theorem tendsto_of_positive_seq_tail {ι β : Type*} {l : Filter ι} {k : Filter β}
    [l.IsCountablyGenerated] {F : ι → β} {P : ι → Prop} (hP : ∀ᶠ x in l, P x)
    (h : ∀ u : ℕ → ι, Tendsto u atTop l → (∀ j, P (u j)) →
      Tendsto (F ∘ u) atTop k) : Tendsto F l k := by
  apply Filter.tendsto_of_seq_tendsto
  intro u hu
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 (hu.eventually hP)
  apply (tendsto_add_atTop_iff_nat N).1
  have hh := h (fun j ↦ u (j + N)) (hu.comp (tendsto_add_atTop_nat N))
    (fun j ↦ hN (j + N) (by omega))
  simpa only [Function.comp_def] using hh

variable {d k : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]
variable (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
variable (hD0 : ∀ A : MatrixTransport.Paper.RotatingReaction.Mat,
  A.IsHermitian → D.D0 A = 0)
variable (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
variable (L : Matrix (Fin k) (Fin k) ℝ)

/-- The original signed-Radon minimum as a function of both real parameters. -/
def nativeValue (ε θ : ℝ) : ℝ≥0∞ :=
  minimumValue (rotationProblem D μ) L (reactionWeight ε θ)

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {ε θ : ι → ℝ}

include hΩ hD0 hμ

omit [l.IsCountablyGenerated] in
/-- Every eventually positive reaction parameter gives an eventually finite native value. -/
theorem nativeValue_eventually_finite (hpos : ∀ᶠ x in l, 0 < ε x) :
    ∀ᶠ x in l, nativeValue D μ L (ε x) (θ x) ≠ ⊤ := by
  filter_upwards [hpos] with x hx
  rw [nativeValue,rotation_minimum_eq_regular hΩ D hD0 μ hμ L hx]
  exact ENNReal.ofReal_ne_top

/-- The scale sin²(theta)/epsilon gives the finite real limit on a parameter filter. -/
theorem nativeValue_finite_toReal {ℓ : ℝ} (hpos : ∀ᶠ x in l, 0 < ε x)
    (hε : Tendsto ε l (𝓝 0)) (hθ : Tendsto θ l (𝓝 0))
    (hratio : Tendsto (fun x ↦ Real.sin (θ x) ^ 2 / ε x) l (𝓝 ℓ)) :
    Tendsto (fun x ↦ (nativeValue D μ L (ε x) (θ x)).toReal) l
      (𝓝 (targetValue + ℓ ^ 2 / 2)) := by
  apply tendsto_of_positive_seq_tail hpos
  intro u hu hp
  simpa only [Function.comp_def,nativeValue] using!
    rotation_minimum_finite_limit_regular hΩ D hD0 μ hμ L hp
      (hε.comp hu) (hθ.comp hu) (hratio.comp hu)

/-- The finite limit is a limit of the actual extended-valued minima. -/
theorem nativeValue_finite {ℓ : ℝ} (hpos : ∀ᶠ x in l, 0 < ε x)
    (hε : Tendsto ε l (𝓝 0)) (hθ : Tendsto θ l (𝓝 0))
    (hratio : Tendsto (fun x ↦ Real.sin (θ x) ^ 2 / ε x) l (𝓝 ℓ)) :
    Tendsto (fun x ↦ nativeValue D μ L (ε x) (θ x)) l
      (𝓝 (ENNReal.ofReal (targetValue + ℓ ^ 2 / 2))) := by
  have h := ENNReal.tendsto_ofReal
    (nativeValue_finite_toReal hΩ D hD0 μ hμ L hpos hε hθ hratio)
  apply h.congr'
  filter_upwards [nativeValue_eventually_finite hΩ D hD0 μ hμ L hpos] with x hx
  exact ENNReal.ofReal_toReal hx

/-- Divergence in the sin²(theta)/epsilon regime, in real value coordinates. -/
theorem nativeValue_atTop_toReal (hpos : ∀ᶠ x in l, 0 < ε x)
    (hε : Tendsto ε l (𝓝 0)) (hθ : Tendsto θ l (𝓝 0))
    (hratio : Tendsto (fun x ↦ Real.sin (θ x) ^ 2 / ε x) l atTop) :
    Tendsto (fun x ↦ (nativeValue D μ L (ε x) (θ x)).toReal) l atTop := by
  apply tendsto_of_positive_seq_tail hpos
  intro u hu hp
  simpa only [Function.comp_def,nativeValue] using!
    rotation_minimum_atTop_regular hΩ D hD0 μ hμ L hp
      (hε.comp hu) (hθ.comp hu) (hratio.comp hu)

/-- The divergent regime tends to top in the original extended-valued minimum. -/
theorem nativeValue_top (hpos : ∀ᶠ x in l, 0 < ε x)
    (hε : Tendsto ε l (𝓝 0)) (hθ : Tendsto θ l (𝓝 0))
    (hratio : Tendsto (fun x ↦ Real.sin (θ x) ^ 2 / ε x) l atTop) :
    Tendsto (fun x ↦ nativeValue D μ L (ε x) (θ x)) l (𝓝 ⊤) := by
  have h := ENNReal.tendsto_ofReal_nhds_top.2
    (nativeValue_atTop_toReal hΩ D hD0 μ hμ L hpos hε hθ hratio)
  apply h.congr'
  filter_upwards [nativeValue_eventually_finite hΩ D hD0 μ hμ L hpos] with x hx
  exact ENNReal.ofReal_toReal hx

/-- Subcritical and critical angle limits on real parameter filters. -/
theorem nativeValue_angle_finite_toReal {a : ℝ} (hpos : ∀ᶠ x in l, 0 < ε x)
    (hε : Tendsto ε l (𝓝 0)) (hθ : Tendsto θ l (𝓝 0))
    (hratio : Tendsto (fun x ↦ θ x / Real.sqrt (ε x)) l (𝓝 a)) :
    Tendsto (fun x ↦ (nativeValue D μ L (ε x) (θ x)).toReal) l
      (𝓝 (targetValue + a ^ 4 / 2)) := by
  apply tendsto_of_positive_seq_tail hpos
  intro u hu hp
  simpa only [Function.comp_def,nativeValue] using!
    rotation_minimum_angle_finite_limit_regular hΩ D hD0 μ hμ L hp
      (hε.comp hu) (hθ.comp hu) (hratio.comp hu)

theorem nativeValue_angle_finite {a : ℝ} (hpos : ∀ᶠ x in l, 0 < ε x)
    (hε : Tendsto ε l (𝓝 0)) (hθ : Tendsto θ l (𝓝 0))
    (hratio : Tendsto (fun x ↦ θ x / Real.sqrt (ε x)) l (𝓝 a)) :
    Tendsto (fun x ↦ nativeValue D μ L (ε x) (θ x)) l
      (𝓝 (ENNReal.ofReal (targetValue + a ^ 4 / 2))) := by
  have h := ENNReal.tendsto_ofReal
    (nativeValue_angle_finite_toReal hΩ D hD0 μ hμ L hpos hε hθ hratio)
  apply h.congr'
  filter_upwards [nativeValue_eventually_finite hΩ D hD0 μ hμ L hpos] with x hx
  exact ENNReal.ofReal_toReal hx

/-- Supercritical real angle limits on a parameter filter. -/
theorem nativeValue_angle_atTop_toReal (hpos : ∀ᶠ x in l, 0 < ε x)
    (hε : Tendsto ε l (𝓝 0)) (hθ : Tendsto θ l (𝓝 0))
    (hratio : Tendsto (fun x ↦ |θ x| / Real.sqrt (ε x)) l atTop) :
    Tendsto (fun x ↦ (nativeValue D μ L (ε x) (θ x)).toReal) l atTop := by
  apply tendsto_of_positive_seq_tail hpos
  intro u hu hp
  simpa only [Function.comp_def,nativeValue] using!
    rotation_minimum_angle_atTop_regular hΩ D hD0 μ hμ L hp
      (hε.comp hu) (hθ.comp hu) (hratio.comp hu)

theorem nativeValue_angle_top (hpos : ∀ᶠ x in l, 0 < ε x)
    (hε : Tendsto ε l (𝓝 0)) (hθ : Tendsto θ l (𝓝 0))
    (hratio : Tendsto (fun x ↦ |θ x| / Real.sqrt (ε x)) l atTop) :
    Tendsto (fun x ↦ nativeValue D μ L (ε x) (θ x)) l (𝓝 ⊤) := by
  have h := ENNReal.tendsto_ofReal_nhds_top.2
    (nativeValue_angle_atTop_toReal hΩ D hD0 μ hμ L hpos hε hθ hratio)
  apply h.congr'
  filter_upwards [nativeValue_eventually_finite hΩ D hD0 μ hμ L hpos] with x hx
  exact ENNReal.ofReal_toReal hx

omit hΩ hD0 hμ [l.IsCountablyGenerated] in
/-- The supercritical asymptotic scale is well-defined eventually. -/
theorem angle_scale_eventually_pos (hpos : ∀ᶠ x in l, 0 < ε x)
    (hratio : Tendsto (fun x ↦ |θ x| / Real.sqrt (ε x)) l atTop) :
    ∀ᶠ x in l, 0 < θ x ^ 4 / (2 * ε x ^ 2) := by
  filter_upwards [hpos,hratio.eventually_gt_atTop 0] with x hx hr
  have hn : θ x ≠ 0 := by intro hn; simp [hn] at hr
  have hs : 0 < θ x ^ 4 := by
    have hh := sq_pos_of_ne_zero hn
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hh)]
  exact div_pos hs (by positivity)

/-- The exact angle asymptotic holds without any restriction to a chosen sequence. -/
theorem nativeValue_angle_asymptotic (hpos : ∀ᶠ x in l, 0 < ε x)
    (hε : Tendsto ε l (𝓝 0)) (hθ : Tendsto θ l (𝓝 0))
    (hratio : Tendsto (fun x ↦ |θ x| / Real.sqrt (ε x)) l atTop) :
    Tendsto (fun x ↦ (nativeValue D μ L (ε x) (θ x)).toReal /
      (θ x ^ 4 / (2 * ε x ^ 2))) l (𝓝 1) := by
  apply tendsto_of_positive_seq_tail hpos
  intro u hu hp
  simpa only [Function.comp_def,nativeValue] using!
    rotation_minimum_angle_asymptotic_regular hΩ D hD0 μ hμ L hp
      (hε.comp hu) (hθ.comp hu) (hratio.comp hu)

omit hΩ hD0 hμ

/-- The joint positive-epsilon, zero-angle source filter of the manuscript. -/
def rotFilter : Filter (ℝ × ℝ) := (𝓝[>] (0 : ℝ)) ×ˢ (𝓝 (0 : ℝ))

/-- Imposing an additional scale limit on the joint real parameter filter. -/
def ratioFilter (g : ℝ × ℝ → ℝ) (r : Filter ℝ) : Filter (ℝ × ℝ) :=
  rotFilter ⊓ Filter.comap g r

instance ratioFilter_countablyGenerated (g : ℝ × ℝ → ℝ) (r : Filter ℝ)
    [r.IsCountablyGenerated] : (ratioFilter g r).IsCountablyGenerated := by
  unfold ratioFilter rotFilter
  infer_instance

theorem ratioFilter_epsilon (g : ℝ × ℝ → ℝ) (r : Filter ℝ) :
    Tendsto Prod.fst (ratioFilter g r) (𝓝 0) :=
  (tendsto_fst.mono_left inf_le_left).mono_right nhdsWithin_le_nhds

theorem ratioFilter_theta (g : ℝ × ℝ → ℝ) (r : Filter ℝ) :
    Tendsto Prod.snd (ratioFilter g r) (𝓝 0) := tendsto_snd.mono_left inf_le_left

theorem ratioFilter_positive (g : ℝ × ℝ → ℝ) (r : Filter ℝ) :
    ∀ᶠ p in ratioFilter g r, 0 < p.1 := by
  have h : Tendsto Prod.fst (ratioFilter g r) (𝓝[>] (0 : ℝ)) :=
    tendsto_fst.mono_left inf_le_left
  exact h.eventually self_mem_nhdsWithin

theorem ratioFilter_ratio (g : ℝ × ℝ → ℝ) (r : Filter ℝ) :
    Tendsto g (ratioFilter g r) r := tendsto_comap.mono_left inf_le_right

include hΩ hD0 hμ

/-- The finite sin²(theta)/epsilon limit on the full joint real parameter filter. -/
theorem joint_finite (ℓ : ℝ) :
    Tendsto (fun p : ℝ × ℝ ↦ nativeValue D μ L p.1 p.2)
      (ratioFilter (fun p ↦ Real.sin p.2 ^ 2 / p.1) (𝓝 ℓ))
      (𝓝 (ENNReal.ofReal (targetValue + ℓ ^ 2 / 2))) :=
  nativeValue_finite hΩ D hD0 μ hμ L (ratioFilter_positive _ _)
    (ratioFilter_epsilon _ _) (ratioFilter_theta _ _) (ratioFilter_ratio _ _)

/-- The divergent sin²(theta)/epsilon limit for the original joint minimum. -/
theorem joint_top :
    Tendsto (fun p : ℝ × ℝ ↦ nativeValue D μ L p.1 p.2)
      (ratioFilter (fun p ↦ Real.sin p.2 ^ 2 / p.1) atTop) (𝓝 ⊤) :=
  nativeValue_top hΩ D hD0 μ hμ L (ratioFilter_positive _ _)
    (ratioFilter_epsilon _ _) (ratioFilter_theta _ _) (ratioFilter_ratio _ _)

/-- The angle-normalized finite classification on the full joint parameter filter. -/
theorem joint_angle_finite (a : ℝ) :
    Tendsto (fun p : ℝ × ℝ ↦ nativeValue D μ L p.1 p.2)
      (ratioFilter (fun p ↦ p.2 / Real.sqrt p.1) (𝓝 a))
      (𝓝 (ENNReal.ofReal (targetValue + a ^ 4 / 2))) :=
  nativeValue_angle_finite hΩ D hD0 μ hμ L (ratioFilter_positive _ _)
    (ratioFilter_epsilon _ _) (ratioFilter_theta _ _) (ratioFilter_ratio _ _)

/-- The supercritical joint minimum tends to infinity in its original value space. -/
theorem joint_angle_top :
    Tendsto (fun p : ℝ × ℝ ↦ nativeValue D μ L p.1 p.2)
      (ratioFilter (fun p ↦ |p.2| / Real.sqrt p.1) atTop) (𝓝 ⊤) :=
  nativeValue_angle_top hΩ D hD0 μ hμ L (ratioFilter_positive _ _)
    (ratioFilter_epsilon _ _) (ratioFilter_theta _ _) (ratioFilter_ratio _ _)

/-- Exact supercritical asymptotic on the joint real parameter filter. -/
theorem joint_angle_asymptotic :
    Tendsto (fun p : ℝ × ℝ ↦ (nativeValue D μ L p.1 p.2).toReal /
      (p.2 ^ 4 / (2 * p.1 ^ 2)))
      (ratioFilter (fun p ↦ |p.2| / Real.sqrt p.1) atTop) (𝓝 1) :=
  nativeValue_angle_asymptotic hΩ D hD0 μ hμ L (ratioFilter_positive _ _)
    (ratioFilter_epsilon _ _) (ratioFilter_theta _ _) (ratioFilter_ratio _ _)

#print axioms nativeValue_finite
#print axioms nativeValue_top
#print axioms nativeValue_angle_finite
#print axioms nativeValue_angle_top
#print axioms nativeValue_angle_asymptotic
#print axioms joint_finite
#print axioms joint_top
#print axioms joint_angle_finite
#print axioms joint_angle_top
#print axioms joint_angle_asymptotic
end LiZouTransport.RotationFilters
