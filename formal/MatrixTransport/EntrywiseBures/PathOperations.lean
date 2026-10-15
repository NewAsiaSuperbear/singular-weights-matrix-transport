import MatrixTransport.ReactionZero.LimitTheorem

/-!
# Signed pushforward, sums and density paths for the original support action

Everything here is stated for the ORIGINAL objects of the reaction-zero development:
finite signed coordinate measures, the Jordan pairing `MatrixTransport.signedPair`, the
continuous dual supremum `Duality.continuousDual`, and the RN-integrated action
`ReactionZero.action`.  The proofs use the already formalized identity
`WeightedSet.action_eq_continuousDual`; no action inequality is assumed.

* `pushSigned` is the genuine pushforward of a finite signed measure (both Jordan parts are
  pushed); `pushSigned_apply` identifies its value on every measurable set.
* `action_le_of_pullback` is the generic contraction principle: if every admissible continuous
  dual field on the target pulls back to an admissible field on the source with a controlled
  pairing, the target action is controlled.  Pushforward, sums and time rescaling are instances.
* `action_densityPath` computes the action of a density path against an arbitrary finite
  reference.  Unlike `lintegral_canonicalDensity_withDensity`, it has no `1 ≤ weight`
  hypothesis.

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace MatrixTransport.EntrywiseBures

/-! ### Genuine signed pushforward -/

section Push

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Pushforward of a finite signed measure along `T`: push both Jordan parts and subtract. -/
def pushSigned (T : α → β) (s : SignedMeasure α) : SignedMeasure β :=
  (s.toJordanDecomposition.posPart.map T).toSignedMeasure -
    (s.toJordanDecomposition.negPart.map T).toSignedMeasure

/-- `pushSigned` is the pushforward: its value on a measurable set is the value of the original
signed measure on the preimage. -/
theorem pushSigned_apply {T : α → β} (hT : Measurable T) (s : SignedMeasure α)
    {B : Set β} (hB : MeasurableSet B) : pushSigned T s B = s (T ⁻¹' B) := by
  rw [SignedMeasure.apply_eq_posPart_real_sub_negPart_real s (hT hB)]
  simp only [pushSigned, VectorMeasure.sub_apply,
    Measure.toSignedMeasure_apply_measurable hB, Measure.map_apply hT hB, measureReal_def]

/-- Coordinatewise pushforward of a finite family of signed measures. -/
def pushPath {ι : Type*} (T : α → β) (μ : ι → SignedMeasure α) : ι → SignedMeasure β :=
  fun c ↦ pushSigned T (μ c)

variable [MetricSpace β] [CompactSpace β] [BorelSpace β]

/-- Exact change of variables for the Jordan pairing of a continuous test. -/
theorem signedPair_pushSigned {T : α → β} (hT : Measurable T) (s : SignedMeasure α)
    (f : C(β, ℝ)) :
    MatrixTransport.signedPair (pushSigned T s) f =
      MatrixTransport.signedPair s (fun x ↦ f (T x)) := by
  let a : FiniteMeasure β := ⟨s.toJordanDecomposition.posPart.map T, inferInstance⟩
  let b : FiniteMeasure β := ⟨s.toJordanDecomposition.negPart.map T, inferInstance⟩
  have hab : pushSigned T s =
      (a : Measure β).toSignedMeasure - (b : Measure β).toSignedMeasure := rfl
  rw [hab, ReactionZero.signedPair_difference a b f]
  change (∫ x, f x ∂(s.toJordanDecomposition.posPart.map T)) -
      (∫ x, f x ∂(s.toJordanDecomposition.negPart.map T)) = _
  rw [integral_map hT.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map hT.aemeasurable f.continuous.aestronglyMeasurable]
  rfl

theorem coordinatePair_pushPath {ι : Type*} [Fintype ι] (coeff : ι → ℝ) {T : α → β}
    (hT : Measurable T) (μ : ι → SignedMeasure α) (a : C(β, ι → ℝ)) :
    ReactionZero.Duality.coordinatePair coeff (pushPath T μ) a =
      ReactionZero.Duality.coordinatePair coeff μ (fun x ↦ a (T x)) := by
  unfold ReactionZero.Duality.coordinatePair
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact signedPair_pushSigned hT (μ i) (ReactionZero.Duality.coordinateTest a i)

end Push

/-! ### Additivity of the Jordan pairing -/

section Additive

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [CompactSpace X] [BorelSpace X]

theorem signedPair_add (s t : SignedMeasure X) (f : C(X, ℝ)) :
    MatrixTransport.signedPair (s + t) f =
      MatrixTransport.signedPair s f + MatrixTransport.signedPair t f := by
  let a : FiniteMeasure X :=
    ⟨s.toJordanDecomposition.posPart + t.toJordanDecomposition.posPart, inferInstance⟩
  let b : FiniteMeasure X :=
    ⟨s.toJordanDecomposition.negPart + t.toJordanDecomposition.negPart, inferInstance⟩
  have hst : s + t = (a : Measure X).toSignedMeasure - (b : Measure X).toSignedMeasure := by
    have hs := SignedMeasure.toSignedMeasure_toJordanDecomposition s
    have ht := SignedMeasure.toSignedMeasure_toJordanDecomposition t
    change s + t =
      (s.toJordanDecomposition.posPart + t.toJordanDecomposition.posPart).toSignedMeasure -
        (s.toJordanDecomposition.negPart + t.toJordanDecomposition.negPart).toSignedMeasure
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    calc s + t = s.toJordanDecomposition.toSignedMeasure +
          t.toJordanDecomposition.toSignedMeasure := by rw [hs, ht]
      _ = _ := by
          simp only [JordanDecomposition.toSignedMeasure]
          abel
  rw [hst, ReactionZero.signedPair_difference a b f]
  change (∫ x, f x ∂(s.toJordanDecomposition.posPart + t.toJordanDecomposition.posPart)) -
      (∫ x, f x ∂(s.toJordanDecomposition.negPart + t.toJordanDecomposition.negPart)) = _
  rw [integral_add_measure (ReactionZero.continuousTest_integrable f _)
      (ReactionZero.continuousTest_integrable f _),
    integral_add_measure (ReactionZero.continuousTest_integrable f _)
      (ReactionZero.continuousTest_integrable f _)]
  simp only [MatrixTransport.signedPair]
  ring

variable {ι : Type*} [Fintype ι]

theorem coordinatePair_add (coeff : ι → ℝ) (μ ν : ι → SignedMeasure X) (a : C(X, ι → ℝ)) :
    ReactionZero.Duality.coordinatePair coeff (μ + ν) a =
      ReactionZero.Duality.coordinatePair coeff μ a +
        ReactionZero.Duality.coordinatePair coeff ν a := by
  unfold ReactionZero.Duality.coordinatePair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mul_add]
  congr 1
  exact signedPair_add (μ i) (ν i) (ReactionZero.Duality.coordinateTest a i)

/-- The continuous dual supremum is subadditive in the path. -/
theorem continuousDual_add_le (coeff : ι → ℝ) (S : Set (ι → ℝ)) (μ ν : ι → SignedMeasure X) :
    ReactionZero.Duality.continuousDual coeff S (μ + ν) ≤
      ReactionZero.Duality.continuousDual coeff S μ +
        ReactionZero.Duality.continuousDual coeff S ν := by
  unfold ReactionZero.Duality.continuousDual
  refine iSup_le fun a ↦ iSup_le fun ha ↦ ?_
  rw [coordinatePair_add]
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_)
  · exact le_iSup₂ (f := fun (a : C(X, ι → ℝ)) (_ : ∀ x, a x ∈ S) ↦
      ENNReal.ofReal (ReactionZero.Duality.coordinatePair coeff μ a)) a ha
  · exact le_iSup₂ (f := fun (a : C(X, ι → ℝ)) (_ : ∀ x, a x ∈ S) ↦
      ENNReal.ofReal (ReactionZero.Duality.coordinatePair coeff ν a)) a ha

/-- Subadditivity of the ORIGINAL RN-integrated action, derived from its proved continuous
dual representation. -/
theorem action_add_le {n k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (μ ν : ReactionZero.Coord n k → SignedMeasure X) :
    ReactionZero.action L H (μ + ν) ≤ ReactionZero.action L H μ + ReactionZero.action L H ν := by
  rw [ReactionZero.WeightedSet.action_eq_continuousDual,
    ReactionZero.WeightedSet.action_eq_continuousDual,
    ReactionZero.WeightedSet.action_eq_continuousDual]
  exact continuousDual_add_le _ _ μ ν

end Additive

/-! ### Constant tests -/

theorem signedPair_const {X : Type*} [MeasurableSpace X] (s : SignedMeasure X) (c : ℝ) :
    MatrixTransport.signedPair s (fun _ ↦ c) = c * s univ := by
  unfold MatrixTransport.signedPair
  rw [integral_const, integral_const,
    SignedMeasure.apply_eq_posPart_real_sub_negPart_real s MeasurableSet.univ]
  simp only [smul_eq_mul, measureReal_def]
  ring

/-! ### Generic pullback comparison of continuous dual suprema -/

section Compare

variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [MeasurableSpace Y] [TopologicalSpace Y] [CompactSpace Y] [BorelSpace Y]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem continuousDual_le_of_pullback (coeffX : ι → ℝ) (coeffY : κ → ℝ)
    (SX : Set (ι → ℝ)) (SY : Set (κ → ℝ)) (μ : ι → SignedMeasure X)
    (ν : κ → SignedMeasure Y) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a : C(Y, κ → ℝ), (∀ y, a y ∈ SY) → ∃ b : C(X, ι → ℝ), (∀ x, b x ∈ SX) ∧
      ReactionZero.Duality.coordinatePair coeffY ν a ≤
        c * ReactionZero.Duality.coordinatePair coeffX μ b) :
    ReactionZero.Duality.continuousDual coeffY SY ν ≤
      ENNReal.ofReal c * ReactionZero.Duality.continuousDual coeffX SX μ := by
  unfold ReactionZero.Duality.continuousDual
  refine iSup_le fun a ↦ iSup_le fun ha ↦ ?_
  obtain ⟨b, hb, hle⟩ := h a ha
  calc ENNReal.ofReal (ReactionZero.Duality.coordinatePair coeffY ν a)
      ≤ ENNReal.ofReal (c * ReactionZero.Duality.coordinatePair coeffX μ b) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal c * ENNReal.ofReal (ReactionZero.Duality.coordinatePair coeffX μ b) :=
        ENNReal.ofReal_mul hc
    _ ≤ ENNReal.ofReal c * ⨆ (b : C(X, ι → ℝ)) (_ : ∀ x, b x ∈ SX),
          ENNReal.ofReal (ReactionZero.Duality.coordinatePair coeffX μ b) := by
        gcongr
        exact le_iSup₂ (f := fun (b : C(X, ι → ℝ)) (_ : ∀ x, b x ∈ SX) ↦
          ENNReal.ofReal (ReactionZero.Duality.coordinatePair coeffX μ b)) b hb

end Compare

section ActionCompare

variable {X Y : Type*} [MeasurableSpace X] [MetricSpace X] [CompactSpace X] [BorelSpace X]
  [MeasurableSpace Y] [MetricSpace Y] [CompactSpace Y] [BorelSpace Y]
  {n k k' : ℕ}

/-- The generic comparison principle for the ORIGINAL action. -/
theorem action_le_of_pullback (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (L' : Matrix (Fin k') (Fin k') ℝ) (H' : Matrix (Fin n) (Fin n) ℝ)
    (μ : ReactionZero.Coord n k → SignedMeasure X)
    (ν : ReactionZero.Coord n k' → SignedMeasure Y) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a : C(Y, ReactionZero.Coord n k' → ℝ), (∀ y, a y ∈ ReactionZero.dualSet L' H') →
      ∃ b : C(X, ReactionZero.Coord n k → ℝ), (∀ x, b x ∈ ReactionZero.dualSet L H) ∧
        ReactionZero.Duality.coordinatePair (fun _ ↦ 1) ν a ≤
          c * ReactionZero.Duality.coordinatePair (fun _ ↦ 1) μ b) :
    ReactionZero.action L' H' ν ≤ ENNReal.ofReal c * ReactionZero.action L H μ := by
  rw [ReactionZero.WeightedSet.action_eq_continuousDual,
    ReactionZero.WeightedSet.action_eq_continuousDual]
  exact continuousDual_le_of_pullback _ _ _ _ μ ν hc h

/-- A continuous pushforward cannot increase the ORIGINAL action. -/
theorem action_pushPath_le (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    {T : X → Y} (hT : Continuous T) (μ : ReactionZero.Coord n k → SignedMeasure X) :
    ReactionZero.action L H (pushPath T μ) ≤ ReactionZero.action L H μ := by
  have h := action_le_of_pullback L H L H μ (pushPath T μ) zero_le_one fun a ha ↦
    ⟨a.comp ⟨T, hT⟩, fun x ↦ ha (T x), by
      rw [coordinatePair_pushPath _ hT.measurable μ a, one_mul]
      exact le_rfl⟩
  simpa only [ENNReal.ofReal_one, one_mul] using h

end ActionCompare

/-! ### Density paths against an arbitrary finite reference -/

section Reference

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]
  {ν : Measure X} [IsFiniteMeasure ν]

theorem coordinateWeight_nonneg (z : ι → X → ℝ) (x : X) : 0 ≤ coordinateWeight z x :=
  Finset.sum_nonneg fun i _ ↦ abs_nonneg (z i x)

theorem eq_zero_of_coordinateWeight_eq_zero (z : ι → X → ℝ) {x : X}
    (h0 : coordinateWeight z x = 0) (i : ι) : z i x = 0 := by
  have h := abs_le_coordinateWeight z i x
  rw [h0] at h
  exact abs_nonpos_iff.mp h

theorem integrable_div_coordinateWeight' (z : ι → X → ℝ) (hzM : ∀ i, Measurable (z i))
    (hzI : ∀ i, Integrable (z i) ν) (i : ι) :
    Integrable (fun x ↦ z i x / coordinateWeight z x)
      (jointReference (fun j ↦ ν.withDensityᵥ (z j))) := by
  have hwM := measurable_coordinateWeight z hzM
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((hzM i).div hwM).aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_div]
  rcases eq_or_lt_of_le (coordinateWeight_nonneg z x) with h0 | hpos
  · rw [← h0, abs_zero, div_zero]
    exact zero_le_one
  · rw [abs_of_pos hpos]
    exact (div_le_one hpos).mpr (abs_le_coordinateWeight z i x)

theorem withDensityᵥ_div_coordinateWeight' (z : ι → X → ℝ) (hzM : ∀ i, Measurable (z i))
    (hzI : ∀ i, Integrable (z i) ν) (i : ι) :
    (jointReference (fun j ↦ ν.withDensityᵥ (z j))).withDensityᵥ
        (fun x ↦ z i x / coordinateWeight z x) = ν.withDensityᵥ (z i) := by
  have hwM := measurable_coordinateWeight z hzM
  have hfm : AEMeasurable (fun x ↦ ENNReal.ofReal (coordinateWeight z x)) ν :=
    (ENNReal.measurable_ofReal.comp hwM).aemeasurable
  have hflt : ∀ᵐ x ∂ν, ENNReal.ofReal (coordinateWeight z x) < ∞ :=
    ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top
  have hfun : (fun x ↦ (ENNReal.ofReal (coordinateWeight z x)).toReal •
      (z i x / coordinateWeight z x)) = z i := by
    funext x
    rw [ENNReal.toReal_ofReal (coordinateWeight_nonneg z x), smul_eq_mul]
    rcases eq_or_lt_of_le (coordinateWeight_nonneg z x) with h0 | hpos
    · rw [eq_zero_of_coordinateWeight_eq_zero z h0.symm i, ← h0]
      simp
    · have hne : coordinateWeight z x ≠ 0 := hpos.ne'
      field_simp
  have hint : Integrable (fun x ↦ (ENNReal.ofReal (coordinateWeight z x)).toReal •
      (z i x / coordinateWeight z x)) ν := by
    rw [hfun]
    exact hzI i
  have key := withDensityᵥ_smul_eq_withDensityᵥ_withDensity' (μ := ν)
    (f := fun x ↦ ENNReal.ofReal (coordinateWeight z x))
    (g := fun x ↦ z i x / coordinateWeight z x) hfm hflt hint
  rw [hfun] at key
  rw [jointReference_withDensityᵥ z hzM hzI]
  exact key.symm

/-- Reference change for every measurable positively homogeneous local cost, with no lower
bound on the coordinate weight.  Points where all densities vanish contribute zero on both
sides because homogeneity forces `J 0 = 0`. -/
theorem lintegral_rnDeriv_withDensityᵥ (z : ι → X → ℝ) (hzM : ∀ i, Measurable (z i))
    (hzI : ∀ i, Integrable (z i) ν) (J : (ι → ℝ) → ℝ≥0∞) (hJ : Measurable J)
    (hJhom : ∀ t : ℝ, 0 ≤ t → ∀ v, J (t • v) = ENNReal.ofReal t * J v) :
    ∫⁻ x, J (fun i ↦ SignedMeasure.rnDeriv (ν.withDensityᵥ (z i))
        (jointReference (fun j ↦ ν.withDensityᵥ (z j))) x)
      ∂(jointReference (fun j ↦ ν.withDensityᵥ (z j))) = ∫⁻ x, J (fun i ↦ z i x) ∂ν := by
  have hwM := measurable_coordinateWeight z hzM
  have hae : ∀ᵐ x ∂(jointReference (fun j ↦ ν.withDensityᵥ (z j))),
      (fun i ↦ SignedMeasure.rnDeriv (ν.withDensityᵥ (z i))
        (jointReference (fun j ↦ ν.withDensityᵥ (z j))) x) =
        fun i ↦ z i x / coordinateWeight z x := by
    have hi : ∀ i, SignedMeasure.rnDeriv (ν.withDensityᵥ (z i))
        (jointReference (fun j ↦ ν.withDensityᵥ (z j)))
        =ᵐ[jointReference (fun j ↦ ν.withDensityᵥ (z j))]
          fun x ↦ z i x / coordinateWeight z x := fun i ↦
      Integrable.ae_eq_of_withDensityᵥ_eq
        (integrable_rnDeriv_jointReference (fun j ↦ ν.withDensityᵥ (z j)) i)
        (integrable_div_coordinateWeight' z hzM hzI i)
        ((withDensityᵥ_rnDeriv_jointReference (fun j ↦ ν.withDensityᵥ (z j)) i).trans
          (withDensityᵥ_div_coordinateWeight' z hzM hzI i).symm)
    filter_upwards [ae_all_iff.2 hi] with x hx
    funext i
    exact hx i
  have hfm : Measurable (fun x ↦ ENNReal.ofReal (coordinateWeight z x)) :=
    ENNReal.measurable_ofReal.comp hwM
  have hgm : Measurable (fun x ↦ J (fun i ↦ z i x / coordinateWeight z x)) :=
    hJ.comp (measurable_pi_iff.2 fun i ↦ (hzM i).div hwM)
  calc ∫⁻ x, J (fun i ↦ SignedMeasure.rnDeriv (ν.withDensityᵥ (z i))
        (jointReference (fun j ↦ ν.withDensityᵥ (z j))) x)
        ∂(jointReference (fun j ↦ ν.withDensityᵥ (z j)))
      = ∫⁻ x, J (fun i ↦ z i x / coordinateWeight z x)
          ∂(jointReference (fun j ↦ ν.withDensityᵥ (z j))) :=
        lintegral_congr_ae (hae.mono fun x hx ↦ congrArg J hx)
    _ = ∫⁻ x, J (fun i ↦ z i x / coordinateWeight z x)
          ∂(ν.withDensity fun x ↦ ENNReal.ofReal (coordinateWeight z x)) := by
        rw [jointReference_withDensityᵥ z hzM hzI]
    _ = ∫⁻ x, ENNReal.ofReal (coordinateWeight z x) *
          J (fun i ↦ z i x / coordinateWeight z x) ∂ν :=
        lintegral_withDensity_eq_lintegral_mul ν hfm hgm
    _ = ∫⁻ x, J (fun i ↦ z i x) ∂ν := by
        refine lintegral_congr fun x ↦ ?_
        rcases eq_or_lt_of_le (coordinateWeight_nonneg z x) with h0 | hpos
        · have hz : (fun i ↦ z i x) = (0 : ℝ) • (fun i ↦ z i x) := by
            funext i
            simp [eq_zero_of_coordinateWeight_eq_zero z h0.symm i]
          rw [← h0, ENNReal.ofReal_zero, zero_mul, hz, hJhom 0 le_rfl, ENNReal.ofReal_zero,
            zero_mul]
        · have hv : (coordinateWeight z x) • (fun i ↦ z i x / coordinateWeight z x) =
              fun i ↦ z i x := by
            funext i
            simp only [Pi.smul_apply, smul_eq_mul]
            have hne : coordinateWeight z x ≠ 0 := hpos.ne'
            field_simp
          rw [← hJhom (coordinateWeight z x) hpos.le, hv]

/-- The ORIGINAL action of a density path equals the integral of the local cost against the
chosen finite reference. -/
theorem action_densityPath {n k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (z : ReactionZero.Coord n k → X → ℝ)
    (hzM : ∀ c, Measurable (z c)) (hzI : ∀ c, Integrable (z c) ν) :
    ReactionZero.action L H (fun c ↦ ν.withDensityᵥ (z c)) =
      ∫⁻ x, ReactionZero.cost L H (fun c ↦ z c x) ∂ν := by
  unfold ReactionZero.action ReactionZero.density
  exact lintegral_rnDeriv_withDensityᵥ z hzM hzI (ReactionZero.cost L H)
    (ReactionZero.measurable_cost L H) (fun t ht v ↦ ReactionZero.cost_smul_nonneg L H v ht)

end Reference

/-! ### Pushed density paths -/

section PushedDensity

variable {X Y : Type*} [MeasurableSpace X] [MetricSpace X] [CompactSpace X] [BorelSpace X]
  [MeasurableSpace Y] [MetricSpace Y] [CompactSpace Y] [BorelSpace Y]
  {ι : Type*} [Fintype ι]

/-- The pairing of a pushed density path with a continuous field is the reference integral of
the pulled-back pointwise pairing. -/
theorem coordinatePair_pushDensity (ν : Measure X) [IsFiniteMeasure ν] (z : ι → X → ℝ)
    (hzM : ∀ c, Measurable (z c)) (hzI : ∀ c, Integrable (z c) ν) {Θ : X → Y}
    (hΘ : Continuous Θ) (a : C(Y, ι → ℝ)) :
    ReactionZero.Duality.coordinatePair (fun _ ↦ 1)
        (pushPath Θ (fun c ↦ ν.withDensityᵥ (z c))) a =
      ∫ x, weightedPair (fun _ ↦ 1) (a (Θ x)) (fun c ↦ z c x) ∂ν := by
  rw [coordinatePair_pushPath _ hΘ.measurable]
  have hbound : ∀ c, ∃ C : ℝ, ∀ x, |a (Θ x) c| ≤ C := fun c ↦ by
    obtain ⟨C, hC⟩ := ReactionZero.Duality.continuousField_coordinate_bounded a c
    exact ⟨C, fun x ↦ hC (Θ x)⟩
  have hmeas : ∀ c, Measurable (fun x ↦ a (Θ x) c) := fun c ↦
    ((continuous_apply c).comp (a.continuous.comp hΘ)).measurable
  have hterm : ∀ c, MatrixTransport.signedPair (ν.withDensityᵥ (z c)) (fun x ↦ a (Θ x) c) =
      ∫ x, a (Θ x) c * z c x ∂ν := fun c ↦
    signedPair_withDensityᵥ ν (hzM c) (hzI c) (hmeas c) (hbound c)
  have hint : ∀ c, Integrable (fun x ↦ 1 * a (Θ x) c * z c x) ν := fun c ↦ by
    obtain ⟨C, hC⟩ := hbound c
    simpa only [one_mul] using (hzI c).bdd_mul (f := fun x ↦ a (Θ x) c) (c := C)
      (hmeas c).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)
  unfold ReactionZero.Duality.coordinatePair weightedPair
  dsimp only
  rw [integral_finsetSum Finset.univ fun c _ ↦ hint c]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [hterm c, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  ring

/-- Action of a pushed density path: the local cost integrated against the source reference
bounds it.  Both the pushforward contraction and the reference change are proved above. -/
theorem action_pushDensity_le {n k : ℕ}
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (ν : Measure X)
    [IsFiniteMeasure ν] (z : ReactionZero.Coord n k → X → ℝ) (hzM : ∀ c, Measurable (z c))
    (hzI : ∀ c, Integrable (z c) ν) {Θ : X → Y} (hΘ : Continuous Θ) :
    ReactionZero.action L H (pushPath Θ (fun c ↦ ν.withDensityᵥ (z c))) ≤
      ∫⁻ x, ReactionZero.cost L H (fun c ↦ z c x) ∂ν :=
  (action_pushPath_le L H hΘ _).trans_eq (action_densityPath L H z hzM hzI)

end PushedDensity

#print axioms pushSigned_apply
#print axioms signedPair_pushSigned
#print axioms signedPair_add
#print axioms continuousDual_le_of_pullback
#print axioms action_le_of_pullback
#print axioms action_pushPath_le
#print axioms action_add_le
#print axioms lintegral_rnDeriv_withDensityᵥ
#print axioms action_densityPath
#print axioms coordinatePair_pushDensity
#print axioms action_pushDensity_le

end MatrixTransport.EntrywiseBures
