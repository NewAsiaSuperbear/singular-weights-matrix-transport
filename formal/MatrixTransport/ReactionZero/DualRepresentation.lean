import MatrixTransport.MeasureRepresentation
import MatrixTransport.SupportFunction
import MatrixTransport.Pairing

/-!
# Continuous dual tests and the integrated support action

These declarations use arbitrary finite coordinate signed measures, including singular measures.
They prove that the actual signed-measure pairing of every continuous admissible dual field is
bounded by the integrated support action. They also prove lower semicontinuity of the continuous
dual supremum. The converse representation inequality is not asserted in this module.

The support set need not be a cone. In particular the quadratic matrix dual set in Li--Zou is
convex and contains zero, but is generally not closed under positive scaling.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace MatrixTransport.ReactionZero.Duality

variable {Q ι : Type*} [MeasurableSpace Q] [Fintype ι]

/-- All coordinate RN derivatives against the canonical joint total variation reference. -/
def density (μ : ι → SignedMeasure Q) (x : Q) : ι → ℝ :=
  fun i ↦ (μ i).rnDeriv (jointReference μ) x

/-- The genuine integrated support action, with its extended-value range restrictions. -/
def integratedSupport (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (μ : ι → SignedMeasure Q) : ℝ≥0∞ :=
  ∫⁻ x, supportFunction coeff S (density μ x) ∂jointReference μ

theorem measurable_density (μ : ι → SignedMeasure Q) : Measurable (density μ) :=
  Measurable.of_eval fun i ↦ measurable_rnDeriv_jointReference μ i

theorem measurable_integratedSupport_integrand (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (μ : ι → SignedMeasure Q) :
    Measurable (fun x ↦ supportFunction coeff S (density μ x)) :=
  (measurable_supportFunction coeff S).comp (measurable_density μ)

/-- Coordinate pairing defined by the Jordan decomposition integrals of the signed measures. -/
def coordinatePair (coeff : ι → ℝ) (μ : ι → SignedMeasure Q) (a : Q → ι → ℝ) : ℝ :=
  ∑ i, coeff i * signedPair (μ i) (fun x ↦ a x i)

theorem coordinatePair_eq_integral (coeff : ι → ℝ) (μ : ι → SignedMeasure Q)
    (a : Q → ι → ℝ) (haM : ∀ i, Measurable (fun x ↦ a x i))
    (haB : ∀ i, ∃ C : ℝ, ∀ x, |a x i| ≤ C) :
    coordinatePair coeff μ a =
      ∫ x, weightedPair coeff (a x) (density μ x) ∂jointReference μ := by
  have hint : ∀ i, Integrable
      (fun x ↦ coeff i * a x i * density μ x i) (jointReference μ) := by
    intro i
    obtain ⟨C, hC⟩ := haB i
    simpa only [density, mul_assoc] using ((integrable_rnDeriv_jointReference μ i).bdd_mul
      (f := fun x ↦ a x i) (c := C) (haM i).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)).const_mul (coeff i)
  unfold coordinatePair
  have hterm : ∀ i, coeff i * signedPair (μ i) (fun x ↦ a x i) =
      ∫ x, coeff i * a x i * density μ x i ∂jointReference μ := by
    intro i
    rw [signedPair_rnDeriv (jointReference μ) (μ i)
      (absolutelyContinuous_jointReference μ i) (haM i) (haB i), ← integral_const_mul]
    simp only [density, mul_assoc]
  simp_rw [hterm]
  rw [← integral_finsetSum Finset.univ (fun i _ ↦ hint i)]
  rfl

theorem integrable_weightedPair (coeff : ι → ℝ) (μ : ι → SignedMeasure Q)
    (a : Q → ι → ℝ) (haM : ∀ i, Measurable (fun x ↦ a x i))
    (haB : ∀ i, ∃ C : ℝ, ∀ x, |a x i| ≤ C) :
    Integrable (fun x ↦ weightedPair coeff (a x) (density μ x)) (jointReference μ) := by
  apply integrable_finsetSum
  intro i _
  obtain ⟨C, hC⟩ := haB i
  simpa only [density, mul_assoc] using ((integrable_rnDeriv_jointReference μ i).bdd_mul
    (f := fun x ↦ a x i) (c := C) (haM i).aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)).const_mul (coeff i)

/-- The positive part of a real integral is bounded by the integral of the positive parts. -/
theorem ofReal_integral_le_lintegral_ofReal {ν : Measure Q} {f : Q → ℝ}
    (hf : Integrable f ν) :
    ENNReal.ofReal (∫ x, f x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  calc
    ENNReal.ofReal (∫ x, f x ∂ν) ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂ν) :=
      ENNReal.ofReal_le_ofReal (integral_mono hf hf.pos_part fun x ↦ le_max_left _ _)
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂ν :=
      ofReal_integral_eq_lintegral_ofReal hf.pos_part
        (ae_of_all _ fun x ↦ le_max_right _ _)
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
      congr 1
      funext x
      simp

theorem coordinatePair_le_integratedSupport (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (μ : ι → SignedMeasure Q) (a : Q → ι → ℝ)
    (haM : ∀ i, Measurable (fun x ↦ a x i))
    (haB : ∀ i, ∃ C : ℝ, ∀ x, |a x i| ≤ C) (haS : ∀ x, a x ∈ S) :
    ENNReal.ofReal (coordinatePair coeff μ a) ≤ integratedSupport coeff S μ := by
  rw [coordinatePair_eq_integral coeff μ a haM haB]
  exact (ofReal_integral_le_lintegral_ofReal
    (integrable_weightedPair coeff μ a haM haB)).trans
      (lintegral_mono fun x ↦ supportFunction_fenchel coeff S (density μ x) (a x) (haS x))

section ContinuousTests

variable [TopologicalSpace Q] [CompactSpace Q] [BorelSpace Q]

/-- Scalar coordinate of a continuous vector field. -/
def coordinateTest (a : C(Q, ι → ℝ)) (i : ι) : C(Q, ℝ) :=
  ⟨fun x ↦ a x i, (continuous_apply i).comp a.continuous⟩

omit [MeasurableSpace Q] [Fintype ι] [BorelSpace Q] in
theorem continuousField_coordinate_bounded (a : C(Q, ι → ℝ)) (i : ι) :
    ∃ C : ℝ, ∀ x, |a x i| ≤ C :=
  ⟨‖coordinateTest a i‖, fun x ↦ by
    simpa only [Real.norm_eq_abs, coordinateTest, ContinuousMap.coe_mk] using
      (coordinateTest a i).norm_coe_le_norm x⟩

/-- Supremum over admissible continuous fields, using the actual signed-measure pairing. -/
def continuousDual (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (μ : ι → SignedMeasure Q) : ℝ≥0∞ :=
  ⨆ (a : C(Q, ι → ℝ)) (_ : ∀ x, a x ∈ S), ENNReal.ofReal (coordinatePair coeff μ a)

theorem continuousDual_le_integratedSupport (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (μ : ι → SignedMeasure Q) :
    continuousDual coeff S μ ≤ integratedSupport coeff S μ := by
  refine iSup_le fun a ↦ iSup_le fun ha ↦ ?_
  exact coordinatePair_le_integratedSupport coeff S μ a
    (fun i ↦ (coordinateTest a i).continuous.measurable)
    (continuousField_coordinate_bounded a) ha

/-- The same dual supremum on the genuine product of weak dual spaces. -/
def weakDualSupport (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (ℓ : ι → WeakDual ℝ C(Q, ℝ)) : ℝ≥0∞ :=
  ⨆ (a : C(Q, ι → ℝ)) (_ : ∀ x, a x ∈ S),
    ENNReal.ofReal (∑ i, coeff i * ℓ i (coordinateTest a i))

omit [MeasurableSpace Q] [CompactSpace Q] [BorelSpace Q] in
theorem lowerSemicontinuous_weakDualSupport (coeff : ι → ℝ) (S : Set (ι → ℝ)) :
    LowerSemicontinuous (weakDualSupport (Q := Q) coeff S) := by
  unfold weakDualSupport
  refine lowerSemicontinuous_iSup fun a ↦ lowerSemicontinuous_iSup fun _ ↦ ?_
  apply Continuous.lowerSemicontinuous
  apply ENNReal.continuous_ofReal.comp
  exact continuous_finsetSum _ fun i _ ↦ continuous_const.mul
    ((WeakDual.eval_continuous (coordinateTest a i)).comp (continuous_apply i))

omit [CompactSpace Q] [BorelSpace Q] in
/-- Direct sequential lower semicontinuity under all scalar continuous signed-measure tests.
This conclusion is for `continuousDual`; equality with `integratedSupport` is still needed to
transfer this lower semicontinuity to the integrated action.
-/
theorem continuousDual_le_liminf (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (μ : ℕ → ι → SignedMeasure Q) (ν : ι → SignedMeasure Q)
    (hμ : ∀ i (f : C(Q, ℝ)),
      Tendsto (fun n ↦ signedPair (μ n i) f) atTop (𝓝 (signedPair (ν i) f))) :
    continuousDual coeff S ν ≤ atTop.liminf (fun n ↦ continuousDual coeff S (μ n)) := by
  refine iSup_le fun a ↦ iSup_le fun ha ↦ ?_
  have ht : Tendsto (fun n ↦ ENNReal.ofReal (coordinatePair coeff (μ n) a)) atTop
      (𝓝 (ENNReal.ofReal (coordinatePair coeff ν a))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    exact tendsto_finsetSum _ fun i _ ↦ tendsto_const_nhds.mul (hμ i (coordinateTest a i))
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (.of_forall fun n ↦ by
    unfold continuousDual
    exact le_iSup₂ (f := fun (a : C(Q, ι → ℝ)) (_ : ∀ x, a x ∈ S) ↦
      ENNReal.ofReal (coordinatePair coeff (μ n) a)) a ha)

end ContinuousTests

#print axioms coordinatePair_eq_integral
#print axioms continuousDual_le_integratedSupport
#print axioms lowerSemicontinuous_weakDualSupport
#print axioms continuousDual_le_liminf

end MatrixTransport.ReactionZero.Duality

namespace MatrixTransport.ReactionZero.ConvexProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A nonempty closed convex target in a real Hilbert space. -/
structure Target (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  convex : Convex ℝ carrier

/-- Nearest-point projection, obtained from the actual Hilbert projection theorem. -/
def project (K : Target E) (u : E) : E :=
  Classical.choose
    (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex u)

theorem project_mem (K : Target E) (u : E) : project K u ∈ K.carrier :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex u)).1

theorem project_minimizes (K : Target E) (u : E) :
    ‖u - project K u‖ = ⨅ w : K.carrier, ‖u - w‖ :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex u)).2

theorem project_variational (K : Target E) (u w : E) (hw : w ∈ K.carrier) :
    inner ℝ (u - project K u) (w - project K u) ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero K.convex (project_mem K u)).mp
    (project_minimizes K u) w hw

/-- The metric projection onto a closed convex set is nonexpansive. -/
theorem project_norm_sub_le (K : Target E) (u v : E) :
    ‖project K u - project K v‖ ≤ ‖u - v‖ := by
  let p := project K u
  let q := project K v
  have hu := project_variational K u q (project_mem K v)
  have hv := project_variational K v p (project_mem K u)
  change inner ℝ (u - p) (q - p) ≤ 0 at hu
  change inner ℝ (v - q) (p - q) ≤ 0 at hv
  have hneg : q - p = -(p - q) := by abel
  rw [hneg, inner_neg_right] at hu
  have hid : inner ℝ (u - v) (p - q) =
      inner ℝ (u - p) (p - q) - inner ℝ (v - q) (p - q) +
        inner ℝ (p - q) (p - q) := by
    simp only [inner_sub_left]
    ring
  have hsq : ‖p - q‖ ^ 2 ≤ inner ℝ (u - v) (p - q) := by
    rw [hid, real_inner_self_eq_norm_sq]
    linarith
  have hcs := real_inner_le_norm (u - v) (p - q)
  change ‖p - q‖ ≤ ‖u - v‖
  nlinarith [norm_nonneg (p - q), norm_nonneg (u - v)]

theorem project_lipschitz (K : Target E) : LipschitzWith 1 (project K) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using project_norm_sub_le K u v

theorem project_continuous (K : Target E) : Continuous (project K) :=
  (project_lipschitz K).continuous

theorem project_eq_self (K : Target E) {u : E} (hu : u ∈ K.carrier) : project K u = u := by
  have hle : ‖u - project K u‖ ≤ 0 := by
    rw [project_minimizes]
    have h := ciInf_le
      (show BddBelow (Set.range fun w : K.carrier ↦ ‖u - w‖) from
        ⟨0, by rintro y ⟨w, rfl⟩; exact norm_nonneg _⟩) ⟨u, hu⟩
    simpa using h
  have hz : u - project K u = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact (sub_eq_zero.mp hz).symm

/-- Projection preserves a pointwise target constraint and decreases approximation errors. -/
theorem project_approximation_error (K : Target E) {u v : E} (hu : u ∈ K.carrier) :
    ‖u - project K v‖ ≤ ‖u - v‖ := by
  simpa only [project_eq_self K hu] using project_norm_sub_le K u v

#print axioms project_norm_sub_le
#print axioms project_lipschitz
#print axioms project_eq_self

section ContinuousApproximation

open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [NormalSpace X]
  [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.WeaklyRegular]

/-- Continuous approximation in L1 that satisfies the closed convex target constraint everywhere.
No strict interior assumption on the target is used. This is a genuine approximation theorem,
obtained by composing mathlib's continuous L1 approximation with the nonexpansive projection.
-/
theorem exists_continuous_target_approximation (K : Target E) {f : X → E}
    (hf : Integrable f ν) (hfK : ∀ x, f x ∈ K.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(X, E), (∀ x, g x ∈ K.carrier) ∧ (∫ x, ‖f x - g x‖ ∂ν) ≤ ε := by
  obtain ⟨g, herr, hg⟩ := hf.exists_boundedContinuous_integral_sub_le hε
  let a : C(X, E) := ⟨fun x ↦ project K (g x), (project_continuous K).comp g.continuous⟩
  refine ⟨a, fun x ↦ project_mem K (g x), ?_⟩
  apply le_trans _ herr
  exact integral_mono_of_nonneg (ae_of_all _ fun x ↦ norm_nonneg (f x - a x))
    (hf.sub hg).norm (ae_of_all _ fun x ↦ project_approximation_error K (hfK x))

#print axioms exists_continuous_target_approximation

end ContinuousApproximation

end MatrixTransport.ReactionZero.ConvexProjection
