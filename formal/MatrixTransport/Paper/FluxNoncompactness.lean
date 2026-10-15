import MatrixTransport.Paper.BoundaryTime
import MatrixTransport.PartialWeights.FrobeniusRates

/-!
# Failure of compactness for unscaled transport flux

On the unit interval, with entrywise divergence and equal uniform endpoints `I₂ dx`,
the actual signed-coordinate path `(I₂, √t J, 0)` satisfies every native closed-cylinder
continuity test. Its original action at weights `(t I₂, I₂)` is `1/t`, the minimum is zero,
and its genuine Frobenius variation is `√t √2`. Every increasing parameter subsequence
has no unscaled signed-coordinate weak-star limit.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.FluxNoncompactness
open MatrixTransport MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures
open LiZouTransport.Boundary

theorem _root_.Continuous.continuous_integrable {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {ρ : Measure X} [IsFiniteMeasure ρ]
    {f : X → ℝ} (hf : Continuous f) : Integrable f ρ :=
  continuousTest_integrable ⟨f, hf⟩ ρ

/-- The antisymmetric matrix in the existing flux compactness counterexample. -/
def J : Mat 2 := !![0, 1; -1, 0]

/-- In one space dimension the entrywise divergence adjoint is the spatial derivative. -/
def derivativeOperator : AdjointOperator 1 2 2 where
  D0 := 0
  Dj := fun _ ↦ ContinuousLinearMap.id ℝ (Mat 2)
  D0_one := by simp

theorem derivativeOperator_apply {Ω : Set (Space 1)} (φ : ClosedC1Jet Ω 2) (p : Q Ω) :
    derivativeOperator.apply φ p = φ.dx 0 p := by
  simp [AdjointOperator.apply, derivativeOperator]

theorem frob_J_zero (A : Mat 2) (hA : A.IsHermitian) : ReactionZero.frob A J = 0 := by
  have hs := hA.apply 0 1
  simp only [star_trivial] at hs
  simp [ReactionZero.frob, J, Fin.sum_univ_two]
  linarith

theorem frobeniusSq_J : frobeniusSq J = 2 := by
  norm_num [frobeniusSq, J, Fin.sum_univ_two]

theorem gram_J : gram J = (1 : Mat 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, J, Matrix.mul_apply, Fin.sum_univ_two]

/-- Constant primal density, parametrized by its unscaled flux amplitude. -/
def primal (a : ℝ) : Coord 2 2 → ℝ := pack 1 (a • J) 0

/-- Exact local cost, derived from the original quadratic support function. -/
theorem cost_primal (t a : ℝ) (ht : 0 < t) :
    cost (t • (1 : Mat 2)) (1 : Mat 2) (primal a) = ENNReal.ofReal (a ^ 2 / t ^ 2) := by
  have ht0 : t ≠ 0 := ht.ne'
  have hn : 0 ≤ a ^ 2 / t ^ 2 := by positivity
  apply le_antisymm
  · unfold cost supportFunction
    refine iSup₂_le fun b hb ↦ ENNReal.ofReal_le_ofReal ?_
    rw [primal, weightedPair_pack]
    have hdiag0 := hb.2.diag_nonneg (i := 0)
    have hdiag1 := hb.2.diag_nonneg (i := 1)
    have hsq01 := sq_nonneg (t * ReactionZero.flux b 0 1 - a / t)
    have hsq10 := sq_nonneg (t * ReactionZero.flux b 1 0 + a / t)
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
      gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mul_smul, Matrix.mul_one,
      Fin.sum_univ_two] at hdiag0 hdiag1
    simp [ReactionZero.frob, Fin.sum_univ_two, J] at ⊢
    have hdiv : a / t * t = a := div_mul_cancel₀ a ht0
    have hdivsq : (a / t) ^ 2 = a ^ 2 / t ^ 2 := div_pow a t 2
    have hc01 : t * ReactionZero.flux b 0 1 * (a / t) = ReactionZero.flux b 0 1 * a := by
      calc _ = ReactionZero.flux b 0 1 * (a / t * t) := by ring
           _ = _ := by rw [hdiv]
    have hc10 : t * ReactionZero.flux b 1 0 * (a / t) = ReactionZero.flux b 1 0 * a := by
      calc _ = ReactionZero.flux b 1 0 * (a / t * t) := by ring
           _ = _ := by rw [hdiv]
    nlinarith [sq_nonneg (t * ReactionZero.flux b 0 0), sq_nonneg (t * ReactionZero.flux b 1 1),
      sq_nonneg (ReactionZero.reaction b 0 0), sq_nonneg (ReactionZero.reaction b 0 1),
      sq_nonneg (ReactionZero.reaction b 1 0), sq_nonneg (ReactionZero.reaction b 1 1)]
  · let s := a / t ^ 2
    have hb := pack_flux_mem_dualSet (t • (1 : Mat 2)) (1 : Mat 2) s J
    have hf := cost_fenchel (t • (1 : Mat 2)) (1 : Mat 2) (primal a) _ hb
    have he : weightedPair (fun _ ↦ 1)
        (pack (-(s ^ 2 / 2) • gram (J * (t • (1 : Mat 2)))) (s • J) 0)
        (primal a) = a ^ 2 / t ^ 2 := by
      rw [primal, weightedPair_pack]
      simp only [Matrix.mul_smul, Matrix.mul_one, gram_smul, gram_J]
      simp [ReactionZero.frob, J, Fin.sum_univ_two, s]
      field_simp
      ring
    rw [he] at hf
    exact hf

variable {Ω : Set (Space 1)} [Fact (IsCompact Ω)]

/-- A stationary uniform matrix endpoint against its scalar spatial reference. -/
def endpoint (ν : Measure ↥Ω) (ij : Fin 2 × Fin 2) : SignedMeasure ↥Ω :=
  ν.withDensityᵥ (fun _ ↦ (1 : Mat 2) ij.1 ij.2)

/-- The genuine product reference on the closed cylinder. -/
def cylinderReference (ν : Measure ↥Ω) : Measure (Q Ω) :=
  (unitTime.prod ν).map (fun p ↦ timeInsert p.1 p.2)

instance cylinderReference_finite (ν : Measure ↥Ω) [IsFiniteMeasure ν] :
    IsFiniteMeasure (cylinderReference ν) := inferInstanceAs
      (IsFiniteMeasure ((unitTime.prod ν).map (fun p ↦ timeInsert p.1 p.2)))

/-- Genuine signed Radon coordinate measures with density `(I,aJ,0)`. -/
def path (ν : Measure ↥Ω) (a : ℝ) : Limit.Path Ω 2 2 :=
  fun c ↦ (cylinderReference ν).withDensityᵥ (fun _ ↦ primal a c)

omit [Fact (IsCompact Ω)] in
theorem endpoint_positive (ν : Measure ↥Ω) [IsFiniteMeasure ν] :
    EndpointPositiveSemidefinite (endpoint ν) := by
  intro B hB
  have he : (fun i j ↦ endpoint ν (i, j) B) = ν.real B • (1 : Mat 2) := by
    ext i j
    simp only [endpoint, withDensityᵥ_apply (integrable_const _) hB,
      Matrix.smul_apply, smul_eq_mul, integral_const]
    simp [measureReal_def, mul_comm]
  rw [he]
  exact Matrix.PosSemidef.one.smul ENNReal.toReal_nonneg

def problem (ν : Measure ↥Ω) [IsFiniteMeasure ν] : Limit.Problem Ω 2 2 where
  operator := derivativeOperator
  initial := endpoint ν
  terminal := endpoint ν
  initial_positive := endpoint_positive ν
  terminal_positive := endpoint_positive ν

omit [Fact (IsCompact Ω)] in
theorem path_symmetric (ν : Measure ↥Ω) (a : ℝ) : MassSymmetric (path ν a) := by
  intro i j
  simp only [path, primal, pack, Matrix.one_apply]
  congr 1
  funext p
  simp [eq_comm]


instance spatial_compactSpace : CompactSpace ↥Ω :=
  isCompact_iff_compactSpace.mp (Fact.out : IsCompact Ω)

theorem densityPair (ρ : Measure (Q Ω)) [IsFiniteMeasure ρ] (v : Coord 2 2 → ℝ)
    (A : C(Q Ω, Coord 2 2 → ℝ)) :
    Duality.coordinatePair (fun _ ↦ 1) (fun c ↦ ρ.withDensityᵥ (fun _ ↦ v c)) A =
      ∫ p, weightedPair (fun _ ↦ 1) (A p) v ∂ρ := by
  unfold Duality.coordinatePair weightedPair
  simp only [one_mul]
  have hint : ∀ c, Integrable (fun p ↦ A p c * v c) ρ := fun c ↦
    (((continuous_apply c).comp A.continuous).continuous_integrable).mul_const _
  rw [integral_finsetSum _ fun c _ ↦ hint c]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  exact signedPair_withDensityᵥ ρ measurable_const (integrable_const _) 
    ((continuous_apply c).comp A.continuous).measurable
    (Duality.continuousField_coordinate_bounded A c)

theorem endpointPair_integral (ν : Measure ↥Ω) [IsFiniteMeasure ν]
    (φ : ClosedC1Jet Ω 2) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    endpointPair (endpoint ν) φ s hs =
      ∫ x, ReactionZero.frob (φ.value (timeBoundary s hs x)) (1 : Mat 2) ∂ν := by
  unfold endpointPair ReactionZero.frob
  have hint : ∀ i j, Integrable (fun x ↦
      φ.value (timeBoundary s hs x) i j * (1 : Mat 2) i j) ν := fun i j ↦
    (((continuous_apply j).comp ((continuous_apply i).comp
      (φ.value.continuous.comp (timeBoundary s hs).continuous))).continuous_integrable).mul_const _
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ hint i j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact signedPair_withDensityᵥ ν measurable_const (integrable_const _)
    ((continuous_apply j).comp ((continuous_apply i).comp
      (φ.value.continuous.comp (timeBoundary s hs).continuous))).measurable
    (by let f : C(↥Ω, ℝ) := ⟨fun x ↦ φ.value (timeBoundary s hs x) i j, by fun_prop⟩
        exact ⟨‖f‖, fun x ↦ by change |f x| ≤ ‖f‖; simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩)

theorem path_good (G : HubGeometry 1 Ω) (ν : Measure ↥Ω) [IsFiniteMeasure ν]
    (a : ℝ) : Limit.Good (problem ν) (path ν a) := by
  refine ⟨path_symmetric ν a, ?_⟩
  intro φ
  change Duality.coordinatePair (fun _ ↦ 1) (path ν a) (testField derivativeOperator φ) = _
  unfold path
  rw [densityPair]
  have hp : ∀ p : Q Ω, weightedPair (fun _ ↦ 1)
      (testField derivativeOperator φ p) (primal a) =
        ReactionZero.frob (φ.dt p) (1 : Mat 2) := by
    intro p
    rw [primal, weightedPair_pack]
    simp only [testField, ContinuousMap.coe_mk, mass_pack, flux_pack, reaction_pack,
      derivativeOperator_apply, frob_smul_right, frob_J_zero _ (φ.dx_symmetric 0 p),
      mul_zero, frob_zero_right, add_zero]
  simp_rw [hp]
  unfold cylinderReference
  erw [integral_map continuous_timeInsert.measurable.aemeasurable
    ((continuous_frob_left (1 : Mat 2)).comp φ.dt.continuous).aestronglyMeasurable]
  have hi : Integrable (fun p : UnitI × ↥Ω ↦
      ReactionZero.frob (φ.dt (timeInsert p.1 p.2)) (1 : Mat 2)) (unitTime.prod ν) :=
    (((continuous_frob_left (1 : Mat 2)).comp
      (φ.dt.continuous.comp continuous_timeInsert)).continuous_integrable)
  dsimp only [Function.comp_def]
  rw [integral_prod_symm _ hi]
  have hinner : ∀ x : ↥Ω, ∫ s, ReactionZero.frob (φ.dt (timeInsert s x)) (1 : Mat 2)
      ∂unitTime = ReactionZero.frob (φ.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ x)) 1 -
        ReactionZero.frob (φ.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ x)) 1 := by
    intro x
    simp [ReactionZero.frob, Fin.sum_univ_two]
    have h0 := timeResidual_zero G φ 0 0 x
    have h1 := timeResidual_zero G φ 1 1 x
    unfold timeResidual at h0 h1
    have hm : Continuous (fun s : UnitI ↦ timeInsert s x) :=
      continuous_timeInsert.comp (continuous_id.prodMk continuous_const)
    have hc0 : Continuous (fun s : UnitI ↦ φ.dt (timeInsert s x) 0 0) :=
      (continuous_apply 0).comp ((continuous_apply 0).comp (φ.dt.continuous.comp hm))
    have hc1 : Continuous (fun s : UnitI ↦ φ.dt (timeInsert s x) 1 1) :=
      (continuous_apply 1).comp ((continuous_apply 1).comp (φ.dt.continuous.comp hm))
    rw [integral_add hc0.continuous_integrable hc1.continuous_integrable]
    linarith
  simp_rw [hinner]
  have hc1 : Continuous (fun x : ↥Ω ↦ ReactionZero.frob
      (φ.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ x)) (1 : Mat 2)) :=
    (continuous_frob_left (1 : Mat 2)).comp
      (φ.value.continuous.comp (timeBoundary 1 ⟨zero_le_one, le_rfl⟩).continuous)
  have hc0 : Continuous (fun x : ↥Ω ↦ ReactionZero.frob
      (φ.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ x)) (1 : Mat 2)) :=
    (continuous_frob_left (1 : Mat 2)).comp
      (φ.value.continuous.comp (timeBoundary 0 ⟨le_rfl, zero_le_one⟩).continuous)
  rw [integral_sub hc1.continuous_integrable hc0.continuous_integrable]
  exact (congrArg₂ (· - ·) (endpointPair_integral ν φ 1
    ⟨zero_le_one, le_rfl⟩).symm (endpointPair_integral ν φ 0
    ⟨le_rfl, zero_le_one⟩).symm)


theorem cylinderReference_univ (ν : Measure ↥Ω) [IsFiniteMeasure ν] (hν : ν univ = 1) :
    cylinderReference ν univ = 1 := by
  simp [cylinderReference, Measure.map_apply continuous_timeInsert.measurable
    MeasurableSet.univ]
  rw [← Set.univ_prod_univ, Measure.prod_prod, unitTime_univ, hν, one_mul]

theorem path_action (ν : Measure ↥Ω) [IsFiniteMeasure ν] (hν : ν univ = 1)
    (t a : ℝ) (ht : 0 < t) :
    action (t • (1 : Mat 2)) (1 : Mat 2) (path ν a) = ENNReal.ofReal (a ^ 2 / t ^ 2) := by
  unfold path
  rw [action_densityPath _ _ _ (fun _ ↦ measurable_const) (fun _ ↦ integrable_const _)]
  simp_rw [cost_primal t a ht]
  rw [lintegral_const, cylinderReference_univ ν hν, mul_one]

theorem frobeniusSq_smul' (b : Mat 2) (s : ℝ) :
    frobeniusSq (s • b) = s ^ 2 * frobeniusSq b := by
  unfold frobeniusSq
  simp only [Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem path_fluxTV (ν : Measure ↥Ω) [IsFiniteMeasure ν] (hν : ν univ = 1) (a : ℝ) :
    MatrixTransport.PartialWeights.rightFluxFrobeniusTV (path ν a) (1 : Mat 2) =
      ENNReal.ofReal (|a| * Real.sqrt 2) := by
  let F : (Coord 2 2 → ℝ) → ℝ≥0∞ := fun v ↦
    ENNReal.ofReal (Real.sqrt (frobeniusSq (ReactionZero.flux v)))
  have hFM : Measurable F := by
    dsimp [F, frobeniusSq, ReactionZero.flux]
    fun_prop
  have hFH : ∀ s : ℝ, 0 ≤ s → ∀ v : Coord 2 2 → ℝ,
      F (s • v) = ENNReal.ofReal s * F v := by
    intro s hs v
    have he : ReactionZero.flux (s • v) = s • ReactionZero.flux v := rfl
    simp only [F, he, frobeniusSq_smul']
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs, abs_of_nonneg hs,
      ENNReal.ofReal_mul hs]
  unfold MatrixTransport.PartialWeights.rightFluxFrobeniusTV path
  simp only [Matrix.mul_one]
  change (∫⁻ x, F (fun c ↦ SignedMeasure.rnDeriv
    ((cylinderReference ν).withDensityᵥ (fun _ ↦ primal a c))
      (jointReference (fun c ↦ (cylinderReference ν).withDensityᵥ
        (fun _ ↦ primal a c))) x) ∂_) = _
  rw [lintegral_rnDeriv_withDensityᵥ _ (fun _ ↦ measurable_const)
    (fun _ ↦ integrable_const _) F hFM hFH]
  simp only [F, primal, flux_pack, frobeniusSq_smul', frobeniusSq_J]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
    lintegral_const, cylinderReference_univ ν hν, mul_one]

theorem minimum_zero (G : HubGeometry 1 Ω) (ν : Measure ↥Ω) [IsFiniteMeasure ν]
    (hν : ν univ = 1) (t : ℝ) (ht : 0 < t) :
    Limit.minimumValue (problem ν) (t • (1 : Mat 2)) (1 : Mat 2) = 0 := by
  apply le_antisymm _ bot_le
  unfold Limit.minimumValue constrainedInfimum
  have h : (⨅ μ, ⨅ (_ : Limit.Good (problem ν) μ), action (t • (1 : Mat 2)) 1 μ) ≤
      action (t • (1 : Mat 2)) 1 (path ν 0) :=
    iInf_le_of_le (path ν 0) (iInf_le_of_le (path_good G ν 0) le_rfl)
  exact h.trans_eq (by simpa using path_action ν hν t 0 ht)


/-- Scalar coordinate embedding into one-dimensional Euclidean space. -/
def line (r : ℝ) : Space 1 := r • EuclideanSpace.single 0 1

theorem continuous_line : Continuous line := continuous_id.smul continuous_const

theorem norm_line_sub (r s : ℝ) : ‖line r - line s‖ = |r - s| := by
  rw [line, line, ← sub_smul, norm_smul]
  simp [Real.norm_eq_abs]

/-- The unit interval `[0,1]`, represented in one-dimensional Euclidean space. -/
def unitInterval : Set (Space 1) := Metric.closedBall (line (1 / 2)) (1 / 2)

instance unitInterval_compact : Fact (IsCompact unitInterval) := ⟨isCompact_closedBall _ _⟩

def intervalHub : HubGeometry 1 unitInterval where
  hub := line (1 / 2)
  convex := convex_closedBall _ _
  hub_mem := by
    have h : Metric.ball (line (1 / 2)) (1 / 2) ⊆ unitInterval := Metric.ball_subset_closedBall
    exact mem_interior_iff_mem_nhds.mpr
      (mem_of_superset (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num))) h)

def intervalPoint (s : UnitI) : ↥unitInterval :=
  ⟨line s.val, by
    rw [unitInterval, Metric.mem_closedBall, dist_eq_norm, norm_line_sub]
    exact abs_le.mpr ⟨by linarith [s.property.1], by linarith [s.property.2]⟩⟩

theorem continuous_intervalPoint : Continuous intervalPoint :=
  (continuous_line.comp continuous_subtype_val).subtype_mk _

/-- The genuine unit Lebesgue reference on the unit interval. -/
def spatialLebesgue : Measure ↥unitInterval := unitTime.map intervalPoint

instance spatialLebesgue_finite : IsFiniteMeasure spatialLebesgue := inferInstanceAs
  (IsFiniteMeasure (unitTime.map intervalPoint))

theorem spatialLebesgue_univ : spatialLebesgue univ = 1 := by
  rw [spatialLebesgue, Measure.map_apply continuous_intervalPoint.measurable
    MeasurableSet.univ, Set.preimage_univ, unitTime_univ]

/-- The existing family `G=I₂`, `q=√t J`, `R=0`, on the unit interval. -/
def examplePath (t : ℝ) : Limit.Path unitInterval 2 2 := path spatialLebesgue (Real.sqrt t)

theorem example_good (t : ℝ) : Limit.Good (problem spatialLebesgue) (examplePath t) :=
  path_good intervalHub spatialLebesgue (Real.sqrt t)

theorem example_action (t : ℝ) (ht : 0 < t) :
    action (t • (1 : Mat 2)) (1 : Mat 2) (examplePath t) = ENNReal.ofReal (1 / t) := by
  rw [examplePath, path_action spatialLebesgue spatialLebesgue_univ t (Real.sqrt t) ht,
    Real.sq_sqrt ht.le]
  congr 1
  field_simp

theorem example_fluxTV (t : ℝ) (_ht : 0 ≤ t) :
    MatrixTransport.PartialWeights.rightFluxFrobeniusTV (examplePath t) (1 : Mat 2) =
      ENNReal.ofReal (Real.sqrt t * Real.sqrt 2) := by
  rw [examplePath, path_fluxTV spatialLebesgue spatialLebesgue_univ,
    abs_of_nonneg (Real.sqrt_nonneg t)]

theorem example_minimum (t : ℝ) (ht : 0 < t) :
    Limit.minimumValue (problem spatialLebesgue) (t • (1 : Mat 2)) (1 : Mat 2) = 0 :=
  minimum_zero intervalHub spatialLebesgue spatialLebesgue_univ t ht


def parameter (j : ℕ) : ℝ := (j : ℝ) + 1

theorem parameter_pos (j : ℕ) : 0 < parameter j := by unfold parameter; positivity

theorem parameter_tendsto : Tendsto parameter atTop atTop :=
  tendsto_atTop_mono (fun j ↦ by dsimp [parameter]; linarith)
    (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ ↦ (j : ℝ)) atTop atTop)

theorem example_action_tendsto : Tendsto
    (fun j ↦ action (parameter j • (1 : Mat 2)) 1 (examplePath (parameter j)))
      atTop (𝓝 0) := by
  have he : (fun j ↦ action (parameter j • (1 : Mat 2)) 1 (examplePath (parameter j))) =
      fun j ↦ ENNReal.ofReal (regSeq j) := by
    funext j
    rw [example_action _ (parameter_pos j)]
    rfl
  rw [he]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp tendsto_regSeq

theorem example_fluxTV_tendsto : Tendsto (fun j ↦
    (MatrixTransport.PartialWeights.rightFluxFrobeniusTV (examplePath (parameter j))
      (1 : Mat 2)).toReal) atTop atTop := by
  have he : (fun j ↦ (MatrixTransport.PartialWeights.rightFluxFrobeniusTV
      (examplePath (parameter j)) (1 : Mat 2)).toReal) =
        fun j ↦ Real.sqrt (parameter j) * Real.sqrt 2 := by
    funext j
    rw [example_fluxTV _ (parameter_pos j).le, ENNReal.toReal_ofReal (by positivity)]
  rw [he]
  exact (Real.tendsto_sqrt_atTop.comp parameter_tendsto).atTop_mul_const (by positivity)

/-- The original near-minimizing family has diverging genuine unscaled flux variation. -/
theorem no_unscaled_flux_bound :
    (∀ j, Limit.Good (problem spatialLebesgue) (examplePath (parameter j))) ∧
    (∀ j, Limit.minimumValue (problem spatialLebesgue)
      (parameter j • (1 : Mat 2)) 1 = 0) ∧
    Tendsto (fun j ↦ action (parameter j • (1 : Mat 2)) 1
      (examplePath (parameter j))) atTop (𝓝 0) ∧
    Tendsto (fun j ↦ (MatrixTransport.PartialWeights.rightFluxFrobeniusTV
      (examplePath (parameter j)) (1 : Mat 2)).toReal) atTop atTop :=
  ⟨fun _ ↦ example_good _, fun j ↦ example_minimum _ (parameter_pos j),
    example_action_tendsto, example_fluxTV_tendsto⟩


theorem example_flux_coordinate_pair (t : ℝ) :
    signedPair (examplePath t (Sum.inr (Sum.inl ((0 : Fin 2), (1 : Fin 2)))))
      (fun _ ↦ (1 : ℝ)) = Real.sqrt t := by
  unfold examplePath path
  rw [signedPair_withDensityᵥ _ measurable_const (integrable_const _)
    measurable_const ⟨1, fun _ ↦ by norm_num⟩]
  simp [primal, pack, J, integral_const, measureReal_def,
    cylinderReference_univ spatialLebesgue spatialLebesgue_univ]

/-- No increasing subsequence of the unscaled signed-coordinate paths has a weak-star limit. -/
theorem no_unscaled_weakStar_subsequence (u : ℕ → ℕ) (hu : StrictMono u)
    (ν : Limit.Path unitInterval 2 2) :
    ¬SignedWeakStarTendsto (fun j ↦ examplePath (parameter (u j))) ν := by
  intro h
  let c : Coord 2 2 := Sum.inr (Sum.inl (0, 1))
  let f : C(Q unitInterval, ℝ) := ContinuousMap.const _ 1
  have hn := h c f
  have he : (fun j ↦ signedPair (examplePath (parameter (u j)) c) f) =
      fun j ↦ Real.sqrt (parameter (u j)) := by
    funext j
    exact example_flux_coordinate_pair _
  rw [he] at hn
  have ht := Real.tendsto_sqrt_atTop.comp (parameter_tendsto.comp hu.tendsto_atTop)
  exact not_tendsto_nhds_of_tendsto_atTop ht _ hn

#print axioms example_flux_coordinate_pair
#print axioms no_unscaled_weakStar_subsequence
#print axioms example_action_tendsto
#print axioms example_fluxTV_tendsto
#print axioms no_unscaled_flux_bound
#print axioms example_good
#print axioms example_action
#print axioms example_fluxTV
#print axioms example_minimum
#print axioms cost_primal
#print axioms path_good
#print axioms path_action
#print axioms path_fluxTV
#print axioms minimum_zero
end LiZouTransport.FluxNoncompactness
