import MatrixTransport.Paper.RotatingReactionValue
import MatrixTransport.EntrywiseBures.PureReaction

/-! # Uniform reaction on compact regular closed domains

Interior density extends the native boundary time equation to spatial boundary points.
The resulting uniform signed-Radon paths attain the weighted Bures minimum.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.RegularReaction
open MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures
open MatrixTransport.ReactionZero.Limit
open LiZouTransport.Reaction

variable {d n k : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

/-- Closures of open spatial domains have the required interior density. -/
theorem closure_open_regular {U : Set (Space d)} (hU : IsOpen U) :
    closure U ⊆ closure (interior (closure U)) :=
  closure_mono (interior_maximal subset_closure hU)

/-- Native time differentiation extends to boundary spatial points by interior density. -/
theorem timeResidual_zero_regular (hΩ : Ω ⊆ closure (interior Ω))
    (φ : ClosedC1Jet Ω n) (i j : Fin n) (x : ↥Ω) :
    LiZouTransport.Boundary.timeResidual φ i j x = 0 := by
  obtain ⟨y, hy, ht⟩ := mem_closure_iff_seq_limit.mp (hΩ x.property)
  let z : ℕ → ↥Ω := fun m ↦ ⟨y m, interior_subset (hy m)⟩
  have hz : Tendsto z atTop (𝓝 x) := tendsto_subtype_rng.mpr ht
  have hlim := ((LiZouTransport.Boundary.continuous_timeResidual φ i j).tendsto x).comp hz
  have he : (fun m ↦ LiZouTransport.Boundary.timeResidual φ i j (z m)) =
      fun _ ↦ (0 : ℝ) := by
    funext m
    exact LiZouTransport.Boundary.timeResidual_zero_of_interior φ i j _ (hy m)
  change Tendsto (fun m ↦ LiZouTransport.Boundary.timeResidual φ i j (z m)) atTop
    (𝓝 (LiZouTransport.Boundary.timeResidual φ i j x)) at hlim
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Time FTC with scalar time weights and the complete native boundary test convention. -/
theorem weighted_time_FTC_regular (hΩ : Ω ⊆ closure (interior Ω))
    (φ : ClosedC1Jet Ω n) (f f' : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hf' : ContinuousOn f' (Icc (0 : ℝ) 1))
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (i j : Fin n) (x : ↥Ω) :
    (∫ s, (f' s.val * φ.value (LiZouTransport.Boundary.timeInsert s x) i j +
      f s.val * φ.dt (LiZouTransport.Boundary.timeInsert s x) i j) ∂unitTime) =
      f 1 * φ.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ x) i j -
        f 0 * φ.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ x) i j := by
  have h := timeResidual_zero_regular hΩ
    (LiZouTransport.NativeSeparation.timeWeightedJet φ f f' hf hf' hder) i j x
  simp only [LiZouTransport.Boundary.timeResidual,
    LiZouTransport.NativeSeparation.timeWeightedJet_dt,
    LiZouTransport.NativeSeparation.timeWeightedJet_value,
    LiZouTransport.Boundary.timeInsert, timeBoundary, ContinuousMap.coe_mk,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
  change (∫ s, (f' s.val * φ.value (LiZouTransport.Boundary.timeInsert s x) i j +
      f s.val * φ.dt (LiZouTransport.Boundary.timeInsert s x) i j) ∂unitTime) -
      f 1 * φ.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ x) i j +
      f 0 * φ.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ x) i j = 0 at h
  linarith

/-- Fundamental theorem of calculus for a complete factor reaction segment, at every x. -/
theorem integral_reactionPotential_regular (hΩ : Ω ⊆ closure (interior Ω)) (φ : ClosedC1Jet Ω n)
    (H P Δ : RMat n) (a r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) (x : ↥Ω) :
    (∫ s, MatrixTransport.ReactionZero.frob
      ((timePullbackJet φ a r ha hab hr).value (LiZouTransport.Boundary.timeInsert s x))
      (factorMassDeriv H P Δ s.val) +
      MatrixTransport.ReactionZero.frob
      ((timePullbackJet φ a r ha hab hr).dt (LiZouTransport.Boundary.timeInsert s x))
      (factorMass H P Δ s.val) ∂unitTime) =
    MatrixTransport.ReactionZero.frob (φ.value (timeBoundary (a + r) hab x))
      (factorMass H P Δ 1) -
    MatrixTransport.ReactionZero.frob (φ.value (timeBoundary a ha x))
      (factorMass H P Δ 0) := by
  let ψ := timePullbackJet φ a r ha hab hr
  have hmass : ∀ i j, Continuous (fun s ↦ factorMass H P Δ s i j) := fun i j ↦
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_factorMass H P Δ))
  have hder : ∀ i j, Continuous (fun s ↦ factorMassDeriv H P Δ s i j) := fun i j ↦
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_factorMassDeriv H P Δ))
  have hpoint : ∀ i j, (∫ s, (factorMassDeriv H P Δ s.val i j *
      ψ.value (LiZouTransport.Boundary.timeInsert s x) i j +
      factorMass H P Δ s.val i j * ψ.dt (LiZouTransport.Boundary.timeInsert s x) i j) ∂unitTime) =
      factorMass H P Δ 1 i j * ψ.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ x) i j -
      factorMass H P Δ 0 i j * ψ.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ x) i j := fun i j ↦
    weighted_time_FTC_regular hΩ ψ _ _ (hmass i j).continuousOn
      (hder i j).continuousOn (fun s _ ↦ hasDerivAt_entry (factorMass_deriv H P Δ s) i j) i j x
  have hint : ∀ i j, Integrable (fun s : UnitI ↦ factorMassDeriv H P Δ s.val i j *
      ψ.value (LiZouTransport.Boundary.timeInsert s x) i j +
      factorMass H P Δ s.val i j * ψ.dt (LiZouTransport.Boundary.timeInsert s x) i j) unitTime := by
    intro i j
    have ht : Continuous (fun s : UnitI ↦ LiZouTransport.Boundary.timeInsert s x) :=
      LiZouTransport.Boundary.continuous_timeInsert.comp (continuous_id.prodMk continuous_const)
    have hv := (continuous_apply j).comp ((continuous_apply i).comp (ψ.value.continuous.comp ht))
    have hd := (continuous_apply j).comp ((continuous_apply i).comp (ψ.dt.continuous.comp ht))
    exact (((hder i j).comp continuous_subtype_val).mul hv |>.add
      (((hmass i j).comp continuous_subtype_val).mul hd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold MatrixTransport.ReactionZero.frob
  simp_rw [← Finset.sum_add_distrib]
  have hfun : (fun s : UnitI ↦ ∑ i, ∑ j,
      (ψ.value (LiZouTransport.Boundary.timeInsert s x) i j * factorMassDeriv H P Δ s.val i j +
       ψ.dt (LiZouTransport.Boundary.timeInsert s x) i j * factorMass H P Δ s.val i j)) =
      fun s ↦ ∑ i, ∑ j, (factorMassDeriv H P Δ s.val i j *
        ψ.value (LiZouTransport.Boundary.timeInsert s x) i j +
        factorMass H P Δ s.val i j * ψ.dt (LiZouTransport.Boundary.timeInsert s x) i j) := by
    funext s
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  change (∫ s, ∑ i, ∑ j, (ψ.value (LiZouTransport.Boundary.timeInsert s x) i j *
      factorMassDeriv H P Δ s.val i j + ψ.dt (LiZouTransport.Boundary.timeInsert s x) i j *
      factorMass H P Δ s.val i j) ∂unitTime) = _
  rw [hfun, integral_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hint i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ ↦ hint _ j), hpoint]
  simp only [ψ, timePullbackJet_value, timeScale, timeScalePoint, timeBoundary,
    ContinuousMap.coe_mk, mul_one, mul_zero, add_zero, Finset.sum_sub_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- The complete original CE pairing of a timed factor reaction segment. -/
theorem reactionPath_coordinatePair_regular (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d n k)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] {H : RMat n} (hH : Hᵀ = H) (P Δ : RMat n)
    (a r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r)
    (φ : ClosedC1Jet Ω n) :
    MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1)
      (reactionPath μ H P Δ a r ha hab hr) (testField D φ) =
      endpointPair (uniformEndpoint μ (factorMass H P Δ 1)) φ (a + r) hab -
      endpointPair (uniformEndpoint μ (factorMass H P Δ 0)) φ a ha := by
  let z : MatrixTransport.ReactionZero.Coord n k → UnitI × ↥Ω → ℝ :=
    fun c p ↦ reactionDensity H P Δ r p c
  have hzM : ∀ c, Measurable (z c) := fun c ↦
    ((continuous_apply c).comp (continuous_reactionDensity H P Δ r)).measurable
  have hzI : ∀ c, Integrable (z c) (reactionRef μ) := integrable_reactionDensity μ H P Δ r
  have hpair := coordinatePair_pushDensity (reactionRef μ) z hzM hzI
    (reactionMap a r ha hab hr).continuous (testField D φ)
  change MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1)
    (reactionPath μ H P Δ a r ha hab hr) (testField D φ) = _ at hpair
  rw [hpair]
  let ψ := timePullbackJet φ a r ha hab hr
  let F : UnitI × ↥Ω → ℝ := fun p ↦ MatrixTransport.ReactionZero.frob
      (ψ.value (LiZouTransport.Boundary.timeInsert p.1 p.2)) (factorMassDeriv H P Δ p.1.val) +
    MatrixTransport.ReactionZero.frob (ψ.dt (LiZouTransport.Boundary.timeInsert p.1 p.2))
      (factorMass H P Δ p.1.val)
  have he : (fun p : UnitI × ↥Ω ↦ MatrixTransport.weightedPair (fun _ ↦ 1)
      (testField D φ (reactionMap a r ha hab hr p)) (fun c ↦ z c p)) = F :=
    funext fun p ↦ pairing_reactionDensity D φ hH P Δ a r ha hab hr p
  have hc : Continuous (fun p : UnitI × ↥Ω ↦ MatrixTransport.weightedPair (fun _ ↦ 1)
      (testField D φ (reactionMap a r ha hab hr p)) (fun c ↦ z c p)) := by
    unfold MatrixTransport.weightedPair
    apply continuous_finsetSum
    intro c _
    have h1 := (continuous_apply c).comp ((testField D φ).continuous.comp
      (reactionMap a r ha hab hr).continuous)
    have h2 := (continuous_apply c).comp (continuous_reactionDensity (Ω := Ω) (k := k) H P Δ r)
    exact (continuous_const.mul h1).mul h2
  have hI : Integrable F (reactionRef μ) := by
    rw [← he]
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ p, MatrixTransport.weightedPair (fun _ ↦ 1)
    (testField D φ (reactionMap a r ha hab hr p)) (fun c ↦ z c p) ∂reactionRef μ) = _
  rw [he]
  unfold reactionRef at hI ⊢
  rw [integral_prod_symm F hI]
  have hinner : ∀ x : ↥Ω, (∫ s : UnitI, F (s, x) ∂unitTime) =
      MatrixTransport.ReactionZero.frob (φ.value (timeBoundary (a + r) hab x))
        (factorMass H P Δ 1) -
      MatrixTransport.ReactionZero.frob (φ.value (timeBoundary a ha x))
        (factorMass H P Δ 0) := fun x ↦
    integral_reactionPotential_regular hΩ φ H P Δ a r ha hab hr x
  simp_rw [hinner]
  have h1 : Integrable (fun x : ↥Ω ↦ MatrixTransport.ReactionZero.frob
      (φ.value (timeBoundary (a + r) hab x)) (factorMass H P Δ 1)) μ :=
    ((continuous_frob_left _).comp (φ.value.continuous.comp
      (timeBoundary (a + r) hab).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h0 : Integrable (fun x : ↥Ω ↦ MatrixTransport.ReactionZero.frob
      (φ.value (timeBoundary a ha x)) (factorMass H P Δ 0)) μ :=
    ((continuous_frob_left _).comp (φ.value.continuous.comp
      (timeBoundary a ha).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_sub h1 h0, endpointPair_uniformEndpoint, endpointPair_uniformEndpoint]

/-- A genuine factor path is admissible for the uniform endpoint problem. -/
theorem reactionPath_good_uniform_regular (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d n k)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] {H : RMat n} (hH : Hᵀ = H) (P Δ : RMat n) :
    MatrixTransport.ReactionZero.Limit.Good
      (uniformProblem D μ (MatrixTransport.ReactionZero.gram P)
        (MatrixTransport.ReactionZero.gram (P + H * Δ))
        (MatrixTransport.ReactionZero.posSemidef_gram P)
        (MatrixTransport.ReactionZero.posSemidef_gram (P + H * Δ)))
      (reactionPath μ H P Δ 0 1 ⟨le_rfl, zero_le_one⟩
        (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one) := by
  refine ⟨reactionPath_massSymmetric μ H P Δ 0 1 _ _ _, ?_⟩
  intro φ
  have h := reactionPath_coordinatePair_regular hΩ D μ hH P Δ 0 1
    ⟨le_rfl, zero_le_one⟩ (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one φ
  change MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1)
    (reactionPath μ H P Δ 0 1 _ _ _) (testField D φ) =
    endpointPair (uniformEndpoint μ (MatrixTransport.ReactionZero.gram (P + H * Δ))) φ 1 _ -
    endpointPair (uniformEndpoint μ (MatrixTransport.ReactionZero.gram P)) φ 0 _
  simpa only [factorMass_zero, factorMass_one, zero_add] using h

/-- Exact weighted Bures minimum for uniform PSD endpoints in the original Radon problem.
The upper bound uses a constructed factor path; the lower bound tests every competitor. -/
theorem uniform_reaction_minimumValue_regular (R : PSDSqrt n)
    (hΩ : Ω ⊆ closure (interior Ω))
    (D : AdjointOperator d n k)
    (hD0 : ∀ A : RMat n, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    {H A0 A1 : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    (hA0 : A0.PosSemidef) (hA1 : A1.PosSemidef) (L : Matrix (Fin k) (Fin k) ℝ) :
    minimumValue (uniformProblem D μ A0 A1 hA0 hA1) L H =
      ENNReal.ofReal (buresValue R H A0 A1) := by
  apply le_antisymm
  · obtain ⟨P,Δ,hP,hPD,hcost⟩ := exists_bures_reaction_factor R hH hHu hA0 hA1
    have hGood := reactionPath_good_uniform_regular hΩ D μ hH P Δ
    have hGood' : Good (uniformProblem D μ A0 A1 hA0 hA1)
        (reactionPath μ H P Δ 0 1 ⟨le_rfl,zero_le_one⟩
          (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one) := by
      simpa only [hP,hPD] using hGood
    have hAction := reactionPath_action_le μ L hH P Δ 0 1
      ⟨le_rfl,zero_le_one⟩ (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
    have hUpper : MatrixTransport.ReactionZero.action L H
        (reactionPath μ H P Δ 0 1 ⟨le_rfl,zero_le_one⟩
          (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one) ≤
        ENNReal.ofReal (buresValue R H A0 A1) := by
      simpa only [div_one,hμ,mul_one,hcost] using hAction
    exact iInf_le_of_le _ (iInf_le_of_le hGood' hUpper)
  · exact uniform_bures_lower R D hD0 μ hμ hH hHu hA0 hA1 L

/-- The weighted Bures value is the exact pure-reaction minimum for uniform PSD endpoints,
and a constructed zero-flux signed Radon path attains it. Singular PSD endpoints and
arbitrary probability references, including boundary atoms, are allowed. -/
theorem pure_reaction_minimum_attained_regular (R : PSDSqrt n)
    (hΩ : Ω ⊆ closure (interior Ω))
    (D : AdjointOperator d n k)
    (hD0 : ∀ A : RMat n, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    {H A0 A1 : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    (hA0 : A0.PosSemidef) (hA1 : A1.PosSemidef) (L : Matrix (Fin k) (Fin k) ℝ) :
    pureReactionMinimumValue (uniformProblem D μ A0 A1 hA0 hA1) L H =
      ENNReal.ofReal (buresValue R H A0 A1) ∧
    ∃ ν : Path Ω n k, PureReaction (uniformProblem D μ A0 A1 hA0 hA1) ν ∧
      MatrixTransport.ReactionZero.action L H ν = ENNReal.ofReal (buresValue R H A0 A1) := by
  obtain ⟨P,Δ,hP,hPD,hcost⟩ := exists_bures_reaction_factor R hH hHu hA0 hA1
  let ν : Path Ω n k := reactionPath μ H P Δ 0 1 ⟨le_rfl,zero_le_one⟩
    (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
  have hGood : Good (uniformProblem D μ A0 A1 hA0 hA1) ν := by
    simpa only [hP,hPD] using reactionPath_good_uniform_regular hΩ D μ hH P Δ
  have hPure : PureReaction (uniformProblem D μ A0 A1 hA0 hA1) ν :=
    ⟨hGood, fun i j ↦ reactionPath_flux_zero μ H P Δ 0 1 _ _ _ i j⟩
  have hUpper : MatrixTransport.ReactionZero.action L H ν ≤
      ENNReal.ofReal (buresValue R H A0 A1) := by
    have h := reactionPath_action_le μ L hH P Δ 0 1
      ⟨le_rfl,zero_le_one⟩ (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
    simpa only [div_one,hμ,mul_one,hcost] using h
  have hLower : ENNReal.ofReal (buresValue R H A0 A1) ≤
      MatrixTransport.ReactionZero.action L H ν :=
    (uniform_bures_lower R D hD0 μ hμ hH hHu hA0 hA1 L).trans
      (iInf_le_of_le ν (iInf_le_of_le hGood le_rfl))
  have hAction := le_antisymm hUpper hLower
  refine ⟨?_,ν,hPure,hAction⟩
  apply le_antisymm
  · exact iInf_le_of_le ν (iInf_le_of_le hPure hUpper)
  · exact (uniform_bures_lower R D hD0 μ hμ hH hHu hA0 hA1 L).trans
      (minimumValue_le_pureReactionMinimumValue _ L H)

open MatrixTransport.Paper.RotatingReaction

/-- The exact formula is the infimum over the complete original signed-Radon class. -/
theorem rotation_minimum_eq_regular (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℝ} (hε : 0 < ε) :
    minimumValue (rotationProblem D μ) L (reactionWeight ε θ) =
      ENNReal.ofReal (rationalizedValue ε (Real.sin θ ^ 2)) := by
  have hu : IsUnit (reactionWeight ε θ).det := by
    rw [reactionWeight_det, isUnit_iff_ne_zero]
    exact ne_of_gt hε
  have h := uniform_reaction_minimumValue_regular (canonicalPSDSqrt 2) hΩ D hD0 μ hμ
    (reactionWeight_transpose ε θ) hu Matrix.PosSemidef.one endpoint1_posSemidef L
  change minimumValue (rotationProblem D μ) L (reactionWeight ε θ) =
    ENNReal.ofReal (buresValue (canonicalPSDSqrt 2) (reactionWeight ε θ)
      endpoint0 endpoint1) at h
  rw [buresValue_rotation (canonicalPSDSqrt 2) hε] at h
  exact h

/-- The limit's unchanged kernel component is retained in the explicit upper path. -/
theorem singular_minimum_eq_regular (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) :
    minimumValue (rotationProblem D μ) L singularWeight = ENNReal.ofReal targetValue := by
  apply le_antisymm
  · let path := LiZouTransport.Reaction.reactionPath (k := k) μ singularWeight (1 : Mat) growthIncrement 0 1
      ⟨le_rfl, zero_le_one⟩ (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
    have h0 := gram_identity
    have h1 : MatrixTransport.ReactionZero.gram ((1 : Mat) + singularWeight * growthIncrement) =
        endpoint1 := by
      rw [singularWeight_mul_growthIncrement, one_add_growthIncrement, gram_growthFactor]
    have hg : Good (rotationProblem D μ) path := by
      simpa only [rotationProblem, path, h0, h1] using
        reactionPath_good_uniform_regular hΩ D μ singularWeight_transpose (1 : Mat) growthIncrement
    have hmin : minimumValue (rotationProblem D μ) L singularWeight ≤
        MatrixTransport.ReactionZero.action L singularWeight path := by
      unfold minimumValue MatrixTransport.ReactionZero.constrainedInfimum
      exact iInf_le_of_le path (iInf_le_of_le hg le_rfl)
    have hupper := LiZouTransport.Reaction.reactionPath_action_le μ L singularWeight_transpose
      (1 : Mat) growthIncrement 0 1 ⟨le_rfl, zero_le_one⟩
      (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
    exact hmin.trans (by
      simpa only [div_one, hμ, mul_one, frobeniusSq_growthIncrement] using hupper)
  · apply targetValue_le_minimumValue (canonicalPSDSqrt 2) (rotationProblem D μ) hD0
    · exact totalMatrix_uniformEndpoint_probability μ hμ endpoint0
    · exact totalMatrix_uniformEndpoint_probability μ hμ endpoint1

theorem rotation_minimum_toReal_eq_regular (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℝ} (hε : 0 < ε) :
    (minimumValue (rotationProblem D μ) L (reactionWeight ε θ)).toReal =
      rationalizedValue ε (Real.sin θ ^ 2) := by
  rw [rotation_minimum_eq_regular hΩ D hD0 μ hμ L hε,
    ENNReal.toReal_ofReal (rotationValue_nonneg hε)]

/-- The finite scale classification concerns the original minimum values. -/
theorem rotation_minimum_finite_limit_regular (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℕ → ℝ} {ℓ : ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ Real.sin (θ j) ^ 2 / ε j) atTop (𝓝 ℓ)) :
    Tendsto (fun j ↦ (minimumValue (rotationProblem D μ) L
      (reactionWeight (ε j) (θ j))).toReal) atTop (𝓝 (targetValue + ℓ ^ 2 / 2)) := by
  have hp : Tendsto (fun j ↦ Real.sin (θ j) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sin_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using ((Real.continuous_sin.tendsto 0).comp hθ).pow 2
  apply (tendsto_value_finite hε hp hratio).congr
  intro j
  exact (rotation_minimum_toReal_eq_regular hΩ D hD0 μ hμ L (hεpos j)).symm

/-- The infinite `p/ε` case in the extended-limit classification. -/
theorem rotation_minimum_atTop_regular (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℕ → ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ Real.sin (θ j) ^ 2 / ε j) atTop atTop) :
    Tendsto (fun j ↦ (minimumValue (rotationProblem D μ) L
      (reactionWeight (ε j) (θ j))).toReal) atTop atTop := by
  have hp : Tendsto (fun j ↦ Real.sin (θ j) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sin_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using ((Real.continuous_sin.tendsto 0).comp hθ).pow 2
  apply (tendsto_value_atTop hε hp hratio).congr
  intro j
  exact (rotation_minimum_toReal_eq_regular hΩ D hD0 μ hμ L (hεpos j)).symm

/-- Subcritical and critical angle limits for the original minima, including `a=0`. -/
theorem rotation_minimum_angle_finite_limit_regular (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℕ → ℝ} {a : ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ θ j / Real.sqrt (ε j)) atTop (𝓝 a)) :
    Tendsto (fun j ↦ (minimumValue (rotationProblem D μ) L
      (reactionWeight (ε j) (θ j))).toReal) atTop (𝓝 (targetValue + a ^ 4 / 2)) := by
  apply (tendsto_value_angle_finite hεpos hε hθ hratio).congr
  intro j
  exact (rotation_minimum_toReal_eq_regular hΩ D hD0 μ hμ L (hεpos j)).symm

/-- Supercritical original minima diverge. -/
theorem rotation_minimum_angle_atTop_regular (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℕ → ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ |θ j| / Real.sqrt (ε j)) atTop atTop) :
    Tendsto (fun j ↦ (minimumValue (rotationProblem D μ) L
      (reactionWeight (ε j) (θ j))).toReal) atTop atTop := by
  apply (tendsto_value_angle_atTop hεpos hε hθ hratio).congr
  intro j
  exact (rotation_minimum_toReal_eq_regular hΩ D hD0 μ hμ L (hεpos j)).symm

/-- The supercritical equivalence is proved for original minima, with the exact constant. -/
theorem rotation_minimum_angle_asymptotic_regular (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
    (hD0 : ∀ A : Mat, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (L : Matrix (Fin k) (Fin k) ℝ) {ε θ : ℕ → ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ |θ j| / Real.sqrt (ε j)) atTop atTop) :
    Tendsto (fun j ↦ (minimumValue (rotationProblem D μ) L
      (reactionWeight (ε j) (θ j))).toReal / (θ j ^ 4 / (2 * ε j ^ 2)))
      atTop (𝓝 1) := by
  apply (tendsto_value_div_angle_scale hεpos hε hθ hratio).congr
  intro j
  rw [rotation_minimum_toReal_eq_regular hΩ D hD0 μ hμ L (hεpos j)]

#print axioms timeResidual_zero_regular
#print axioms weighted_time_FTC_regular
#print axioms reactionPath_good_uniform_regular
#print axioms uniform_reaction_minimumValue_regular
#print axioms pure_reaction_minimum_attained_regular
#print axioms rotation_minimum_eq_regular
#print axioms singular_minimum_eq_regular
#print axioms rotation_minimum_toReal_eq_regular
#print axioms rotation_minimum_finite_limit_regular
#print axioms rotation_minimum_atTop_regular
#print axioms rotation_minimum_angle_finite_limit_regular
#print axioms rotation_minimum_angle_atTop_regular
#print axioms rotation_minimum_angle_asymptotic_regular
end LiZouTransport.RegularReaction
