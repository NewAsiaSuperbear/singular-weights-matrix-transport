import MatrixTransport.EntrywiseBures.MatrixCurves
import MatrixTransport.Paper.UniformReactionProblem

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.Reaction
open MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures
variable {d n k : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

/-- A reaction segment uses the original source reference `ds ⊗ μ`. -/
def reactionRef (μ : Measure ↥Ω) : Measure (UnitI × ↥Ω) := unitTime.prod μ

instance reactionRef_finite (μ : Measure ↥Ω) [IsFiniteMeasure μ] :
    IsFiniteMeasure (reactionRef μ) := by unfold reactionRef; infer_instance

def reactionMap (a r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) : C(UnitI × ↥Ω, Q Ω) :=
  (timeScale a r ha hab hr).comp
    ⟨fun p ↦ LiZouTransport.Boundary.timeInsert p.1 p.2,
      LiZouTransport.Boundary.continuous_timeInsert⟩

def reactionDensity (H P Δ : RMat n) (r : ℝ) (p : UnitI × ↥Ω) :
    MatrixTransport.ReactionZero.Coord n k → ℝ :=
  MatrixTransport.ReactionZero.pack (r • factorMass H P Δ p.1.val) 0
    (factorRate H P Δ p.1.val)

theorem continuous_reactionDensity (H P Δ : RMat n) (r : ℝ) :
    Continuous (reactionDensity (Ω := Ω) (k := k) H P Δ r) := by
  have ht : Continuous (fun p : UnitI × ↥Ω ↦ p.1.val) := continuous_subtype_val.comp continuous_fst
  have hm := (continuous_factorMass H P Δ).comp ht
  have hr := (continuous_factorRate H P Δ).comp ht
  apply continuous_pi
  intro c
  rcases c with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · exact (((continuous_apply j).comp ((continuous_apply i).comp hm))).const_mul r
  · exact continuous_const
  · exact (continuous_apply j).comp ((continuous_apply i).comp hr)

theorem integrable_reactionDensity (μ : Measure ↥Ω) [IsFiniteMeasure μ]
    (H P Δ : RMat n) (r : ℝ) (c : MatrixTransport.ReactionZero.Coord n k) :
    Integrable (fun p ↦ reactionDensity H P Δ r p c) (reactionRef μ) :=
  ((continuous_apply c).comp (continuous_reactionDensity H P Δ r)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def reactionPath (μ : Measure ↥Ω) (H P Δ : RMat n) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    MatrixTransport.ReactionZero.Coord n k → SignedMeasure (Q Ω) :=
  pushPath (reactionMap a r ha hab hr)
    (fun c ↦ (reactionRef μ).withDensityᵥ (fun p ↦ reactionDensity H P Δ r p c))

/-- The constructed reaction segment has identically zero transport flux. -/
theorem reactionPath_flux_zero (μ : Measure ↥Ω) (H P Δ : RMat n) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r)
    (i : Fin n) (j : Fin k) :
    reactionPath μ H P Δ a r ha hab hr (Sum.inr (Sum.inl (i,j))) = 0 := by
  change pushSigned (reactionMap a r ha hab hr)
    ((reactionRef μ).withDensityᵥ (0 : UnitI × ↥Ω → ℝ)) = 0
  rw [MeasureTheory.withDensityᵥ_zero]
  simp [pushSigned, SignedMeasure.toJordanDecomposition_zero]

theorem reactionPath_massSymmetric (μ : Measure ↥Ω) (H P Δ : RMat n) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    MatrixTransport.ReactionZero.MassSymmetric (reactionPath (k := k) μ H P Δ a r ha hab hr) := by
  intro i j
  have hf : (fun p : UnitI × ↥Ω ↦ reactionDensity (k := k) H P Δ r p (Sum.inl (i, j))) =
      fun p ↦ reactionDensity (k := k) H P Δ r p (Sum.inl (j, i)) := by
    funext p
    change r * factorMass H P Δ p.1.val i j = r * factorMass H P Δ p.1.val j i
    have ht := (MatrixTransport.ReactionZero.posSemidef_gram
      (factorPoint P (H * Δ) p.1.val)).isHermitian
    have h := ht.apply j i
    simpa only [factorMass, star_trivial] using congrArg (fun x : ℝ ↦ r * x) h
  exact congrArg (fun f : UnitI × ↥Ω → ℝ ↦
    pushSigned (reactionMap a r ha hab hr) ((reactionRef μ).withDensityᵥ f)) hf

/-- Pointwise original action bound, with no inverse mass or inverse reaction weight. -/
theorem reactionDensity_cost_le (L : Matrix (Fin k) (Fin k) ℝ) {H : RMat n}
    (hH : Hᵀ = H) (P Δ : RMat n) {r : ℝ} (hr : 0 < r) (p : UnitI × ↥Ω) :
    MatrixTransport.ReactionZero.cost L H (reactionDensity H P Δ r p) ≤
      ENNReal.ofReal (2 / r * MatrixTransport.ReactionZero.frobeniusSq Δ) :=
  cost_reaction_le L hH (factorPoint P (H * Δ) p.1.val) Δ hr

theorem reactionPath_action_le (μ : Measure ↥Ω) [IsFiniteMeasure μ]
    (L : Matrix (Fin k) (Fin k) ℝ) {H : RMat n} (hH : Hᵀ = H)
    (P Δ : RMat n) (a r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    MatrixTransport.ReactionZero.action L H (reactionPath μ H P Δ a r ha hab hr) ≤
      ENNReal.ofReal (2 / r * MatrixTransport.ReactionZero.frobeniusSq Δ) * μ univ := by
  have h := action_pushDensity_le L H (reactionRef μ)
    (fun c p ↦ reactionDensity H P Δ r p c)
    (fun c ↦ ((continuous_apply c).comp (continuous_reactionDensity H P Δ r)).measurable)
    (integrable_reactionDensity μ H P Δ r) (reactionMap a r ha hab hr).continuous
  change MatrixTransport.ReactionZero.action L H (reactionPath μ H P Δ a r ha hab hr) ≤ _ at h
  refine h.trans ?_
  calc
    (∫⁻ p, MatrixTransport.ReactionZero.cost L H (reactionDensity H P Δ r p) ∂reactionRef μ) ≤
        ∫⁻ _p : UnitI × ↥Ω, ENNReal.ofReal (2 / r * MatrixTransport.ReactionZero.frobeniusSq Δ)
          ∂reactionRef μ :=
      lintegral_mono (fun p ↦ reactionDensity_cost_le L hH P Δ hr p)
    _ = ENNReal.ofReal (2 / r * MatrixTransport.ReactionZero.frobeniusSq Δ) * μ univ := by
      rw [lintegral_const]
      congr 1
      have hs : (univ : Set (UnitI × ↥Ω)) = univ ×ˢ univ := by ext p; simp
      change (unitTime.prod μ) univ = μ univ
      rw [hs, Measure.prod_prod, unitTime_univ, one_mul]

/-- The original pairing integrand equals the time derivative of the factor mass potential. -/
theorem pairing_reactionDensity (D : AdjointOperator d n k) (φ : ClosedC1Jet Ω n)
    {H : RMat n} (hH : Hᵀ = H) (P Δ : RMat n) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r)
    (p : UnitI × ↥Ω) :
    MatrixTransport.weightedPair (fun _ ↦ 1) (testField D φ (reactionMap a r ha hab hr p))
        (reactionDensity H P Δ r p) =
      MatrixTransport.ReactionZero.frob
        ((timePullbackJet φ a r ha hab hr).value (LiZouTransport.Boundary.timeInsert p.1 p.2))
        (factorMassDeriv H P Δ p.1.val) +
      MatrixTransport.ReactionZero.frob
        ((timePullbackJet φ a r ha hab hr).dt (LiZouTransport.Boundary.timeInsert p.1 p.2))
        (factorMass H P Δ p.1.val) := by
  have hs : (φ.value (reactionMap a r ha hab hr p))ᵀ =
      φ.value (reactionMap a r ha hab hr p) :=
    transpose_eq_of_isHermitian (φ.value_symmetric _)
  simp only [testField, ContinuousMap.coe_mk, reactionDensity,
    MatrixTransport.ReactionZero.weightedPair_pack, MatrixTransport.ReactionZero.mass_pack,
    MatrixTransport.ReactionZero.flux_pack, MatrixTransport.ReactionZero.reaction_pack,
    MatrixTransport.ReactionZero.frob_smul_right, frob_zero_right, add_zero,
    timePullbackJet_value, timePullbackJet_dt, MatrixTransport.ReactionZero.frob_smul_left]
  change r * MatrixTransport.ReactionZero.frob (φ.dt (reactionMap a r ha hab hr p))
      (factorMass H P Δ p.1.val) +
    MatrixTransport.ReactionZero.frob (φ.value (reactionMap a r ha hab hr p))
      (factorRate H P Δ p.1.val) =
    MatrixTransport.ReactionZero.frob (φ.value (reactionMap a r ha hab hr p))
      (factorMassDeriv H P Δ p.1.val) +
    r * MatrixTransport.ReactionZero.frob (φ.dt (reactionMap a r ha hab hr p))
      (factorMass H P Δ p.1.val)
  rw [frob_factorMassDeriv H P Δ _ hH hs]
  exact add_comm _ _

/-- Fundamental theorem of calculus for a complete factor reaction segment, at every x. -/
theorem integral_reactionPotential (G : HubGeometry d Ω) (φ : ClosedC1Jet Ω n)
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
    LiZouTransport.NativeSeparation.weighted_time_FTC G ψ _ _ (hmass i j).continuousOn
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
theorem reactionPath_coordinatePair (G : HubGeometry d Ω) (D : AdjointOperator d n k)
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
    integral_reactionPotential G φ H P Δ a r ha hab hr x
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

@[simp] theorem factorMass_zero (H P Δ : RMat n) :
    factorMass H P Δ 0 = MatrixTransport.ReactionZero.gram P := by
  simp [factorMass, factorPoint]

@[simp] theorem factorMass_one (H P Δ : RMat n) :
    factorMass H P Δ 1 = MatrixTransport.ReactionZero.gram (P + H * Δ) := by
  simp [factorMass, factorPoint]

/-- A genuine factor path is admissible for the uniform endpoint problem. -/
theorem reactionPath_good_uniform (G : HubGeometry d Ω) (D : AdjointOperator d n k)
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
  have h := reactionPath_coordinatePair G D μ hH P Δ 0 1
    ⟨le_rfl, zero_le_one⟩ (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one φ
  change MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1)
    (reactionPath μ H P Δ 0 1 _ _ _) (testField D φ) =
    endpointPair (uniformEndpoint μ (MatrixTransport.ReactionZero.gram (P + H * Δ))) φ 1 _ -
    endpointPair (uniformEndpoint μ (MatrixTransport.ReactionZero.gram P)) φ 0 _
  simpa only [factorMass_zero, factorMass_one, zero_add] using h

#print axioms reactionPath_action_le
#print axioms pairing_reactionDensity
#print axioms integral_reactionPotential
#print axioms reactionPath_coordinatePair
#print axioms reactionPath_good_uniform
end LiZouTransport.Reaction
