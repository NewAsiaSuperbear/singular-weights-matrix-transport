import MatrixTransport.Paper.NativeSeparationSpace
import MatrixTransport.ReactionZero.LimitTheorem

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise ContDiff

namespace LiZouTransport.NativeSeparation
open MatrixTransport MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures

/-- Lebesgue measure restricted to the actual spatial subtype. -/
def spatialMeasure : Measure ↥disk := Measure.comap Subtype.val volume

instance spatialMeasure_finite : IsFiniteMeasure spatialMeasure := by
  refine ⟨?_⟩
  unfold spatialMeasure
  rw [(MeasurableEmbedding.subtype_coe disk_measurableSet).comap_apply, Set.image_univ,
    Subtype.range_coe, disk_volume_eq_pi]
  exact ENNReal.ofReal_lt_top

/-- A continuous matrix density determines the actual signed Radon endpoint family. -/
def densityEndpoint (g : Spatial → Mat2) : (Fin 2 × Fin 2) → SignedMeasure ↥disk :=
  fun c ↦ spatialMeasure.withDensityᵥ (fun x ↦ g x.val c.1 c.2)

theorem densityEndpoint_positive (g : Spatial → Mat2) (hg : Continuous g)
    (hPSD : ∀ x ∈ disk, (g x).PosSemidef) : EndpointPositiveSemidefinite (densityEndpoint g) := by
  intro B hB
  have hI : ∀ i j, Integrable (fun x : ↥disk ↦ g x.val i j) spatialMeasure := fun i j ↦
    ((continuous_apply j).comp ((continuous_apply i).comp
      (hg.comp continuous_subtype_val))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (fun i j ↦ densityEndpoint g (i, j) B) =
      fun i j ↦ ∫ x in B, g x.val i j ∂spatialMeasure := by
    funext i j
    exact withDensityᵥ_apply (hI i j) hB
  rw [he]
  exact MatrixTransport.ReactionZero.MatrixPositivity.posSemidef_setIntegral
    (fun x : ↥disk ↦ g x.val) hI (ae_of_all _ fun x ↦ hPSD x.val x.property) B

def nativeEndpointPair (g : Spatial → Mat2) (φ : ClosedC1Jet disk 2) (t : ℝ) : ℝ :=
  ∫ x, frob (g x) (zeroExtend φ.value (t, x)) ∂diskVolume

theorem endpointPair_densityEndpoint (g : Spatial → Mat2) (hg : Continuous g)
    (φ : ClosedC1Jet disk 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    MatrixTransport.ReactionZero.ClosedDomain.endpointPair (densityEndpoint g) φ t ht =
      nativeEndpointPair g φ t := by
  let F : C(↥disk, Mat2) := φ.value.comp (timeBoundary t ht)
  have hI : ∀ i j, Integrable (fun x : ↥disk ↦ g x.val i j) spatialMeasure := fun i j ↦
    ((continuous_apply j).comp ((continuous_apply i).comp
      (hg.comp continuous_subtype_val))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hterm : ∀ i j, MatrixTransport.signedPair (densityEndpoint g (i, j))
      (fun x ↦ φ.value (timeBoundary t ht x) i j) =
      ∫ x : ↥disk, φ.value (timeBoundary t ht x) i j * g x.val i j ∂spatialMeasure := by
    intro i j
    apply MatrixTransport.signedPair_withDensityᵥ spatialMeasure
      (((continuous_apply j).comp ((continuous_apply i).comp
        (hg.comp continuous_subtype_val))).measurable) (hI i j)
      (((continuous_apply j).comp ((continuous_apply i).comp F.continuous)).measurable)
    let Fij : C(↥disk, ℝ) := ⟨fun x ↦ F x i j,
      (continuous_apply j).comp ((continuous_apply i).comp F.continuous)⟩
    refine ⟨‖Fij‖, ?_⟩
    intro x
    change |Fij x| ≤ ‖Fij‖
    simpa only [Real.norm_eq_abs] using Fij.norm_coe_le_norm x

  have hprod : ∀ i j, Integrable (fun x : ↥disk ↦
      φ.value (timeBoundary t ht x) i j * g x.val i j) spatialMeasure := fun i j ↦
    ((((continuous_apply j).comp ((continuous_apply i).comp F.continuous)).mul
      ((continuous_apply j).comp ((continuous_apply i).comp
        (hg.comp continuous_subtype_val))))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold MatrixTransport.ReactionZero.ClosedDomain.endpointPair
  simp_rw [hterm]
  have hsum : (∑ i, ∑ j, ∫ x : ↥disk,
      φ.value (timeBoundary t ht x) i j * g x.val i j ∂spatialMeasure) =
      ∫ x : ↥disk, ∑ i, ∑ j,
        φ.value (timeBoundary t ht x) i j * g x.val i j ∂spatialMeasure := by
    symm
    rw [integral_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hprod i j)]
    exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum Finset.univ (fun j _ ↦ hprod i j)
  rw [hsum]

  unfold nativeEndpointPair diskVolume
  rw [← integral_subtype_comap disk_measurableSet]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have he : zeroExtend φ.value (t, x.val) = φ.value (timeBoundary t ht x) :=
    zeroExtend_val φ.value (timeBoundary t ht x)
  dsimp only
  erw [he]
  unfold frob
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- Restricting the genuine native CE to ambient C¹ tests gives the old concrete CE. -/
theorem nativeCE_to_concrete {r : ℕ} (D : AdjointOperator 2 2 r) (Dstar : DStar r)
    (hD : ∀ F : ClosedC1Field, ∀ p, D.apply (closedFieldJet F) p = Dstar F p)
    (hcont : ∀ F : ClosedC1Field, Continuous (Dstar F))
    (g0 g1 : Spatial → Mat2) (hg0 : Continuous g0) (hg1 : Continuous g1)
    (path : MatrixPath r)
    (hCE : PaperContinuityEquation D (densityEndpoint g0) (densityEndpoint g1) path.coords) :
    ContinuityEquation Dstar g0 g1 path := by
  apply (continuityEquation_iff_signedCoordinatePair Dstar g0 g1 path hcont).mpr
  intro F
  have ht := hCE (closedFieldJet F)
  change MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1) path.coords
    (testField D (closedFieldJet F)) =
    MatrixTransport.ReactionZero.ClosedDomain.endpointPair (densityEndpoint g1)
      (closedFieldJet F) 1 ⟨zero_le_one, le_rfl⟩ -
    MatrixTransport.ReactionZero.ClosedDomain.endpointPair (densityEndpoint g0)
      (closedFieldJet F) 0 ⟨le_rfl, zero_le_one⟩ at ht
  erw [endpointPair_densityEndpoint g1 hg1, endpointPair_densityEndpoint g0 hg0] at ht
  have he : (testField D (closedFieldJet F) : MatrixTransport.Q → TransportCoord r → ℝ) =
      testTriplet Dstar F := by
    funext p c
    dsimp only [testField, testTriplet, ContinuousMap.coe_mk]
    erw [closedFieldJet_value, closedFieldJet_dt, hD]
    rcases c with ⟨i,j⟩ | ⟨i,j⟩ | ⟨i,j⟩ <;> rfl
  erw [he] at ht
  have hend (g : Spatial → Mat2) (t : ℝ) (ht' : t ∈ Icc (0 : ℝ) 1) :
      nativeEndpointPair g (closedFieldJet F) t = MatrixTransport.endpointPair g F t := by
    unfold nativeEndpointPair MatrixTransport.endpointPair
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem disk_measurableSet] with x hx
    rw [zeroExtend_of_mem _ ⟨ht', hx⟩]
    rfl
  erw [hend g1 1 ⟨zero_le_one, le_rfl⟩, hend g0 0 ⟨le_rfl, zero_le_one⟩] at ht
  simpa only [MatrixTransport.ReactionZero.Duality.coordinatePair,
    signedCoordinatePair, one_mul, endpointDifference] using ht

/-- The smooth endpoints in the genuine general Radon problem. -/
def densityProblem {r : ℕ} (D : AdjointOperator 2 2 r)
    (g0 g1 : Spatial → Mat2) (hg0 : Continuous g0) (hg1 : Continuous g1)
    (hPSD0 : ∀ x ∈ disk, (g0 x).PosSemidef) (hPSD1 : ∀ x ∈ disk, (g1 x).PosSemidef) :
    MatrixTransport.ReactionZero.Limit.Problem disk 2 r where
  operator := D
  initial := densityEndpoint g0
  terminal := densityEndpoint g1
  initial_positive := densityEndpoint_positive g0 hg0 hPSD0
  terminal_positive := densityEndpoint_positive g1 hg1 hPSD1

/-- Every native competitor is a concrete competitor of equal action. Consequently each
concrete lower bound is valid for the original full boundary-C¹ problem. -/
theorem concrete_minimum_le_native {r : ℕ} (D : AdjointOperator 2 2 r) (Dstar : DStar r)
    (hD : ∀ F : ClosedC1Field, ∀ p, D.apply (closedFieldJet F) p = Dstar F p)
    (hcont : ∀ F : ClosedC1Field, Continuous (Dstar F))
    (g0 g1 : Spatial → Mat2) (hg0 : Continuous g0) (hg1 : Continuous g1)
    (hPSD0 : ∀ x ∈ disk, (g0 x).PosSemidef) (hPSD1 : ∀ x ∈ disk, (g1 x).PosSemidef) :
    wbSquared Dstar g0 g1 ≤ MatrixTransport.ReactionZero.Limit.minimumValue
      (densityProblem D g0 g1 hg0 hg1 hPSD0 hPSD1) 1 1 := by
  apply le_iInf
  intro μ
  apply le_iInf
  intro hμ
  let path : MatrixPath r := ⟨μ,hμ.1⟩
  have hCE := nativeCE_to_concrete D Dstar hD hcont g0 g1 hg0 hg1 path hμ.2
  have h := wbSquared_le_action Dstar g0 g1 path hCE
  erw [action_identity]
  exact h

/-- Density formulation of the native CE with the actual scalar coordinate integrals. -/
theorem nativeCE_of_density_integral {r : ℕ} (D : AdjointOperator 2 2 r)
    (g0 g1 : Spatial → Mat2) (hg0 : Continuous g0) (hg1 : Continuous g1)
    (path : MatrixPath r) (z : TransportCoord r → MatrixTransport.Q → ℝ)
    (hzM : ∀ c, Measurable (z c)) (hzI : ∀ c, Integrable (z c) volumeQ)
    (hcoords : ∀ c, path.coords c = volumeQ.withDensityᵥ (z c))
    (hInt : ∀ φ : ClosedC1Jet disk 2,
      (∫ q, weightedPair (fun _ ↦ 1) (testField D φ q) (fun c ↦ z c q) ∂volumeQ) =
        nativeEndpointPair g1 φ 1 - nativeEndpointPair g0 φ 0) :
    PaperContinuityEquation D (densityEndpoint g0) (densityEndpoint g1) path.coords := by
  intro φ
  change MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1) path.coords
    (testField D φ) =
    MatrixTransport.ReactionZero.ClosedDomain.endpointPair (densityEndpoint g1) φ 1
      ⟨zero_le_one,le_rfl⟩ -
    MatrixTransport.ReactionZero.ClosedDomain.endpointPair (densityEndpoint g0) φ 0
      ⟨le_rfl,zero_le_one⟩
  erw [endpointPair_densityEndpoint g1 hg1, endpointPair_densityEndpoint g0 hg0]
  let a : MatrixTransport.Q → TransportCoord r → ℝ := testField D φ
  have ha : Continuous a := (testField D φ).continuous
  have hm : ∀ c, Measurable (fun q ↦ a q c) := fun c ↦
    ((continuous_apply c).comp ha).measurable
  have hb := exists_coord_bound a ha
  have hpair : MatrixTransport.ReactionZero.Duality.coordinatePair (fun _ ↦ 1) path.coords a =
      canonicalPair r path.coords a := by
    simpa only [MatrixTransport.ReactionZero.Duality.coordinatePair, one_mul, signedCoordinatePair]
      using signedCoordinatePair_eq_canonicalPair r path.coords a hm hb
  erw [hpair]
  have hμ : path.coords = fun c ↦ volumeQ.withDensityᵥ (z c) := funext hcoords
  rw [hμ, canonicalPair_withDensityᵥ r volumeQ z hzM hzI a hm hb]
  exact hInt φ

theorem integrable_nativeEndpoint (g : Spatial → Mat2) (hg : Continuous g)
    (φ : ClosedC1Jet disk 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun x ↦ frob (g x) (zeroExtend φ.value (t,x))) diskVolume := by
  have hv (i j : Fin 2) : ContinuousOn (fun x : Spatial ↦ zeroExtend φ.value (t,x) i j) disk :=
    continuousOn_pi.mp (continuousOn_pi.mp ((continuousOn_zeroExtend φ.value).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx ↦ Set.mk_mem_prod ht hx)) i) j
  have hc : ContinuousOn (fun x ↦ frob (g x) (zeroExtend φ.value (t,x))) disk := by
    unfold frob
    exact continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
      (((continuous_apply j).comp ((continuous_apply i).comp hg)).continuousOn.mul (hv i j))
  exact hc.integrableOn_compact disk_isCompact

/-- The original affine-in-time mass identity is integrated against the actual cylinder volume. -/
theorem integral_nativeTime_eq_endpoint (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (φ : ClosedC1Jet disk 2) :
    (∫ q : MatrixTransport.Q, nativeTimeIntegrand ρ φ q.val ∂volumeQ) =
      nativeEndpointPair (fun x ↦ MatrixTransport.density (ρ x)) φ 1 -
        nativeEndpointPair (fun _ ↦ MatrixTransport.density 0) φ 0 := by
  rw [integral_volumeQ_eq_space_time _ (continuousOn_nativeTimeIntegrand ρ hρ φ)]
  have hI : ∀ᵐ x ∂diskVolume,
      (∫ t in Icc (0 : ℝ) 1, nativeTimeIntegrand ρ φ (t,x)) =
      frob (MatrixTransport.density (ρ x)) (zeroExtend φ.value (1,x)) -
        frob (MatrixTransport.density 0) (zeroExtend φ.value (0,x)) := by
    filter_upwards [ae_restrict_mem disk_measurableSet] with x hx
    exact integral_nativeTimeIntegrand ρ φ hx
  rw [integral_congr_ae hI]
  exact integral_sub
    (integrable_nativeEndpoint _ (by exact (by
      apply continuous_matrix
      intro i j
      simp only [MatrixTransport.density_apply]
      split_ifs <;> first | exact continuous_const | exact continuous_const.add hρ)) φ ⟨zero_le_one,le_rfl⟩)
    (integrable_nativeEndpoint _ continuous_const φ ⟨le_rfl,zero_le_one⟩)

/-- The spatial identity holds for almost every time; the two endpoint times have zero volume. -/
theorem integral_nativeAffine_eq_endpoint (m : ℕ) (ε : ℝ) (φ : ClosedC1Jet disk 2) :
    (∫ q : MatrixTransport.Q, nativeAffineIntegrand m ε φ q.val ∂volumeQ) =
      nativeEndpointPair (fun x ↦ MatrixTransport.density (ε * endpointWave m x)) φ 1 -
        nativeEndpointPair (fun _ ↦ MatrixTransport.density 0) φ 0 := by
  have hc : Continuous (fun x ↦ ε * endpointWave m x) := continuous_const.mul (endpointWave_continuous m)
  have he : (∫ q : MatrixTransport.Q, nativeAffineIntegrand m ε φ q.val ∂volumeQ) =
      ∫ q : MatrixTransport.Q, nativeTimeIntegrand (fun x ↦ ε * endpointWave m x) φ q.val ∂volumeQ := by
    rw [integral_volumeQ_eq_time_space _ (continuousOn_nativeAffineIntegrand m ε φ),
      integral_volumeQ_eq_time_space _ (continuousOn_nativeTimeIntegrand _ hc φ)]
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc :
      Ioo (0 : ℝ) 1 =ᵐ[volume] Icc (0 : ℝ) 1)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact integral_nativeAffine_space m ε φ ht
  rw [he]
  exact integral_nativeTime_eq_endpoint _ hc φ

/-- Native full-operator spatial derivative block. -/
theorem fullOperator_column_one (φ : ClosedC1Jet disk 2) (p : MatrixTransport.Q) (i : Fin 2) :
    fullOperator.apply φ p i 1 = φ.dx 0 p i 1 := by
  change (fullZeroLinear (φ.value p) + ∑ j : Fin 2, fullPartialLinear j (φ.dx j p)) i 1 = _
  rw [Fin.sum_univ_two]
  simp [fullZeroLinear_apply, fullPartialLinear_apply, fullCol]

/-- Exact affine wave continuity equation for every original native boundary-C¹ test. -/
theorem affinePath_nativeCE (m : ℕ) (ε : ℝ) :
    PaperContinuityEquation fullOperator
      (densityEndpoint (fun _ ↦ MatrixTransport.density 0))
      (densityEndpoint (fun x ↦ MatrixTransport.density (ε * endpointWave m x)))
      (affinePath m ε).coords := by
  have hg : Continuous (fun x ↦ MatrixTransport.density (ε * endpointWave m x)) := by
    apply continuous_matrix
    intro i j
    simp only [MatrixTransport.density_apply]
    split_ifs <;> first | exact continuous_const | exact
      (continuous_const.add (continuous_const.mul (endpointWave_continuous m)))
  apply nativeCE_of_density_integral fullOperator _ _ continuous_const hg (affinePath m ε)
    (fun c q ↦ affineTriplet m ε q c) (measurable_affineTriplet_coord m ε)
    (integrable_affineTriplet_coord m ε) (fun c ↦ rfl)
  intro φ
  rw [← integral_nativeAffine_eq_endpoint m ε φ]
  apply integral_congr_ae
  apply ae_of_all
  intro q
  have hp : testField fullOperator φ q =
      packTriplet (φ.dt q) (fullOperator.apply φ q) (φ.value q) := by
    funext c
    rcases c with ⟨i,j⟩ | ⟨i,j⟩ | ⟨i,j⟩ <;> rfl
  dsimp only
  erw [hp]
  unfold affineTriplet
  rw [weightedPair_packTriplet]
  simp only [mass_packTriplet, flux_packTriplet, reaction_packTriplet,
    frob_density_diag, frob_singleFlux, fullOperator_column_one]
  have hz : frob (0 : Mat2) (φ.value q) = 0 := by simp [frob]
  rw [hz]
  unfold nativeAffineIntegrand
  erw [zeroExtend_val φ.dt q, zeroExtend_val (φ.dx 0) q]
  ring

/-- The pure reaction competitor also tests against the entire native class. -/
theorem reactionPath_nativeCE (ρ : Spatial → ℝ) (hρ : Continuous ρ) :
    PaperContinuityEquation LiZouTransport.Examples.kbOp
      (densityEndpoint (fun _ ↦ MatrixTransport.density 0))
      (densityEndpoint (fun x ↦ MatrixTransport.density (ρ x)))
      (reactionPath ρ).coords := by
  have hg : Continuous (fun x ↦ MatrixTransport.density (ρ x)) := by
    apply continuous_matrix
    intro i j
    simp only [MatrixTransport.density_apply]
    split_ifs <;> first | exact continuous_const | exact continuous_const.add hρ
  apply nativeCE_of_density_integral LiZouTransport.Examples.kbOp _ _ continuous_const hg
    (reactionPath ρ) (fun c q ↦ reactionTriplet ρ q c) (measurable_reactionTriplet_coord ρ hρ)
    (integrable_reactionTriplet_coord ρ hρ) (fun c ↦ rfl)
  intro φ
  rw [← integral_nativeTime_eq_endpoint ρ hρ φ]
  apply integral_congr_ae
  apply ae_of_all
  intro q
  have hp : testField LiZouTransport.Examples.kbOp φ q =
      packTriplet (φ.dt q) (LiZouTransport.Examples.kbOp.apply φ q) (φ.value q) := by
    funext c
    rcases c with ⟨i,j⟩ | ⟨i,j⟩ | ⟨i,j⟩ <;> rfl
  dsimp only
  erw [hp]
  unfold reactionTriplet
  rw [weightedPair_packTriplet]
  simp only [mass_packTriplet, flux_packTriplet, reaction_packTriplet,
    frob_density_diag, frob_reaction_E]
  have hz : frob (0 : Flux 1) (LiZouTransport.Examples.kbOp.apply φ q) = 0 := by simp [frob]
  rw [hz]
  unfold nativeTimeIntegrand
  erw [zeroExtend_val φ.dt q, zeroExtend_val φ.value q]
  ring

theorem continuous_density_comp (ρ : Spatial → ℝ) (hρ : Continuous ρ) :
    Continuous (fun x ↦ MatrixTransport.density (ρ x)) := by
  apply continuous_matrix
  intro i j
  simp only [MatrixTransport.density_apply]
  split_ifs <;> first | exact continuous_const | exact continuous_const.add hρ

theorem density_posSemidef_of_bound (ρ : Spatial → ℝ) (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ))
    (x : Spatial) : (MatrixTransport.density (ρ x)).PosSemidef := by
  exact psd_diag2 1 (1 + ρ x) zero_le_one (by have h := (abs_le.mp (hb x)).1; linarith)

theorem density_zero_posSemidef : (MatrixTransport.density 0).PosSemidef := by
  simpa [MatrixTransport.density] using psd_diag2 1 1 zero_le_one zero_le_one

/-- Native general problem for the uniformly positive smooth densities. -/
def smoothProblem {r : ℕ} (D : AdjointOperator 2 2 r) (ρ : Spatial → ℝ)
    (hρ : Continuous ρ) (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ)) :
    MatrixTransport.ReactionZero.Limit.Problem disk 2 r :=
  densityProblem D (fun _ ↦ MatrixTransport.density 0)
    (fun x ↦ MatrixTransport.density (ρ x)) continuous_const (continuous_density_comp ρ hρ)
    (fun _ _ ↦ density_zero_posSemidef)
    (fun x _ ↦ density_posSemidef_of_bound ρ hb x)

def smoothValue {r : ℕ} (D : AdjointOperator 2 2 r) (ρ : Spatial → ℝ)
    (hρ : Continuous ρ) (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ)) : ℝ≥0∞ :=
  MatrixTransport.ReactionZero.Limit.minimumValue (smoothProblem D ρ hρ hb) 1 1

/-- Original all-Radon minimum: exact existing full-operator upper bound. -/
theorem full_native_upper (m : ℕ) (ε : ℝ)
    (hb : ∀ x, |ε * endpointWave m x| ≤ (1 / 2 : ℝ)) :
    smoothValue fullOperator (fun x ↦ ε * endpointWave m x)
      (continuous_const.mul (endpointWave_continuous m)) hb ≤
      ENNReal.ofReal (Real.pi * ε ^ 2 / waveNumber m ^ 2) := by
  have hGood : MatrixTransport.ReactionZero.Limit.Good
      (smoothProblem fullOperator (fun x ↦ ε * endpointWave m x)
        (continuous_const.mul (endpointWave_continuous m)) hb) (affinePath m ε).coords :=
    ⟨(affinePath m ε).massSymmetry, affinePath_nativeCE m ε⟩
  have hmin : smoothValue fullOperator (fun x ↦ ε * endpointWave m x)
      (continuous_const.mul (endpointWave_continuous m)) hb ≤
      MatrixTransport.ReactionZero.action (1 : Matrix (Fin 8) (Fin 8) ℝ) 1 (affinePath m ε).coords :=
    iInf_le_of_le (affinePath m ε).coords (iInf_le_of_le hGood le_rfl)
  exact hmin.trans ((action_identity 8 _).le.trans (affinePath_action_le m ε hb))

/-- Original all-Radon minimum: the finite KB upper bound of the reaction path. -/
theorem kb_native_upper (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ)) :
    smoothValue LiZouTransport.Examples.kbOp ρ hρ hb ≤ ENNReal.ofReal (Real.pi / 4) := by
  have hGood : MatrixTransport.ReactionZero.Limit.Good
      (smoothProblem LiZouTransport.Examples.kbOp ρ hρ hb) (reactionPath ρ).coords :=
    ⟨(reactionPath ρ).massSymmetry, reactionPath_nativeCE ρ hρ⟩
  have hmin : smoothValue LiZouTransport.Examples.kbOp ρ hρ hb ≤
      MatrixTransport.ReactionZero.action (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (reactionPath ρ).coords :=
    iInf_le_of_le (reactionPath ρ).coords (iInf_le_of_le hGood le_rfl)
  exact hmin.trans ((action_identity 1 _).le.trans (reactionPath_action_le ρ hρ hb))

/-- The concrete KB lower estimate applies without weakening the original native test class. -/
theorem kb_concrete_lower_native (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ)) :
    wbSquared KBDstar (fun _ ↦ MatrixTransport.density 0)
      (fun x ↦ MatrixTransport.density (ρ x)) ≤
        smoothValue LiZouTransport.Examples.kbOp ρ hρ hb :=
  concrete_minimum_le_native LiZouTransport.Examples.kbOp KBDstar kbOperator_on_closedField
    continuous_KBstar _ _ continuous_const (continuous_density_comp ρ hρ)
    (fun _ _ ↦ density_zero_posSemidef)
    (fun x _ ↦ density_posSemidef_of_bound ρ hb x)

/-- The original smooth separation construction now has the original general Radon minima
and the full native closed-domain boundary-C¹ continuity equation on both sides. -/
theorem exists_native_smooth_positive_separation :
    ∃ N : ℕ, ∃ c : ℝ, ∃ hb : ∀ j x,
      |(1 / 4 : ℝ) * endpointWave (j + N) x| ≤ (1 / 2 : ℝ),
      0 < c ∧
      (∀ j, ContDiff ℝ ∞ (separatedEndpoint N j)) ∧
      (∀ j x,
        LoewnerLE ((1 / 2 : ℝ) • (1 : Mat2)) (separatedEndpoint N j x) ∧
        LoewnerLE (separatedEndpoint N j x) ((3 / 2 : ℝ) • (1 : Mat2))) ∧
      weakStarConverges (separatedEndpoint N) baseEndpoint ∧
      Tendsto (fun j ↦ smoothValue fullOperator
        (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
        (continuous_const.mul (endpointWave_continuous (j + N))) (hb j)) atTop (𝓝 0) ∧
      (∀ j, ENNReal.ofReal c ≤ smoothValue LiZouTransport.Examples.kbOp
        (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
        (continuous_const.mul (endpointWave_continuous (j + N))) (hb j) ∧
        smoothValue LiZouTransport.Examples.kbOp
        (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
        (continuous_const.mul (endpointWave_continuous (j + N))) (hb j) ≤
          ENNReal.ofReal (Real.pi / 4)) ∧
      ¬ Tendsto (fun j ↦ smoothValue LiZouTransport.Examples.kbOp
        (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
        (continuous_const.mul (endpointWave_continuous (j + N))) (hb j)) atTop (𝓝 0) := by
  obtain ⟨c,hc,hcLower⟩ := exists_positive_KB_lower
  obtain ⟨N2,hN2⟩ := Filter.eventually_atTop.1 hcLower
  obtain ⟨N0,hN0⟩ := exists_uniform_endpointWave_bound
  obtain ⟨N1,hN1⟩ := exists_uniform_waveEndpoint_bounds
  let N := max N0 (max N1 N2)
  have hN0' : N0 ≤ N := le_max_left _ _
  have hN1' : N1 ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN2' : N2 ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hb : ∀ j x, |(1 / 4 : ℝ) * endpointWave (j + N) x| ≤ (1 / 2 : ℝ) := by
    intro j x
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have h := hN0 (j + N) (by omega) x
    linarith
  have hlo : ∀ j, ENNReal.ofReal c ≤ smoothValue LiZouTransport.Examples.kbOp
      (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
      (continuous_const.mul (endpointWave_continuous (j + N))) (hb j) := by
    intro j
    exact (hN2 (j + N) (by omega)).trans
      (kb_concrete_lower_native _ (continuous_const.mul (endpointWave_continuous (j + N))) (hb j))
  refine ⟨N,c,hb,hc,?_,?_,?_,?_,?_,?_⟩
  · intro j; exact waveEndpoint_contDiff (j + N)
  · intro j x; exact hN1 (j + N) (by omega) x
  · intro Φ; exact (waveEndpoint_weakStarConverges Φ).comp (tendsto_add_atTop_nat N)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (tendsto_ennreal_upper_bound.comp (tendsto_add_atTop_nat N))
      (Filter.Eventually.of_forall fun _ ↦ bot_le)
    exact Filter.Eventually.of_forall fun j ↦
      (full_native_upper (j + N) (1 / 4) (hb j)).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  · intro j
    exact ⟨hlo j, kb_native_upper _ (continuous_const.mul (endpointWave_continuous (j + N))) (hb j)⟩
  · intro ht
    have hz : ENNReal.ofReal c ≤ 0 := ge_of_tendsto' ht hlo
    exact absurd hz (not_le.mpr (ENNReal.ofReal_pos.mpr hc))

/-- No finite uniform squared-value comparison holds along the genuine native sequence. -/
theorem no_native_eventual_uniform_comparison :
    ∃ N : ℕ, ∃ hb : ∀ j x,
      |(1 / 4 : ℝ) * endpointWave (j + N) x| ≤ (1 / 2 : ℝ),
      ∀ C : ℝ, ¬ (∀ᶠ j : ℕ in atTop,
        smoothValue LiZouTransport.Examples.kbOp
          (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
          (continuous_const.mul (endpointWave_continuous (j + N))) (hb j) ≤
        ENNReal.ofReal C * smoothValue fullOperator
          (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
          (continuous_const.mul (endpointWave_continuous (j + N))) (hb j)) := by
  obtain ⟨N,c,hb,hc,_,_,_,hfull,hkb,_⟩ := exists_native_smooth_positive_separation
  refine ⟨N,hb,?_⟩
  intro C hcompare
  have hmul : Tendsto (fun j ↦ ENNReal.ofReal C * smoothValue fullOperator
      (fun x ↦ (1 / 4 : ℝ) * endpointWave (j + N) x)
      (continuous_const.mul (endpointWave_continuous (j + N))) (hb j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C)
      hfull (Or.inr ENNReal.ofReal_ne_top)
  have hzero : ENNReal.ofReal c ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hmul (by
    filter_upwards [hcompare] with j hj
    exact (hkb j).1.trans hj)
  exact absurd hzero (not_le.mpr (ENNReal.ofReal_pos.mpr hc))

#print axioms densityEndpoint_positive
#print axioms endpointPair_densityEndpoint
#print axioms nativeCE_to_concrete
#print axioms concrete_minimum_le_native
#print axioms nativeCE_of_density_integral
#print axioms affinePath_nativeCE
#print axioms reactionPath_nativeCE
#print axioms full_native_upper
#print axioms kb_native_upper
#print axioms kb_concrete_lower_native
#print axioms exists_native_smooth_positive_separation
#print axioms no_native_eventual_uniform_comparison
end LiZouTransport.NativeSeparation
