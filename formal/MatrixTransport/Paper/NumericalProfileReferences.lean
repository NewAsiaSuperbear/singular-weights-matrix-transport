import MatrixTransport.Paper.ExampleBridges
import MatrixTransport.Paper.HubLimit

/-! # Continuum hub reference for the recorded numerical profiles

The two literal smooth profiles on [0,1] have total matrix I, trace density two,
and second trace moments 1/6 about the midpoint. The native hub bound therefore
has coefficient 1/3. No cell averages or solver values enter these computations.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.NumericalProfileReferences
open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain
open MatrixTransport.ReactionZero.Limit MatrixTransport.EntrywiseBures
open LiZouTransport.FluxNoncompactness LiZouTransport.HubLimit

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

def diagSign : Mat := !![1,0;0,-1]
def swap : Mat := !![0,1;1,0]

def profile0Scalar (s : ℝ) : Mat := 1 + (Real.cos (2 * Real.pi * s) / 4) • diagSign
def profile1Scalar (s : ℝ) : Mat := 1 + (Real.sin (2 * Real.pi * s) / 4) • swap

theorem continuous_profile0Scalar : Continuous profile0Scalar := by
  exact continuous_const.add (((Real.continuous_cos.comp
    (continuous_const.mul continuous_id)).div_const 4).smul continuous_const)

theorem continuous_profile1Scalar : Continuous profile1Scalar := by
  exact continuous_const.add (((Real.continuous_sin.comp
    (continuous_const.mul continuous_id)).div_const 4).smul continuous_const)

/-- The actual continuum cosine profile, with the spatial coordinate of [0,1]. -/
def profile0 : C(↥FluxNoncompactness.unitInterval,Mat) := ⟨fun x ↦ profile0Scalar (x.val 0),
  continuous_profile0Scalar.comp ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
    continuous_subtype_val)⟩

/-- The actual continuum sine profile. -/
def profile1 : C(↥FluxNoncompactness.unitInterval,Mat) := ⟨fun x ↦ profile1Scalar (x.val 0),
  continuous_profile1Scalar.comp ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
    continuous_subtype_val)⟩

theorem profile0_trace (s : ℝ) : (profile0Scalar s).trace = 2 := by
  simp [profile0Scalar,diagSign,Matrix.trace_fin_two]

theorem profile1_trace (s : ℝ) : (profile1Scalar s).trace = 2 := by
  simp [profile1Scalar,swap,Matrix.trace_fin_two]

theorem profile0_lower (s : ℝ) :
    (profile0Scalar s - (3 / 4 : ℝ) • (1 : Mat)).PosSemidef := by
  have hc := abs_le.mp (Real.abs_cos_le_one (2 * Real.pi * s))
  convert MatrixTransport.psd_diag2 (1 / 4 + Real.cos (2 * Real.pi * s) / 4)
    (1 / 4 - Real.cos (2 * Real.pi * s) / 4) (by linarith) (by linarith) using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [profile0Scalar,diagSign] <;> ring

/-- A diagonalization expressed as a sum of positive rank-one Gram matrices. -/
theorem swap_lower (u : ℝ) (hu : |u| ≤ (1 / 4 : ℝ)) :
    ((1 / 4 : ℝ) • (1 : Mat) + u • swap).PosSemidef := by
  let P : Mat := !![1,0;1,0]
  let Q : Mat := !![1,0;-1,0]
  have hp : 0 ≤ (1 / 4 + u) / 2 := by have h := (abs_le.mp hu).1; linarith
  have hq : 0 ≤ (1 / 4 - u) / 2 := by have h := (abs_le.mp hu).2; linarith
  have h := ((posSemidef_gram P).smul hp).add ((posSemidef_gram Q).smul hq)
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [gram,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
    <;> norm_num [P,Q,swap] <;> ring

theorem profile1_lower (s : ℝ) :
    (profile1Scalar s - (3 / 4 : ℝ) • (1 : Mat)).PosSemidef := by
  have h := swap_lower (Real.sin (2 * Real.pi * s) / 4) (by
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by norm_num))
  convert h using 1
  ext i j
  simp [profile1Scalar,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply]
  ring

theorem profile0_positive (x : ↥FluxNoncompactness.unitInterval) : (profile0 x).PosSemidef := by
  have h := (profile0_lower (x.val 0)).add
    (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 3 / 4))
  simpa only [profile0,ContinuousMap.coe_mk,sub_add_cancel] using h

theorem profile1_positive (x : ↥FluxNoncompactness.unitInterval) : (profile1 x).PosSemidef := by
  have h := (profile1_lower (x.val 0)).add
    (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 3 / 4))
  simpa only [profile1,ContinuousMap.coe_mk,sub_add_cancel] using h

/-- Strict positivity follows from the common 3/4 identity lower bound. -/
theorem profile0_posDef (x : ↥FluxNoncompactness.unitInterval) : (profile0 x).PosDef := by
  have h := Matrix.PosDef.posSemidef_add (profile0_lower (x.val 0))
    (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 3 / 4))
  simpa only [profile0,ContinuousMap.coe_mk,sub_add_cancel] using h

theorem profile1_posDef (x : ↥FluxNoncompactness.unitInterval) : (profile1 x).PosDef := by
  have h := Matrix.PosDef.posSemidef_add (profile1_lower (x.val 0))
    (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 3 / 4))
  simpa only [profile1,ContinuousMap.coe_mk,sub_add_cancel] using h

/-- Continuous densities define finite signed endpoint measures on the real interval. -/
def profileEndpoint (G : C(↥FluxNoncompactness.unitInterval,Mat)) :
    (Fin 2 × Fin 2) → SignedMeasure ↥FluxNoncompactness.unitInterval :=
  fun c ↦ spatialLebesgue.withDensityᵥ (fun x ↦ G x c.1 c.2)

theorem profile_integrable (G : C(↥FluxNoncompactness.unitInterval,Mat)) (i j : Fin 2) :
    Integrable (fun x ↦ G x i j) spatialLebesgue :=
  ((continuous_apply j).comp ((continuous_apply i).comp G.continuous)).continuous_integrable

theorem profileEndpoint_positive (G : C(↥FluxNoncompactness.unitInterval,Mat))
    (hG : ∀ x, (G x).PosSemidef) : EndpointPositiveSemidefinite (profileEndpoint G) := by
  intro B hB
  have he : (fun i j ↦ profileEndpoint G (i,j) B) =
      fun i j ↦ ∫ x in B, G x i j ∂spatialLebesgue := by
    funext i j
    exact withDensityᵥ_apply (profile_integrable G i j) hB
  rw [he]
  exact MatrixTransport.ReactionZero.MatrixPositivity.posSemidef_setIntegral
    G (profile_integrable G) (ae_of_all _ hG) B

theorem profileEndpoint_total (G : C(↥FluxNoncompactness.unitInterval,Mat)) (i j : Fin 2) :
    totalMatrix (profileEndpoint G) i j = ∫ x, G x i j ∂spatialLebesgue := by
  unfold totalMatrix profileEndpoint
  rw [withDensityᵥ_apply (profile_integrable G i j) MeasurableSet.univ,setIntegral_univ]

theorem line_coordinate (s : ℝ) : line s 0 = s := by
  simp [line]

/-- Integration of a continuous scalar function against actual interval Lebesgue measure. -/
theorem integral_spatial_scalar (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x : ↥FluxNoncompactness.unitInterval, f (x.val 0) ∂spatialLebesgue) =
      ∫ s in (0 : ℝ)..1, f s := by
  have hc : Continuous (fun x : ↥FluxNoncompactness.unitInterval ↦ f (x.val 0)) :=
    hf.comp ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp continuous_subtype_val)
  calc
    (∫ x : ↥FluxNoncompactness.unitInterval, f (x.val 0) ∂spatialLebesgue) =
        ∫ s : UnitI, f ((intervalPoint s).val 0) ∂unitTime :=
      integral_map (μ := unitTime) continuous_intervalPoint.measurable.aemeasurable
        (f := fun x : ↥FluxNoncompactness.unitInterval ↦ f (x.val 0))
        hc.aestronglyMeasurable
    _ = _ := by simpa only [intervalPoint,line_coordinate] using integral_unitTime f

theorem integral_cos_profile :
    (∫ x : ↥FluxNoncompactness.unitInterval, Real.cos (2 * Real.pi * x.val 0)
      ∂spatialLebesgue) = 0 := by
  rw [integral_spatial_scalar (fun s ↦ Real.cos (2 * Real.pi * s))
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)),
    intervalIntegral.integral_comp_mul_left Real.cos (by positivity : 2 * Real.pi ≠ 0),
    _root_.integral_cos]
  simp [Real.sin_two_pi]

theorem integral_sin_profile :
    (∫ x : ↥FluxNoncompactness.unitInterval, Real.sin (2 * Real.pi * x.val 0)
      ∂spatialLebesgue) = 0 := by
  rw [integral_spatial_scalar (fun s ↦ Real.sin (2 * Real.pi * s))
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)),
    intervalIntegral.integral_comp_mul_left Real.sin (by positivity : 2 * Real.pi ≠ 0),
    _root_.integral_sin]
  simp [Real.cos_two_pi]

theorem continuous_coordinate :
    Continuous (fun x : ↥FluxNoncompactness.unitInterval ↦ x.val 0) :=
  (EuclideanSpace.proj (0 : Fin 1)).continuous.comp continuous_subtype_val

theorem total_profile0 : totalMatrix (profileEndpoint profile0) = (1 : Mat) := by
  ext i j
  rw [profileEndpoint_total]
  have hi : Integrable (fun x : ↥FluxNoncompactness.unitInterval ↦
      Real.cos (2 * Real.pi * x.val 0) / 4) spatialLebesgue :=
    (Continuous.div_const (Real.continuous_cos.comp
      (continuous_const.mul continuous_coordinate)) 4).continuous_integrable
  change (∫ x : ↥FluxNoncompactness.unitInterval,
    (1 : Mat) i j + (Real.cos (2 * Real.pi * x.val 0) / 4) * diagSign i j
      ∂spatialLebesgue) = _
  rw [integral_add (integrable_const _) (hi.mul_const _),integral_mul_const,
    integral_div,integral_cos_profile]
  simp [integral_const,measureReal_def,spatialLebesgue_univ]

theorem total_profile1 : totalMatrix (profileEndpoint profile1) = (1 : Mat) := by
  ext i j
  rw [profileEndpoint_total]
  have hi : Integrable (fun x : ↥FluxNoncompactness.unitInterval ↦
      Real.sin (2 * Real.pi * x.val 0) / 4) spatialLebesgue :=
    (Continuous.div_const (Real.continuous_sin.comp
      (continuous_const.mul continuous_coordinate)) 4).continuous_integrable
  change (∫ x : ↥FluxNoncompactness.unitInterval,
    (1 : Mat) i j + (Real.sin (2 * Real.pi * x.val 0) / 4) * swap i j
      ∂spatialLebesgue) = _
  rw [integral_add (integrable_const _) (hi.mul_const _),integral_mul_const,
    integral_div,integral_sin_profile]
  simp [integral_const,measureReal_def,spatialLebesgue_univ]


/-- Exact second trace moment of Lebesgue measure on [0,1] about its midpoint. -/
theorem integral_midpoint_second :
    (∫ s in (0 : ℝ)..1, 2 * (s - 1 / 2) ^ 2) = 1 / 6 := by
  have hf : (fun s : ℝ ↦ 2 * (s - 1 / 2) ^ 2) =
      fun s ↦ 2 * s ^ 2 - 2 * s + 1 / 2 := by funext s; ring
  have i0 : IntervalIntegrable (fun s : ℝ ↦ 2 * s ^ 2) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun s : ℝ ↦ 2 * s) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [hf,intervalIntegral.integral_add (i0.sub i1) (intervalIntegrable_const),
    intervalIntegral.integral_sub i0 i1,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  norm_num [_root_.integral_pow]

/-- Density pairing computes the actual endpoint's second trace moment. -/
theorem hubMoment_profile (G : C(↥FluxNoncompactness.unitInterval,Mat))
    (htrace : ∀ x, (G x).trace = 2) :
    hubMoment (profileEndpoint G) (line (1 / 2)) = 1 / 6 := by
  let f : C(↥FluxNoncompactness.unitInterval,ℝ) := hubDistSq (line (1 / 2))
  have hp (i : Fin 2) : MatrixTransport.signedPair (profileEndpoint G (i,i))
      (fun x ↦ ‖x.val - line (1 / 2)‖ ^ 2) =
      ∫ x, ‖x.val - line (1 / 2)‖ ^ 2 * G x i i ∂spatialLebesgue := by
    apply MatrixTransport.signedPair_withDensityᵥ spatialLebesgue
      (((continuous_apply i).comp ((continuous_apply i).comp G.continuous)).measurable)
      (profile_integrable G i i) f.continuous.measurable
      (hubDistSq_bounded (line (1 / 2)))
  have hi (i : Fin 2) : Integrable
      (fun x : ↥FluxNoncompactness.unitInterval ↦ ‖x.val - line (1 / 2)‖ ^ 2 * G x i i)
      spatialLebesgue :=
    (f.continuous.mul ((continuous_apply i).comp
      ((continuous_apply i).comp G.continuous))).continuous_integrable
  rw [hubMoment,Fin.sum_univ_two,hp,hp,← integral_add (hi 0) (hi 1)]
  have he : (fun x : ↥FluxNoncompactness.unitInterval ↦
      ‖x.val - line (1 / 2)‖ ^ 2 * G x 0 0 + ‖x.val - line (1 / 2)‖ ^ 2 * G x 1 1) =
      fun x ↦ 2 * ‖x.val - line (1 / 2)‖ ^ 2 := by
    funext x
    have ht := htrace x
    rw [Matrix.trace_fin_two] at ht
    nlinarith
  rw [he]
  have hc : Continuous (fun x : ↥FluxNoncompactness.unitInterval ↦
      2 * ‖x.val - line (1 / 2)‖ ^ 2) := continuous_const.mul f.continuous
  rw [spatialLebesgue]
  have hm := integral_map (μ := unitTime) continuous_intervalPoint.measurable.aemeasurable
    (f := fun x : ↥FluxNoncompactness.unitInterval ↦ 2 * ‖x.val - line (1 / 2)‖ ^ 2)
    hc.aestronglyMeasurable
  rw [hm]
  simp only [intervalPoint,norm_line_sub,sq_abs]
  rw [integral_unitTime (fun s : ℝ ↦ 2 * (s - 1 / 2) ^ 2)]
  exact integral_midpoint_second

theorem hubMoment_profile0 : hubMoment (profileEndpoint profile0) (line (1 / 2)) = 1 / 6 :=
  hubMoment_profile profile0 (fun x ↦ profile0_trace (x.val 0))

theorem hubMoment_profile1 : hubMoment (profileEndpoint profile1) (line (1 / 2)) = 1 / 6 :=
  hubMoment_profile profile1 (fun x ↦ profile1_trace (x.val 0))

/-- The original native interval problem with the literal two numerical profiles. -/
def profileProblem : Problem FluxNoncompactness.unitInterval 2 2 where
  operator := entrywiseDivergence 1 2
  initial := profileEndpoint profile0
  terminal := profileEndpoint profile1
  initial_positive := profileEndpoint_positive profile0 profile0_positive
  terminal_positive := profileEndpoint_positive profile1 profile1_positive

theorem profile_energy_zero : endpointEnergy (canonicalPSDSqrt 2) profileProblem (1 : Mat) = 0 := by
  unfold endpointEnergy profileProblem
  rw [total_profile0,total_profile1]
  exact LiZouTransport.ExampleBridges.buresValue_self (canonicalPSDSqrt 2) (1 : Mat)
    (by simp) Matrix.PosSemidef.one

theorem profile_hubConstant_sq : hubConstant intervalHub profileProblem ^ 2 = 1 / 3 := by
  unfold hubConstant
  change ((Real.sqrt (hubMoment (profileEndpoint profile0) (line (1 / 2))) +
    Real.sqrt (hubMoment (profileEndpoint profile1) (line (1 / 2)))) / Real.sqrt 2) ^ 2 = _
  rw [hubMoment_profile0,hubMoment_profile1,div_pow]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [h2]
  nlinarith

/-- The continuum dashed reference has exactly the coefficient used in the figure. -/
theorem profile_native_hub_bound (t : ℝ) (ht : 0 < t) :
    minimumValue profileProblem (t • (1 : Mat)) (1 : Mat) ≤ ENNReal.ofReal (1 / (3 * t ^ 2)) := by
  have h := minimumValue_le_hub_bound (canonicalPSDSqrt 2) intervalHub profileProblem rfl
    (H := (1 : Mat)) (by simp) (by simp) ht
  rw [profile_energy_zero,Real.sqrt_zero,zero_add,div_pow,profile_hubConstant_sq] at h
  rw [show (1 / 3 : ℝ) / t ^ 2 = 1 / (3 * t ^ 2) by ring] at h
  exact h

/-- The original continuum minima converge to their zero Bures reference. -/
theorem profile_native_limit :
    Tendsto (fun t : ℝ ↦ minimumValue profileProblem (t • (1 : Mat)) (1 : Mat))
      atTop (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ ↦ 1 / (3 * t ^ 2)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.pow 2).const_mul (1 / 3 : ℝ)
    have h' : Tendsto (fun t : ℝ ↦ (1 / 3 : ℝ) * t⁻¹ ^ 2) atTop (𝓝 0) := by
      simpa using h
    exact h'.congr (fun _ ↦ by ring)
  have hu : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (1 / (3 * t ^ 2))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using! ENNReal.tendsto_ofReal hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hu (Filter.Eventually.of_forall fun _ ↦ bot_le)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact profile_native_hub_bound t ht

#print axioms profile0_lower
#print axioms profile1_lower
#print axioms profile0_posDef
#print axioms profile1_posDef
#print axioms total_profile0
#print axioms total_profile1
#print axioms hubMoment_profile0
#print axioms hubMoment_profile1
#print axioms profile_energy_zero
#print axioms profile_hubConstant_sq
#print axioms profile_native_hub_bound
#print axioms profile_native_limit
end LiZouTransport.NumericalProfileReferences
