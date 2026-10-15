import MatrixTransport.Paper.NativeSeparationTime
import MatrixTransport.AffineContinuity

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.NativeSeparation
open MatrixTransport MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures

def nativeSlice (φ : ClosedC1Jet disk 2) (t : ℝ) (x : Spatial) : ℝ :=
  zeroExtend φ.value (t, x) 1 1

def nativeSliceD (φ : ClosedC1Jet disk 2) (t : ℝ) (x : Spatial) : ℝ :=
  zeroExtend (φ.dx 0) (t, x) 1 1

theorem continuousOn_nativeSlice (φ : ClosedC1Jet disk 2) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ContinuousOn (nativeSlice φ t) disk := by
  have h := (continuousOn_zeroExtend φ.value).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun x hx ↦ Set.mk_mem_prod ht hx)
  exact continuousOn_pi.mp (continuousOn_pi.mp h 1) 1

theorem continuousOn_nativeSliceD (φ : ClosedC1Jet disk 2) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ContinuousOn (nativeSliceD φ t) disk := by
  have h := (continuousOn_zeroExtend (φ.dx 0)).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun x hx ↦ Set.mk_mem_prod ht hx)
  exact continuousOn_pi.mp (continuousOn_pi.mp h 1) 1

theorem nativeSlice_hasLineDerivAt (φ : ClosedC1Jet disk 2) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {x : Spatial} (hx : x ∈ interior disk) :
    HasLineDerivAt ℝ (nativeSlice φ t) (nativeSliceD φ t x) x e1 := by
  let p : MatrixTransport.ReactionZero.ClosedDomain.Q disk :=
    ⟨(t, x), Ioo_subset_Icc_self ht, interior_subset hx⟩
  have hp : p.val ∈ interior (domain disk) := by
    rw [interior_domain_eq]; exact ⟨ht, hx⟩
  have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp (φ.space_deriv p 0 hp) 1) 1
  have he : zeroExtend (φ.dx 0) (t, x) = φ.dx 0 p := zeroExtend_val (φ.dx 0) p
  simpa only [HasLineDerivAt, nativeSlice, nativeSliceD, spaceLine, p, e1, he] using h

theorem chi_tsupport_subset_interior_disk : tsupport chi ⊆ interior disk := by
  exact chi_tsupport_subset.trans
    (Metric.isOpen_ball.subset_interior_iff.mpr ball_half_subset_disk)

/-- Integration by parts on the actual compact wave support uses only the native spatial
partial derivative, with no extension to a neighborhood of the boundary. -/
theorem integral_endpointWave_mul_nativeSlice (m : ℕ) (φ : ClosedC1Jet disk 2) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ x, endpointWave m x * nativeSlice φ t x ∂diskVolume) =
      -(∫ x, primitiveWave m x * nativeSliceD φ t x ∂diskVolume) := by
  have h1 : Integrable (fun x ↦ primitiveWave m x * nativeSlice φ t x) volume :=
    integrable_mul_of_continuousOn_disk _ _ (primitiveWave_continuous m)
      (primitiveWave_compact m) ((tsupport_primitiveWave_subset m).trans chi_tsupport_subset)
      (continuousOn_nativeSlice φ (Ioo_subset_Icc_self ht))
  have h2 : Integrable (fun x ↦ endpointWave m x * nativeSlice φ t x) volume :=
    integrable_mul_of_continuousOn_disk _ _ (endpointWave_continuous m)
      (endpointWave_compact m) ((tsupport_endpointWave_subset m).trans chi_tsupport_subset)
      (continuousOn_nativeSlice φ (Ioo_subset_Icc_self ht))
  have h3 : Integrable (fun x ↦ primitiveWave m x * nativeSliceD φ t x) volume :=
    integrable_mul_of_continuousOn_disk _ _ (primitiveWave_continuous m)
      (primitiveWave_compact m) ((tsupport_primitiveWave_subset m).trans chi_tsupport_subset)
      (continuousOn_nativeSliceD φ (Ioo_subset_Icc_self ht))
  have hf : ∀ x ∈ tsupport (nativeSlice φ t),
      HasLineDerivAt ℝ (primitiveWave m) (endpointWave m x) x e1 := by
    intro x _
    simpa only [fderiv_primitiveWave_e1] using
      (primitiveWave_differentiable m x).hasFDerivAt.hasLineDerivAt e1
  have hg : ∀ x ∈ tsupport (primitiveWave m),
      HasLineDerivAt ℝ (nativeSlice φ t) (nativeSliceD φ t x) x e1 :=
    fun x hx ↦ nativeSlice_hasLineDerivAt φ ht
      (chi_tsupport_subset_interior_disk (tsupport_primitiveWave_subset m hx))
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) h2 h3 h1 hf hg
  have eE : (∫ x in disk, endpointWave m x * nativeSlice φ t x) =
      ∫ x, endpointWave m x * nativeSlice φ t x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [endpointWave_eq_zero_of_not_mem_disk m x hx]; simp
  have eP : (∫ x in disk, primitiveWave m x * nativeSliceD φ t x) =
      ∫ x, primitiveWave m x * nativeSliceD φ t x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [primitiveWave_eq_zero_of_not_mem_disk m x hx]; simp
  unfold diskVolume
  rw [eE, eP]
  change (∫ x, primitiveWave m x * nativeSliceD φ t x) =
    -(∫ x, endpointWave m x * nativeSlice φ t x) at h
  linarith

def nativeTimeIntegrand (ρ : Spatial → ℝ) (φ : ClosedC1Jet disk 2) (p : MatrixTransport.Ambient) : ℝ :=
  zeroExtend φ.dt p 0 0 + zeroExtend φ.dt p 1 1 +
    ρ p.2 * (zeroExtend φ.value p 1 1 + p.1 * zeroExtend φ.dt p 1 1)

theorem integral_unitTime_Icc (f : ℝ → ℝ) :
    (∫ s : UnitI, f s.val ∂unitTime) = ∫ s in Icc (0 : ℝ) 1, f s := by
  rw [integral_unitTime, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc]

/-- The time-affine density identity holds for native tests at every point of the disk. -/
theorem integral_nativeTimeIntegrand (ρ : Spatial → ℝ) (φ : ClosedC1Jet disk 2)
    {x : Spatial} (hx : x ∈ disk) :
    (∫ s in Icc (0 : ℝ) 1, nativeTimeIntegrand ρ φ (s,x)) =
      frob (MatrixTransport.density (ρ x)) (zeroExtend φ.value (1,x)) -
        frob (MatrixTransport.density 0) (zeroExtend φ.value (0,x)) := by
  let x' : ↥disk := ⟨x,hx⟩
  let ins : UnitI → MatrixTransport.ReactionZero.ClosedDomain.Q disk :=
    fun s ↦ LiZouTransport.Boundary.timeInsert s x'
  have hins : Continuous ins := LiZouTransport.Boundary.continuous_timeInsert.comp
    (continuous_id.prodMk continuous_const)
  have hc (A : C(MatrixTransport.ReactionZero.ClosedDomain.Q disk, Mat2)) (i j : Fin 2) :
      Continuous (fun s : UnitI ↦ A (ins s) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (A.continuous.comp hins))
  have hi (A : C(MatrixTransport.ReactionZero.ClosedDomain.Q disk, Mat2)) (i j : Fin 2) :
      Integrable (fun s : UnitI ↦ A (ins s) i j) unitTime :=
    (hc A i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hip : Integrable (fun s : UnitI ↦
      φ.value (ins s) 1 1 + s.val * φ.dt (ins s) 1 1) unitTime :=
    ((hc φ.value 1 1).add (continuous_subtype_val.mul (hc φ.dt 1 1))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h0 := LiZouTransport.Boundary.timeResidual_zero diskHub φ 0 0 x'
  have h1 := LiZouTransport.Boundary.timeResidual_zero diskHub φ 1 1 x'
  have hp := integral_timeProduct diskHub φ 1 1 x'
  simp only [LiZouTransport.Boundary.timeResidual] at h0 h1
  have h0' : (∫ s, φ.dt (ins s) 0 0 ∂unitTime) =
      φ.value (timeBoundary 1 ⟨zero_le_one,le_rfl⟩ x') 0 0 -
        φ.value (timeBoundary 0 ⟨le_rfl,zero_le_one⟩ x') 0 0 := by linarith
  have h1' : (∫ s, φ.dt (ins s) 1 1 ∂unitTime) =
      φ.value (timeBoundary 1 ⟨zero_le_one,le_rfl⟩ x') 1 1 -
        φ.value (timeBoundary 0 ⟨le_rfl,zero_le_one⟩ x') 1 1 := by linarith
  rw [← integral_unitTime_Icc]
  have he : (fun s : UnitI ↦ nativeTimeIntegrand ρ φ (s.val,x)) =
      fun s ↦ φ.dt (ins s) 0 0 + φ.dt (ins s) 1 1 +
        ρ x * (φ.value (ins s) 1 1 + s.val * φ.dt (ins s) 1 1) := by
    funext s
    unfold nativeTimeIntegrand
    rw [zeroExtend_of_mem φ.dt (q := (s.val,x)) ⟨s.property,hx⟩,
      zeroExtend_of_mem φ.value (q := (s.val,x)) ⟨s.property,hx⟩]
    rfl
  rw [he]
  erw [integral_add ((hi φ.dt 0 0).add (hi φ.dt 1 1)) (hip.const_mul (ρ x)),
    integral_add (hi φ.dt 0 0) (hi φ.dt 1 1), integral_const_mul, h0',h1', hp]
  erw [frob_density_slice_eq, frob_density0_eq_diag,
    zeroExtend_of_mem φ.value (q := ((1 : ℝ),x)) ⟨⟨zero_le_one,le_rfl⟩,hx⟩,
    zeroExtend_of_mem φ.value (q := ((0 : ℝ),x)) ⟨⟨le_rfl,zero_le_one⟩,hx⟩]
  simp only [ins, timeBoundary, LiZouTransport.Boundary.timeInsert, x', ContinuousMap.coe_mk]
  ring

theorem continuousOn_nativeTimeIntegrand (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (φ : ClosedC1Jet disk 2) : ContinuousOn (nativeTimeIntegrand ρ φ) QSet := by
  have hd (i j : Fin 2) : ContinuousOn (fun p ↦ zeroExtend φ.dt p i j) QSet :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_zeroExtend φ.dt) i) j
  have hv : ContinuousOn (fun p ↦ zeroExtend φ.value p 1 1) QSet :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_zeroExtend φ.value) 1) 1
  exact ((hd 0 0).add (hd 1 1)).add
    ((hρ.comp continuous_snd).continuousOn.mul (hv.add (continuous_fst.continuousOn.mul (hd 1 1))))

def nativeAffineIntegrand (m : ℕ) (ε : ℝ) (φ : ClosedC1Jet disk 2)
    (p : MatrixTransport.Ambient) : ℝ :=
  zeroExtend φ.dt p 0 0 + zeroExtend φ.dt p 1 1 +
    p.1 * ε * endpointWave m p.2 * zeroExtend φ.dt p 1 1 -
      ε * primitiveWave m p.2 * zeroExtend (φ.dx 0) p 1 1

theorem continuousOn_nativeAffineIntegrand (m : ℕ) (ε : ℝ) (φ : ClosedC1Jet disk 2) :
    ContinuousOn (nativeAffineIntegrand m ε φ) QSet := by
  have hd (i j : Fin 2) : ContinuousOn (fun p ↦ zeroExtend φ.dt p i j) QSet :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_zeroExtend φ.dt) i) j
  have hx : ContinuousOn (fun p ↦ zeroExtend (φ.dx 0) p 1 1) QSet :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_zeroExtend (φ.dx 0)) 1) 1
  exact (((hd 0 0).add (hd 1 1)).add
    (((continuous_fst.continuousOn.mul continuousOn_const).mul
      ((endpointWave_continuous m).comp continuous_snd).continuousOn).mul (hd 1 1))).sub
    ((continuousOn_const.mul ((primitiveWave_continuous m).comp continuous_snd).continuousOn).mul hx)

/-- Spatial integration converts the actual transport pairing into the native time FTC. -/
theorem integral_nativeAffine_space (m : ℕ) (ε : ℝ) (φ : ClosedC1Jet disk 2)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ x, nativeAffineIntegrand m ε φ (t,x) ∂diskVolume) =
      ∫ x, nativeTimeIntegrand (fun x ↦ ε * endpointWave m x) φ (t,x) ∂diskVolume := by
  let B : Spatial → ℝ := fun x ↦ zeroExtend φ.dt (t,x) 0 0 + zeroExtend φ.dt (t,x) 1 1 +
    t * ε * endpointWave m x * zeroExtend φ.dt (t,x) 1 1
  have hdt (i j : Fin 2) : ContinuousOn (fun x : Spatial ↦ zeroExtend φ.dt (t,x) i j) disk := by
    exact continuousOn_pi.mp (continuousOn_pi.mp ((continuousOn_zeroExtend φ.dt).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx ↦ Set.mk_mem_prod (Ioo_subset_Icc_self ht) hx)) i) j
  have hBI : Integrable B diskVolume :=
    (((hdt 0 0).add (hdt 1 1)).add
      ((continuousOn_const.mul (endpointWave_continuous m).continuousOn).mul (hdt 1 1))).integrableOn_compact
      disk_isCompact
  have hPI : Integrable (fun x ↦ primitiveWave m x * nativeSliceD φ t x) diskVolume :=
    ((primitiveWave_continuous m).continuousOn.mul
      (continuousOn_nativeSliceD φ (Ioo_subset_Icc_self ht))).integrableOn_compact disk_isCompact
  have hEI : Integrable (fun x ↦ endpointWave m x * nativeSlice φ t x) diskVolume :=
    ((endpointWave_continuous m).continuousOn.mul
      (continuousOn_nativeSlice φ (Ioo_subset_Icc_self ht))).integrableOn_compact disk_isCompact
  have heA : (fun x ↦ nativeAffineIntegrand m ε φ (t,x)) =
      fun x ↦ B x - ε * (primitiveWave m x * nativeSliceD φ t x) := by
    funext x; unfold nativeAffineIntegrand B nativeSliceD; ring
  have heT : (fun x ↦ nativeTimeIntegrand (fun x ↦ ε * endpointWave m x) φ (t,x)) =
      fun x ↦ B x + ε * (endpointWave m x * nativeSlice φ t x) := by
    funext x; unfold nativeTimeIntegrand B nativeSlice; ring
  rw [heA, heT]
  erw [integral_sub hBI (hPI.const_mul ε), integral_add hBI (hEI.const_mul ε),
    integral_const_mul, integral_const_mul, integral_endpointWave_mul_nativeSlice m φ ht]
  ring

#print axioms integral_endpointWave_mul_nativeSlice
#print axioms integral_nativeTimeIntegrand
#print axioms integral_nativeAffine_space
end LiZouTransport.NativeSeparation
