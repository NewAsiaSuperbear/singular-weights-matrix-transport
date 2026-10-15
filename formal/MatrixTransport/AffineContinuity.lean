import MatrixTransport.SpatialTest
import MatrixTransport.Oscillation
import MatrixTransport.TimeTest
import MatrixTransport.AffinePath

set_option autoImplicit false

open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace MatrixTransport

theorem primitiveWave_eq_zero_of_not_mem_disk (n : ℕ) (x : Spatial) (hx : x ∉ disk) :
    primitiveWave n x = 0 := by
  by_contra h
  exact hx (chi_tsupport_subset_disk
    (tsupport_primitiveWave_subset n (subset_tsupport _ h)))

theorem endpointWave_eq_zero_of_not_mem_disk (n : ℕ) (x : Spatial) (hx : x ∉ disk) :
    endpointWave n x = 0 := by
  by_contra h
  exact hx (chi_tsupport_subset_disk
    (tsupport_endpointWave_subset n (subset_tsupport _ h)))

theorem integral_endpointWave_mul_fieldSlice (n : ℕ) (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, endpointWave n x * fieldSlice Phi t x ∂diskVolume)
      = -(∫ x, primitiveWave n x * fieldSliceD Phi t x ∂diskVolume) := by
  have hdv : diskVolume = volume.restrict disk := by
    first
      | rfl
      | simp [diskVolume]
  have hpt : ∀ x : Spatial,
      primitiveWave n x * fderiv ℝ (fieldSlice Phi t) x e1
        = primitiveWave n x * fieldSliceD Phi t x := by
    intro x
    by_cases hx : x ∈ disk
    · rw [fderiv_fieldSlice_e1 Phi ht hx]
    · rw [primitiveWave_eq_zero_of_not_mem_disk n x hx]
      simp
  have hg : ∀ x ∈ tsupport chi, DifferentiableAt ℝ (fieldSlice Phi t) x :=
    fun x hx => differentiableAt_fieldSlice Phi ht (chi_tsupport_subset_disk hx)
  have h1 : Integrable (fun x => primitiveWave n x * fieldSlice Phi t x) volume :=
    integrable_mul_fieldSlice Phi ht (primitiveWave n) (primitiveWave_continuous n)
      (primitiveWave_compact n)
      ((tsupport_primitiveWave_subset n).trans chi_tsupport_subset)
  have h2 : Integrable (fun x => endpointWave n x * fieldSlice Phi t x) volume :=
    integrable_mul_fieldSlice Phi ht (endpointWave n) (endpointWave_continuous n)
      (endpointWave_compact n)
      ((tsupport_endpointWave_subset n).trans chi_tsupport_subset)
  have h3' : Integrable (fun x => primitiveWave n x * fieldSliceD Phi t x) volume :=
    integrable_mul_fieldSliceD Phi ht (primitiveWave n) (primitiveWave_continuous n)
      (primitiveWave_compact n)
      ((tsupport_primitiveWave_subset n).trans chi_tsupport_subset)
  have hfun : (fun x => primitiveWave n x * fderiv ℝ (fieldSlice Phi t) x e1)
      = fun x => primitiveWave n x * fieldSliceD Phi t x := funext hpt
  have h3 : Integrable
      (fun x => primitiveWave n x * fderiv ℝ (fieldSlice Phi t) x e1) volume := by
    rw [hfun]
    exact h3'
  have key := integral_endpointWave_mul_eq n (fieldSlice Phi t) h1 h2 h3 hg
  have e : (∫ x, primitiveWave n x * fderiv ℝ (fieldSlice Phi t) x e1)
      = ∫ x, primitiveWave n x * fieldSliceD Phi t x :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hE : (∫ x in disk, endpointWave n x * fieldSlice Phi t x)
      = ∫ x, endpointWave n x * fieldSlice Phi t x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [endpointWave_eq_zero_of_not_mem_disk n x hx]
      simp)
  have hP : (∫ x in disk, primitiveWave n x * fieldSliceD Phi t x)
      = ∫ x, primitiveWave n x * fieldSliceD Phi t x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [primitiveWave_eq_zero_of_not_mem_disk n x hx]
      simp)
  rw [hdv, hE, hP, key, e]

noncomputable def affinePairIntegrand (n : ℕ) (eps : ℝ) (Phi : ClosedC1Field)
    (p : Ambient) : ℝ :=
  Matrix.trace (dtPhi Phi p) + p.1 * eps * endpointWave n p.2 * (dtPhi Phi p) 1 1
    - eps * primitiveWave n p.2 * (dxPhi Phi 0 p) 1 1

theorem affinePairIntegrand_eq_weightedPair (n : ℕ) (eps : ℝ) (Phi : ClosedC1Field)
    (q : Q) :
    weightedPair (fun _ => 1) (testTriplet fullDstar Phi q)
      (packTriplet (density ((q : Ambient).1 * eps * endpointWave n (q : Ambient).2))
        (singleFlux (1 : Fin 8) (-eps * primitiveWave n (q : Ambient).2)) (0 : Mat2))
      = affinePairIntegrand n eps Phi (q : Ambient) := by
  unfold testTriplet fullDstar
  simp only [weightedPair_packTriplet, mass_packTriplet, flux_packTriplet,
    reaction_packTriplet, frob_density_diag, frob_singleFlux, fullStar_column_one]
  have hz : frob (0 : Mat2) (Phi.toFun (q : Ambient)) = 0 := by simp [frob]
  simp only [hz]
  simp only [dtPhiQ, dxPhiQ, Matrix.trace_fin_two, affinePairIntegrand]
  ring

theorem continuousOn_matEntry {α : Type*} [TopologicalSpace α] {F : α → Mat2}
    {S : Set α} (h : ContinuousOn F S) (i j : Fin 2) :
    ContinuousOn (fun p => F p i j) S :=
  continuousOn_pi.mp (continuousOn_pi.mp h i) j

theorem continuousOn_dtPhi_QSet (Phi : ClosedC1Field) :
    ContinuousOn (dtPhi Phi) QSet := by
  have h := Phi.continuousOn_fderiv_QSet.clm_apply
    (continuousOn_const (c := ((1 : ℝ), (0 : Spatial))))
  exact h

theorem continuousOn_dxPhi_QSet (Phi : ClosedC1Field) (j : Fin 2) :
    ContinuousOn (dxPhi Phi j) QSet := by
  have h := Phi.continuousOn_fderiv_QSet.clm_apply
    (continuousOn_const (c := ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))))
  exact h

theorem affinePairIntegrand_continuousOn (n : ℕ) (eps : ℝ) (Phi : ClosedC1Field) :
    ContinuousOn (affinePairIntegrand n eps Phi) QSet := by
  have hf : affinePairIntegrand n eps Phi
      = fun p : Ambient =>
        (dtPhi Phi p 0 0 + dtPhi Phi p 1 1)
          + p.1 * eps * endpointWave n p.2 * dtPhi Phi p 1 1
          - eps * primitiveWave n p.2 * dxPhi Phi 0 p 1 1 := by
    funext p
    simp only [affinePairIntegrand, Matrix.trace_fin_two]
  rw [hf]
  have c00 := continuousOn_matEntry (continuousOn_dtPhi_QSet Phi) 0 0
  have c11 := continuousOn_matEntry (continuousOn_dtPhi_QSet Phi) 1 1
  have d11 := continuousOn_matEntry (continuousOn_dxPhi_QSet Phi 0) 1 1
  have hE : ContinuousOn (fun p : Ambient => endpointWave n p.2) QSet :=
    ((endpointWave_continuous n).comp continuous_snd).continuousOn
  have hP : ContinuousOn (fun p : Ambient => primitiveWave n p.2) QSet :=
    ((primitiveWave_continuous n).comp continuous_snd).continuousOn
  have h1 : ContinuousOn (fun p : Ambient => p.1) QSet := continuous_fst.continuousOn
  exact ((c00.add c11).add (((h1.mul continuousOn_const).mul hE).mul c11)).sub
    ((continuousOn_const.mul hP).mul d11)

noncomputable def affineTimeIntegrand (n : ℕ) (eps : ℝ) (Phi : ClosedC1Field)
    (p : Ambient) : ℝ :=
  timePotentialDerivative Phi (eps * endpointWave n p.2) p.2 p.1

theorem affineTimeIntegrand_continuousOn (n : ℕ) (eps : ℝ) (Phi : ClosedC1Field) :
    ContinuousOn (affineTimeIntegrand n eps Phi) QSet := by
  have hf : affineTimeIntegrand n eps Phi
      = fun p : Ambient =>
        (dtPhi Phi p 0 0 + dtPhi Phi p 1 1)
          + (eps * endpointWave n p.2) * Phi.toFun p 1 1
          + p.1 * (eps * endpointWave n p.2) * dtPhi Phi p 1 1 := by
    funext p
    obtain ⟨t, x⟩ := p
    simp only [affineTimeIntegrand, timePotentialDerivative, Matrix.trace_fin_two]
      <;> ring
  rw [hf]
  have c00 := continuousOn_matEntry (continuousOn_dtPhi_QSet Phi) 0 0
  have c11 := continuousOn_matEntry (continuousOn_dtPhi_QSet Phi) 1 1
  have p11 := continuousOn_matEntry Phi.continuousOn_QSet 1 1
  have hE : ContinuousOn (fun p : Ambient => endpointWave n p.2) QSet :=
    ((endpointWave_continuous n).comp continuous_snd).continuousOn
  have h1 : ContinuousOn (fun p : Ambient => p.1) QSet := continuous_fst.continuousOn
  exact ((c00.add c11).add ((continuousOn_const.mul hE).mul p11)).add
    ((h1.mul (continuousOn_const.mul hE)).mul c11)

theorem integral_affinePairIntegrand_space_eq (n : ℕ) (eps : ℝ) (Phi : ClosedC1Field)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, affinePairIntegrand n eps Phi (t, x) ∂diskVolume)
      = ∫ x, affineTimeIntegrand n eps Phi (t, x) ∂diskVolume := by
  have hm : Set.MapsTo (fun x : Spatial => ((t, x) : Ambient)) disk QSet :=
    fun x hx => mem_QSet_of_Icc_disk ht hx
  have hemb : ContinuousOn (fun x : Spatial => ((t, x) : Ambient)) disk :=
    (continuous_const.prodMk continuous_id).continuousOn
  have cdt : ∀ i j : Fin 2, ContinuousOn (fun x : Spatial => dtPhi Phi (t, x) i j) disk :=
    fun i j => continuousOn_matEntry (F := fun x : Spatial => dtPhi Phi (t, x))
      ((continuousOn_dtPhi_QSet Phi).comp hemb hm) i j
  have cdx : ContinuousOn (fun x : Spatial => dxPhi Phi 0 (t, x) 1 1) disk :=
    continuousOn_matEntry (F := fun x : Spatial => dxPhi Phi 0 (t, x))
      ((continuousOn_dxPhi_QSet Phi 0).comp hemb hm) 1 1
  have cPh : ContinuousOn (fun x : Spatial => Phi.toFun (t, x) 1 1) disk :=
    continuousOn_matEntry (F := fun x : Spatial => Phi.toFun (t, x))
      (Phi.continuousOn_QSet.comp hemb hm) 1 1
  have hEd : ContinuousOn (fun x : Spatial => endpointWave n x) disk :=
    (endpointWave_continuous n).continuousOn
  have hPd : ContinuousOn (fun x : Spatial => primitiveWave n x) disk :=
    (primitiveWave_continuous n).continuousOn
  have hF : ∀ x, fieldSlice Phi t x = Phi.toFun (t, x) 1 1 := by
    intro x
    first
      | rfl
      | simp [fieldSlice]
  have hD : ∀ x, fieldSliceD Phi t x = dxPhi Phi 0 (t, x) 1 1 := by
    intro x
    first
      | rfl
      | simp [fieldSliceD, dxPhi]
  obtain ⟨U, hU⟩ : ∃ U : Spatial → ℝ, ∀ x, U x
      = (dtPhi Phi (t, x) 0 0 + dtPhi Phi (t, x) 1 1)
        + t * eps * endpointWave n x * dtPhi Phi (t, x) 1 1 :=
    ⟨fun x => (dtPhi Phi (t, x) 0 0 + dtPhi Phi (t, x) 1 1)
        + t * eps * endpointWave n x * dtPhi Phi (t, x) 1 1, fun x => rfl⟩
  have hUc : ContinuousOn U disk := by
    have : U = fun x => (dtPhi Phi (t, x) 0 0 + dtPhi Phi (t, x) 1 1)
        + t * eps * endpointWave n x * dtPhi Phi (t, x) 1 1 := funext hU
    rw [this]
    exact ((cdt 0 0).add (cdt 1 1)).add
      (((continuousOn_const (c := t * eps)).mul hEd).mul (cdt 1 1))
  have hUi : Integrable U diskVolume := hUc.integrableOn_compact disk_isCompact
  have hHc : ContinuousOn (fun x : Spatial => primitiveWave n x * fieldSliceD Phi t x) disk := by
    have : (fun x : Spatial => primitiveWave n x * fieldSliceD Phi t x)
        = fun x => primitiveWave n x * dxPhi Phi 0 (t, x) 1 1 :=
      funext fun x => by rw [hD x]
    rw [this]
    exact hPd.mul cdx
  have hFc : ContinuousOn (fun x : Spatial => endpointWave n x * fieldSlice Phi t x) disk := by
    have : (fun x : Spatial => endpointWave n x * fieldSlice Phi t x)
        = fun x => endpointWave n x * Phi.toFun (t, x) 1 1 :=
      funext fun x => by rw [hF x]
    rw [this]
    exact hEd.mul cPh
  have hHi : Integrable (fun x : Spatial => primitiveWave n x * fieldSliceD Phi t x)
      diskVolume := hHc.integrableOn_compact disk_isCompact
  have hFi : Integrable (fun x : Spatial => endpointWave n x * fieldSlice Phi t x)
      diskVolume := hFc.integrableOn_compact disk_isCompact
  have iH : Integrable (fun x : Spatial => eps * (primitiveWave n x * fieldSliceD Phi t x))
      diskVolume := hHi.const_mul eps
  have iF : Integrable (fun x : Spatial => eps * (endpointWave n x * fieldSlice Phi t x))
      diskVolume := hFi.const_mul eps
  have hL : ∀ x, affinePairIntegrand n eps Phi (t, x)
      = U x - eps * (primitiveWave n x * fieldSliceD Phi t x) := by
    intro x
    rw [hU x, hD x]
    simp only [affinePairIntegrand, Matrix.trace_fin_two]
    ring
  have hR : ∀ x, affineTimeIntegrand n eps Phi (t, x)
      = U x + eps * (endpointWave n x * fieldSlice Phi t x) := by
    intro x
    rw [hU x, hF x]
    simp only [affineTimeIntegrand, timePotentialDerivative, Matrix.trace_fin_two]
    ring
  have eL : (∫ x, affinePairIntegrand n eps Phi (t, x) ∂diskVolume)
      = ∫ x, (U x - eps * (primitiveWave n x * fieldSliceD Phi t x)) ∂diskVolume :=
    integral_congr_ae (Filter.Eventually.of_forall hL)
  have eR : (∫ x, affineTimeIntegrand n eps Phi (t, x) ∂diskVolume)
      = ∫ x, (U x + eps * (endpointWave n x * fieldSlice Phi t x)) ∂diskVolume :=
    integral_congr_ae (Filter.Eventually.of_forall hR)
  have key := integral_endpointWave_mul_fieldSlice n Phi ht
  rw [eL, eR, integral_sub hUi iH, integral_add hUi iF, integral_const_mul,
    integral_const_mul, key]
  ring

theorem frob_density0_eq_diag (M : Mat2) :
    frob (density 0) M = M 0 0 + M 1 1 := by
  simpa using frob_density_diag (0 : ℝ) M

theorem frob_density_slice_eq (a : ℝ) (M : Mat2) :
    frob (density a) M = M 0 0 + (1 + a) * M 1 1 := by
  first
    | (rw [frob_density_diag]; done)
    | (rw [frob_density_diag]; ring)
    | (simp only [frob_density_diag]; ring)

theorem integrable_frob_density_slice (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (a : Spatial → ℝ) (ha : Continuous a) :
    Integrable (fun x : Spatial => frob (density (a x)) (Phi.toFun (t, x))) diskVolume := by
  have hm : Set.MapsTo (fun x : Spatial => ((t, x) : Ambient)) disk QSet :=
    fun x hx => mem_QSet_of_Icc_disk ht hx
  have hemb : ContinuousOn (fun x : Spatial => ((t, x) : Ambient)) disk :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hP : ContinuousOn (fun x : Spatial => Phi.toFun (t, x)) disk :=
    Phi.continuousOn_QSet.comp hemb hm
  have c00 := continuousOn_matEntry hP 0 0
  have c11 := continuousOn_matEntry hP 1 1
  have hc : ContinuousOn
      (fun x : Spatial => Phi.toFun (t, x) 0 0 + (1 + a x) * Phi.toFun (t, x) 1 1) disk :=
    c00.add ((continuousOn_const.add ha.continuousOn).mul c11)
  have hEq : (fun x : Spatial => frob (density (a x)) (Phi.toFun (t, x)))
      = fun x : Spatial => Phi.toFun (t, x) 0 0 + (1 + a x) * Phi.toFun (t, x) 1 1 :=
    funext fun x => frob_density_slice_eq (a x) _
  rw [hEq]
  exact hc.integrableOn_compact disk_isCompact

theorem integrable_frob_density0_slice (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun x : Spatial => frob (density 0) (Phi.toFun (t, x))) diskVolume := by
  have hm : Set.MapsTo (fun x : Spatial => ((t, x) : Ambient)) disk QSet :=
    fun x hx => mem_QSet_of_Icc_disk ht hx
  have hemb : ContinuousOn (fun x : Spatial => ((t, x) : Ambient)) disk :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hP : ContinuousOn (fun x : Spatial => Phi.toFun (t, x)) disk :=
    Phi.continuousOn_QSet.comp hemb hm
  have c00 := continuousOn_matEntry hP 0 0
  have c11 := continuousOn_matEntry hP 1 1
  have hEq : (fun x : Spatial => frob (density 0) (Phi.toFun (t, x)))
      = fun x : Spatial => Phi.toFun (t, x) 0 0 + Phi.toFun (t, x) 1 1 :=
    funext fun x => frob_density0_eq_diag _
  rw [hEq]
  exact (c00.add c11).integrableOn_compact disk_isCompact

theorem integral_affinePairIntegrand_eq_endpointDifference (n : ℕ) (eps : ℝ)
    (Phi : ClosedC1Field) :
    (∫ q : Q, affinePairIntegrand n eps Phi (q : Ambient) ∂volumeQ)
      = endpointDifference (fun _ => (density 0))
          (fun x => density (eps * endpointWave n x)) Phi := by
  have hAB : (∫ q : Q, affinePairIntegrand n eps Phi (q : Ambient) ∂volumeQ)
      = ∫ q : Q, affineTimeIntegrand n eps Phi (q : Ambient) ∂volumeQ := by
    rw [integral_volumeQ_eq_time_space _ (affinePairIntegrand_continuousOn n eps Phi),
      integral_volumeQ_eq_time_space _ (affineTimeIntegrand_continuousOn n eps Phi)]
    exact setIntegral_congr_fun measurableSet_Icc
      (fun t ht => integral_affinePairIntegrand_space_eq n eps Phi ht)
  rw [hAB, integral_volumeQ_eq_space_time _ (affineTimeIntegrand_continuousOn n eps Phi)]
  have hdisk : ∀ᵐ x ∂diskVolume, x ∈ disk := ae_restrict_mem disk_measurableSet
  have hpt : ∀ᵐ x ∂diskVolume,
      (∫ t in Set.Icc (0 : ℝ) 1, affineTimeIntegrand n eps Phi (t, x))
        = frob (density (eps * endpointWave n x)) (Phi.toFun (1, x))
          - frob (density 0) (Phi.toFun (0, x)) := by
    filter_upwards [hdisk] with x hx
    have h := integral_timePotentialDerivative Phi (eps * endpointWave n x) hx
    calc (∫ t in Set.Icc (0 : ℝ) 1, affineTimeIntegrand n eps Phi (t, x))
        = ∫ t in Set.Icc (0 : ℝ) 1,
            timePotentialDerivative Phi (eps * endpointWave n x) x t := rfl
      _ = Matrix.trace (Phi.toFun (1, x)) - Matrix.trace (Phi.toFun (0, x))
            + (eps * endpointWave n x) * (Phi.toFun (1, x)) 1 1 := h
      _ = _ := by
        rw [frob_density_slice_eq, frob_density0_eq_diag, Matrix.trace_fin_two,
          Matrix.trace_fin_two]
        ring
  have i1 : Integrable
      (fun x : Spatial => frob (density (eps * endpointWave n x)) (Phi.toFun (1, x)))
      diskVolume :=
    integrable_frob_density_slice Phi (Set.right_mem_Icc.mpr zero_le_one)
      (fun x => eps * endpointWave n x) (continuous_const.mul (endpointWave_continuous n))
  have i0 : Integrable (fun x : Spatial => frob (density 0) (Phi.toFun (0, x))) diskVolume :=
    integrable_frob_density0_slice Phi (Set.left_mem_Icc.mpr zero_le_one)
  calc (∫ x, ∫ t in Set.Icc (0 : ℝ) 1, affineTimeIntegrand n eps Phi (t, x) ∂volume
          ∂diskVolume)
      = ∫ x, (frob (density (eps * endpointWave n x)) (Phi.toFun (1, x))
          - frob (density 0) (Phi.toFun (0, x))) ∂diskVolume := integral_congr_ae hpt
    _ = (∫ x, frob (density (eps * endpointWave n x)) (Phi.toFun (1, x)) ∂diskVolume)
          - ∫ x, frob (density 0) (Phi.toFun (0, x)) ∂diskVolume := integral_sub i1 i0
    _ = endpointDifference (fun _ => (density 0))
          (fun x => density (eps * endpointWave n x)) Phi := by
        first
          | rfl
          | (unfold endpointDifference; rfl)
          | simp [endpointDifference]

theorem affinePath_continuityEquation (n : ℕ) (eps : ℝ) :
    ContinuityEquation fullDstar (fun _ => (density 0))
      (fun x => density (eps * endpointWave n x)) (affinePath n eps) := by
  refine (continuityEquation_iff_integral_of_density fullDstar (fun _ => (density 0))
    (fun x => density (eps * endpointWave n x)) (affinePath n eps)
    (fun c q => affineTriplet n eps q c) (measurable_affineTriplet_coord n eps)
    (integrable_affineTriplet_coord n eps) (fun c => rfl)
    (fun Phi => continuous_fullStar Phi)).mpr ?_
  intro Phi
  rw [← integral_affinePairIntegrand_eq_endpointDifference n eps Phi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simpa only [affineTriplet] using affinePairIntegrand_eq_weightedPair n eps Phi q

#print axioms integral_affinePairIntegrand_eq_endpointDifference
#print axioms affinePath_continuityEquation

#print axioms continuousOn_dtPhi_QSet
#print axioms continuousOn_dxPhi_QSet
#print axioms affinePairIntegrand_continuousOn
#print axioms affineTimeIntegrand_continuousOn
#print axioms integral_affinePairIntegrand_space_eq

#print axioms primitiveWave_eq_zero_of_not_mem_disk
#print axioms endpointWave_eq_zero_of_not_mem_disk
#print axioms integral_endpointWave_mul_fieldSlice
#print axioms affinePairIntegrand_eq_weightedPair

end MatrixTransport
