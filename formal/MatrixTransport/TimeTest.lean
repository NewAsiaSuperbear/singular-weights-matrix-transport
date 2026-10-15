import MatrixTransport.Continuity

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

namespace MatrixTransport

noncomputable def timePotential (Phi : ClosedC1Field) (a : ℝ) (x : Spatial) (t : ℝ) : ℝ :=
  Matrix.trace (Phi.toFun (t, x)) + t * a * (Phi.toFun (t, x)) 1 1

noncomputable def timePotentialDerivative (Phi : ClosedC1Field) (a : ℝ) (x : Spatial)
    (t : ℝ) : ℝ :=
  Matrix.trace (dtPhi Phi (t, x)) + a * (Phi.toFun (t, x)) 1 1
    + t * a * (dtPhi Phi (t, x)) 1 1

theorem mem_QSet_of_Icc_disk {t : ℝ} {x : Spatial} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ disk) : ((t, x) : Ambient) ∈ QSet :=
  Set.mk_mem_prod ht hx

theorem hasDerivAt_phi_time (Phi : ClosedC1Field) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {x : Spatial} (hx : x ∈ disk) :
    HasDerivAt (fun s : ℝ => Phi.toFun (s, x)) (dtPhi Phi (t, x)) t := by
  have hd : DifferentiableAt ℝ Phi.toFun (t, x) :=
    Phi.differentiableAt_QSet (mem_QSet_of_Icc_disk ht hx)
  have hc : HasDerivAt (fun s : ℝ => ((s, x) : Ambient)) ((1 : ℝ), (0 : Spatial)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t x)
  exact hd.hasFDerivAt.comp_hasDerivAt t hc

theorem hasDerivAt_phi_entry (Phi : ClosedC1Field) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {x : Spatial} (hx : x ∈ disk) (i j : Fin 2) :
    HasDerivAt (fun s : ℝ => Phi.toFun (s, x) i j) (dtPhi Phi (t, x) i j) t := by
  have h := hasDerivAt_phi_time Phi ht hx
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp h i) j

theorem hasDerivAt_timePotential (Phi : ClosedC1Field) (a : ℝ) {x : Spatial}
    (hx : x ∈ disk) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (timePotential Phi a x) (timePotentialDerivative Phi a x t) t := by
  have e := fun i j => hasDerivAt_phi_entry Phi ht hx i j
  have h0 := (e 0 0).add (e 1 1)
  have hf : (fun s : ℝ => Matrix.trace (Phi.toFun (s, x)))
      = fun s : ℝ => Phi.toFun (s, x) 0 0 + Phi.toFun (s, x) 1 1 := by
    funext s
    first
      | exact Matrix.trace_fin_two _
      | simp [Matrix.trace, Fin.sum_univ_two]
  have hd : Matrix.trace (dtPhi Phi (t, x))
      = dtPhi Phi (t, x) 0 0 + dtPhi Phi (t, x) 1 1 := by
    first
      | exact Matrix.trace_fin_two _
      | simp [Matrix.trace, Fin.sum_univ_two]
  have h1 : HasDerivAt (fun s : ℝ => Matrix.trace (Phi.toFun (s, x)))
      (Matrix.trace (dtPhi Phi (t, x))) t := by
    rw [hf, hd]
    exact h0
  have h2 : HasDerivAt (fun s : ℝ => s * a * Phi.toFun (s, x) 1 1)
      (1 * a * Phi.toFun (t, x) 1 1 + t * a * dtPhi Phi (t, x) 1 1) t :=
    ((hasDerivAt_id' t).mul_const a).mul (e 1 1)
  have key := h1.add h2
  refine HasDerivAt.congr_deriv key ?_
  unfold timePotentialDerivative
  ring

theorem continuousOn_phi_curve (Phi : ClosedC1Field) {x : Spatial} (hx : x ∈ disk)
    (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => Phi.toFun (t, x) i j) (Set.Icc (0 : ℝ) 1) := by
  have hcurve : Continuous (fun t : ℝ => ((t, x) : Ambient)) :=
    continuous_id.prodMk continuous_const
  have h : ContinuousOn (fun t : ℝ => Phi.toFun (t, x)) (Set.Icc (0 : ℝ) 1) :=
    Phi.continuousOn_QSet.comp hcurve.continuousOn
      (fun t ht => mem_QSet_of_Icc_disk ht hx)
  exact continuousOn_pi.mp (continuousOn_pi.mp h i) j

theorem continuousOn_dtPhi_curve (Phi : ClosedC1Field) {x : Spatial} (hx : x ∈ disk)
    (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => dtPhi Phi (t, x) i j) (Set.Icc (0 : ℝ) 1) := by
  have hdt : ContinuousOn
      (fun p : Ambient => fderiv ℝ Phi.toFun p ((1 : ℝ), (0 : Spatial))) QSet :=
    Phi.continuousOn_fderiv_QSet.clm_apply continuousOn_const
  have hcurve : Continuous (fun t : ℝ => ((t, x) : Ambient)) :=
    continuous_id.prodMk continuous_const
  have h : ContinuousOn (fun t : ℝ => dtPhi Phi (t, x)) (Set.Icc (0 : ℝ) 1) :=
    hdt.comp hcurve.continuousOn (fun t ht => mem_QSet_of_Icc_disk ht hx)
  exact continuousOn_pi.mp (continuousOn_pi.mp h i) j

theorem continuousOn_timePotentialDerivative (Phi : ClosedC1Field) (a : ℝ) {x : Spatial}
    (hx : x ∈ disk) :
    ContinuousOn (fun t : ℝ => timePotentialDerivative Phi a x t) (Set.Icc (0 : ℝ) 1) := by
  have hf : (fun t : ℝ => timePotentialDerivative Phi a x t)
      = fun t : ℝ => (dtPhi Phi (t, x) 0 0 + dtPhi Phi (t, x) 1 1)
          + a * Phi.toFun (t, x) 1 1 + t * a * dtPhi Phi (t, x) 1 1 := by
    funext t
    unfold timePotentialDerivative
    rw [Matrix.trace_fin_two]
  rw [hf]
  have c00 := continuousOn_dtPhi_curve Phi hx 0 0
  have c11 := continuousOn_dtPhi_curve Phi hx 1 1
  have p11 := continuousOn_phi_curve Phi hx 1 1
  exact ((c00.add c11).add (continuousOn_const.mul p11)).add
    ((continuousOn_id.mul continuousOn_const).mul c11)

theorem intervalIntegrable_timePotentialDerivative (Phi : ClosedC1Field) (a : ℝ)
    {x : Spatial} (hx : x ∈ disk) :
    IntervalIntegrable (fun t : ℝ => timePotentialDerivative Phi a x t) volume 0 1 :=
  (continuousOn_timePotentialDerivative Phi a hx).intervalIntegrable_of_Icc zero_le_one

theorem integral_timePotentialDerivative (Phi : ClosedC1Field) (a : ℝ) {x : Spatial}
    (hx : x ∈ disk) :
    ∫ t in Set.Icc (0 : ℝ) 1, timePotentialDerivative Phi a x t
      = Matrix.trace (Phi.toFun (1, x)) - Matrix.trace (Phi.toFun (0, x))
        + a * (Phi.toFun (1, x)) 1 1 := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hFTC : ∫ t in (0 : ℝ)..1, timePotentialDerivative Phi a x t
      = timePotential Phi a x 1 - timePotential Phi a x 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_timePotential Phi a hx
        (by rw [Set.uIcc_of_le h01] at ht; exact ht))
      (intervalIntegrable_timePotentialDerivative Phi a hx)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h01,
    hFTC]
  simp only [timePotential]
  ring

theorem volume_restrict_QSet_eq_prod :
    (volume : Measure Ambient).restrict QSet
      = ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod diskVolume := by
  have hQ : QSet = Set.Icc (0 : ℝ) 1 ×ˢ disk := rfl
  rw [hQ, Measure.volume_eq_prod]
  unfold diskVolume
  rw [Measure.prod_restrict]

theorem integrable_of_continuousOn_QSet (F : Ambient → ℝ) (hF : ContinuousOn F QSet) :
    Integrable F (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod diskVolume) := by
  rw [← volume_restrict_QSet_eq_prod]
  exact hF.integrableOn_compact QSet_isCompact

theorem integral_volumeQ_eq_time_space (F : Ambient → ℝ) (hF : ContinuousOn F QSet) :
    (∫ q : Q, F (q : Ambient) ∂volumeQ)
      = ∫ t in Set.Icc (0 : ℝ) 1, ∫ x, F (t, x) ∂diskVolume := by
  rw [integral_volumeQ, volume_restrict_QSet_eq_prod]
  exact integral_prod F (integrable_of_continuousOn_QSet F hF)

theorem integral_volumeQ_eq_space_time (F : Ambient → ℝ) (hF : ContinuousOn F QSet) :
    (∫ q : Q, F (q : Ambient) ∂volumeQ)
      = ∫ x, ∫ t in Set.Icc (0 : ℝ) 1, F (t, x) ∂volume ∂diskVolume := by
  rw [integral_volumeQ, volume_restrict_QSet_eq_prod]
  exact integral_prod_symm F (integrable_of_continuousOn_QSet F hF)

#print axioms hasDerivAt_phi_time
#print axioms hasDerivAt_timePotential
#print axioms continuousOn_timePotentialDerivative
#print axioms intervalIntegrable_timePotentialDerivative
#print axioms integral_timePotentialDerivative
#print axioms integrable_of_continuousOn_QSet
#print axioms integral_volumeQ_eq_time_space
#print axioms integral_volumeQ_eq_space_time

end MatrixTransport
