import MatrixTransport.ClosedDomain

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

namespace MatrixTransport

noncomputable def fieldSlice (Phi : ClosedC1Field) (t : ℝ) (x : Spatial) : ℝ :=
  Phi.toFun (t, x) 1 1

noncomputable def fieldSliceD (Phi : ClosedC1Field) (t : ℝ) (x : Spatial) : ℝ :=
  dxPhi Phi 0 (t, x) 1 1

theorem mk_mem_QSet {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {x : Spatial} (hx : x ∈ disk) :
    (t, x) ∈ QSet :=
  Set.mk_mem_prod ht hx

theorem mapsTo_emb_QSet {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Set.MapsTo (fun y : Spatial ↦ (t, y)) disk QSet :=
  fun _ hx ↦ mk_mem_QSet ht hx

theorem continuous_entry11 : Continuous (fun M : Mat2 ↦ M 1 1) := by
  exact (continuous_apply 1).comp (continuous_apply 1)

theorem continuousOn_fieldSlice (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ContinuousOn (fieldSlice Phi t) disk := by
  have hemb : ContinuousOn (fun y : Spatial ↦ (t, y)) disk :=
    (Continuous.prodMk continuous_const continuous_id).continuousOn
  have h1 : ContinuousOn (Phi.toFun ∘ fun y : Spatial ↦ (t, y)) disk :=
    Phi.continuousOn_QSet.comp hemb (mapsTo_emb_QSet ht)
  have h2 := continuous_entry11.continuousOn.comp h1 (Set.mapsTo_univ _ _)
  exact h2

theorem continuousOn_fieldSliceD (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ContinuousOn (fieldSliceD Phi t) disk := by
  have hemb : ContinuousOn (fun y : Spatial ↦ (t, y)) disk :=
    (Continuous.prodMk continuous_const continuous_id).continuousOn
  have h0 := Phi.continuousOn_fderiv_QSet.clm_apply
    (continuousOn_const (c := ((0 : ℝ), EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))
  have h0' : ContinuousOn (fun p : Ambient ↦ dxPhi Phi 0 p) QSet := h0
  have h1 : ContinuousOn ((fun p : Ambient ↦ dxPhi Phi 0 p) ∘ fun y : Spatial ↦ (t, y)) disk :=
    h0'.comp hemb (mapsTo_emb_QSet ht)
  have h2 := continuous_entry11.continuousOn.comp h1 (Set.mapsTo_univ _ _)
  exact h2

theorem fderiv_entry11 (Phi : ClosedC1Field) {p : Ambient}
    (hd : DifferentiableAt ℝ Phi.toFun p) (v : Ambient) :
    fderiv ℝ (fun y ↦ Phi.toFun y 1 1) p v = fderiv ℝ Phi.toFun p v 1 1 := by
  have h2 : DifferentiableAt ℝ (fun x ↦ Phi.toFun x 1) p := differentiableAt_pi.1 hd 1
  have f1 : fderiv ℝ (fun x ↦ Phi.toFun x 1 1) p =
      (ContinuousLinearMap.proj 1).comp (fderiv ℝ (fun x ↦ Phi.toFun x 1) p) :=
    fderiv_apply h2 1
  have f2 : fderiv ℝ (fun x ↦ Phi.toFun x 1) p =
      (ContinuousLinearMap.proj 1).comp (fderiv ℝ Phi.toFun p) :=
    fderiv_apply hd 1
  rw [f1, f2]
  rfl

theorem hasFDerivAt_fieldSlice (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {x : Spatial} (hx : x ∈ disk) :
    HasFDerivAt (fieldSlice Phi t)
      ((fderiv ℝ (fun p : Ambient ↦ Phi.toFun p 1 1) (t, x)).comp
        ((0 : Spatial →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Spatial))) x := by
  have hd : DifferentiableAt ℝ Phi.toFun (t, x) :=
    Phi.differentiableAt_QSet (mk_mem_QSet ht hx)
  have h2 : DifferentiableAt ℝ (fun p : Ambient ↦ Phi.toFun p 1) (t, x) :=
    differentiableAt_pi.1 hd 1
  have hg : DifferentiableAt ℝ (fun p : Ambient ↦ Phi.toFun p 1 1) (t, x) :=
    differentiableAt_pi.1 h2 1
  have hemb : HasFDerivAt (fun y : Spatial ↦ (t, y))
      ((0 : Spatial →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Spatial)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  exact hg.hasFDerivAt.comp x hemb

theorem differentiableAt_fieldSlice (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {x : Spatial} (hx : x ∈ disk) :
    DifferentiableAt ℝ (fieldSlice Phi t) x :=
  (hasFDerivAt_fieldSlice Phi ht hx).differentiableAt

theorem fderiv_fieldSlice_e1 (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {x : Spatial} (hx : x ∈ disk) :
    fderiv ℝ (fieldSlice Phi t) x e1 = fieldSliceD Phi t x := by
  have hd : DifferentiableAt ℝ Phi.toFun (t, x) :=
    Phi.differentiableAt_QSet (mk_mem_QSet ht hx)
  rw [(hasFDerivAt_fieldSlice Phi ht hx).fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply,
    ContinuousLinearMap.id_apply]
  exact fderiv_entry11 Phi hd (0, e1)

theorem ball_half_subset_disk : Metric.ball (0 : Spatial) (1 / 2 : ℝ) ⊆ disk :=
  Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by norm_num))

theorem continuous_mul_of_continuousOn_disk (h g : Spatial → ℝ) (hc : Continuous h)
    (hts : tsupport h ⊆ Metric.ball (0 : Spatial) (1 / 2 : ℝ))
    (hg : ContinuousOn g disk) : Continuous (fun x ↦ h x * g x) := by
  apply continuous_of_tsupport
  intro x hx
  have hxb : x ∈ Metric.ball (0 : Spatial) (1 / 2 : ℝ) := hts (tsupport_mul_subset_left hx)
  have hn : disk ∈ nhds x :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxb) ball_half_subset_disk
  exact hc.continuousAt.mul (hg.continuousAt hn)

theorem hasCompactSupport_mul_of_compact (h g : Spatial → ℝ) (hcs : HasCompactSupport h) :
    HasCompactSupport (fun x ↦ h x * g x) :=
  hcs.mul_right

theorem integrable_mul_of_continuousOn_disk (h g : Spatial → ℝ) (hc : Continuous h)
    (hcs : HasCompactSupport h)
    (hts : tsupport h ⊆ Metric.ball (0 : Spatial) (1 / 2 : ℝ))
    (hg : ContinuousOn g disk) : Integrable (fun x ↦ h x * g x) volume :=
  (continuous_mul_of_continuousOn_disk h g hc hts hg).integrable_of_hasCompactSupport
    (hasCompactSupport_mul_of_compact h g hcs)

theorem continuous_mul_fieldSlice (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (h : Spatial → ℝ) (hc : Continuous h)
    (hts : tsupport h ⊆ Metric.ball (0 : Spatial) (1 / 2 : ℝ)) :
    Continuous (fun x ↦ h x * fieldSlice Phi t x) :=
  continuous_mul_of_continuousOn_disk h _ hc hts (continuousOn_fieldSlice Phi ht)

theorem hasCompactSupport_mul_fieldSlice (Phi : ClosedC1Field) (t : ℝ)
    (h : Spatial → ℝ) (hcs : HasCompactSupport h) :
    HasCompactSupport (fun x ↦ h x * fieldSlice Phi t x) :=
  hasCompactSupport_mul_of_compact h _ hcs

theorem integrable_mul_fieldSlice (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (h : Spatial → ℝ) (hc : Continuous h)
    (hcs : HasCompactSupport h)
    (hts : tsupport h ⊆ Metric.ball (0 : Spatial) (1 / 2 : ℝ)) :
    Integrable (fun x ↦ h x * fieldSlice Phi t x) volume :=
  integrable_mul_of_continuousOn_disk h _ hc hcs hts (continuousOn_fieldSlice Phi ht)

theorem continuous_mul_fieldSliceD (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (h : Spatial → ℝ) (hc : Continuous h)
    (hts : tsupport h ⊆ Metric.ball (0 : Spatial) (1 / 2 : ℝ)) :
    Continuous (fun x ↦ h x * fieldSliceD Phi t x) :=
  continuous_mul_of_continuousOn_disk h _ hc hts (continuousOn_fieldSliceD Phi ht)

theorem hasCompactSupport_mul_fieldSliceD (Phi : ClosedC1Field) (t : ℝ)
    (h : Spatial → ℝ) (hcs : HasCompactSupport h) :
    HasCompactSupport (fun x ↦ h x * fieldSliceD Phi t x) :=
  hasCompactSupport_mul_of_compact h _ hcs

theorem integrable_mul_fieldSliceD (Phi : ClosedC1Field) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (h : Spatial → ℝ) (hc : Continuous h)
    (hcs : HasCompactSupport h)
    (hts : tsupport h ⊆ Metric.ball (0 : Spatial) (1 / 2 : ℝ)) :
    Integrable (fun x ↦ h x * fieldSliceD Phi t x) volume :=
  integrable_mul_of_continuousOn_disk h _ hc hcs hts (continuousOn_fieldSliceD Phi ht)

end MatrixTransport
