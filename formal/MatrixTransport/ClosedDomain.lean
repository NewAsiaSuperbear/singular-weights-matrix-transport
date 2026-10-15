import Mathlib
import MatrixTransport.Bump
import MatrixTransport.MatrixBasics

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

namespace MatrixTransport

abbrev Ambient := ℝ × Spatial

def QSet : Set Ambient := Set.Icc (0 : ℝ) 1 ×ˢ disk

abbrev Q := ↥QSet

noncomputable instance : MeasureSpace Q := Measure.Subtype.measureSpace

noncomputable def volumeQ : Measure Q := volume

noncomputable def diskVolume : Measure Spatial := volume.restrict disk

theorem disk_isCompact : IsCompact disk := by
  unfold disk
  exact isCompact_closedBall _ _

theorem disk_measurableSet : MeasurableSet disk := by
  unfold disk
  exact Metric.isClosed_closedBall.measurableSet

theorem QSet_isCompact : IsCompact QSet :=
  isCompact_Icc.prod disk_isCompact

theorem QSet_measurableSet : MeasurableSet QSet :=
  measurableSet_Icc.prod disk_measurableSet

instance Q_compactSpace : CompactSpace Q :=
  isCompact_iff_compactSpace.mp QSet_isCompact

theorem disk_volume_eq_pi : (volume : Measure Spatial) disk = ENNReal.ofReal Real.pi := by
  unfold disk
  rw [EuclideanSpace.volume_closedBall_fin_two]
  simp

theorem diskVolume_univ_eq_pi : diskVolume Set.univ = ENNReal.ofReal Real.pi := by
  unfold diskVolume
  rw [Measure.restrict_apply_univ]
  exact disk_volume_eq_pi

theorem diskVolume_real_univ_eq_pi : diskVolume.real Set.univ = Real.pi := by
  show (diskVolume Set.univ).toReal = Real.pi
  rw [diskVolume_univ_eq_pi, ENNReal.toReal_ofReal Real.pi_pos.le]

theorem diskVolume_univ_pos : 0 < diskVolume Set.univ := by
  rw [diskVolume_univ_eq_pi]
  exact ENNReal.ofReal_pos.mpr Real.pi_pos

theorem QSet_volume_eq_pi : (volume : Measure Ambient) QSet = ENNReal.ofReal Real.pi := by
  unfold QSet
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, disk_volume_eq_pi]
  simp

theorem volumeQ_univ_eq_pi : volumeQ Set.univ = ENNReal.ofReal Real.pi := by
  unfold volumeQ
  rw [Measure.Subtype.volume_univ QSet_measurableSet.nullMeasurableSet]
  exact QSet_volume_eq_pi

theorem volumeQ_univ_pos : 0 < volumeQ Set.univ := by
  rw [volumeQ_univ_eq_pi]
  exact ENNReal.ofReal_pos.mpr Real.pi_pos

instance volumeQ_isFiniteMeasure : IsFiniteMeasure volumeQ :=
  ⟨by rw [volumeQ_univ_eq_pi]; exact ENNReal.ofReal_lt_top⟩

instance volume_Q_isFiniteMeasure : IsFiniteMeasure (volume : Measure Q) :=
  volumeQ_isFiniteMeasure

instance diskVolume_isFiniteMeasure : IsFiniteMeasure diskVolume :=
  ⟨by rw [diskVolume_univ_eq_pi]; exact ENNReal.ofReal_lt_top⟩

theorem integral_volumeQ (F : Ambient → ℝ) :
    (∫ q : Q, F (q : Ambient) ∂volumeQ) = ∫ p in QSet, F p ∂volume := by
  unfold volumeQ
  rw [Measure.Subtype.volume_def]
  exact integral_subtype_comap QSet_measurableSet F

theorem lintegral_volumeQ (F : Ambient → ℝ≥0∞) :
    (∫⁻ q : Q, F (q : Ambient) ∂volumeQ) = ∫⁻ p in QSet, F p ∂volume := by
  unfold volumeQ
  rw [Measure.Subtype.volume_def]
  exact lintegral_subtype_comap QSet_measurableSet F

#print axioms QSet_volume_eq_pi
#print axioms integral_volumeQ
#print axioms lintegral_volumeQ

end MatrixTransport

namespace MatrixTransport

structure ClosedC1Field where
  toFun : Ambient → Mat2
  globallyHermitian : ∀ p, (toFun p).IsHermitian
  c1_neighborhood : ∃ U : Set Ambient,
    IsOpen U ∧ QSet ⊆ U ∧ ContDiffOn ℝ 1 toFun U

instance : CoeFun ClosedC1Field (fun _ ↦ Ambient → Mat2) := ⟨ClosedC1Field.toFun⟩

noncomputable def dtPhi (Phi : ClosedC1Field) (p : Ambient) : Mat2 :=
  fderiv ℝ Phi.toFun p (1, (0 : Spatial))
noncomputable def dxPhi (Phi : ClosedC1Field) (j : Fin 2) (p : Ambient) : Mat2 :=
  fderiv ℝ Phi.toFun p (0, EuclideanSpace.single j (1 : ℝ))
noncomputable def dtPhiQ (Phi : ClosedC1Field) : Q → Mat2 := fun q ↦ dtPhi Phi (q : Ambient)
noncomputable def dxPhiQ (Phi : ClosedC1Field) (j : Fin 2) : Q → Mat2 :=
  fun q ↦ dxPhi Phi j (q : Ambient)

theorem ClosedC1Field.continuousOn_QSet (Phi : ClosedC1Field) :
    ContinuousOn Phi.toFun QSet := by
  obtain ⟨U, _, hQU, hC⟩ := Phi.c1_neighborhood
  exact hC.continuousOn.mono hQU

theorem ClosedC1Field.continuous_Q (Phi : ClosedC1Field) :
    Continuous (fun q : Q ↦ Phi.toFun (q : Ambient)) :=
  continuousOn_iff_continuous_domRestrict.mp Phi.continuousOn_QSet

theorem ClosedC1Field.differentiableAt_QSet (Phi : ClosedC1Field) {p : Ambient}
    (hp : p ∈ QSet) : DifferentiableAt ℝ Phi.toFun p := by
  obtain ⟨U, hU, hQU, hC⟩ := Phi.c1_neighborhood
  exact (hC.differentiableOn (by norm_num) p (hQU hp)).differentiableAt
    (hU.mem_nhds (hQU hp))

theorem ClosedC1Field.continuousOn_fderiv_QSet (Phi : ClosedC1Field) :
    ContinuousOn (fderiv ℝ Phi.toFun) QSet := by
  obtain ⟨U, hU, hQU, hC⟩ := Phi.c1_neighborhood
  exact (hC.continuousOn_fderiv_of_isOpen hU le_rfl).mono hQU

theorem continuous_dtPhiQ (Phi : ClosedC1Field) : Continuous (dtPhiQ Phi) := by
  have h := Phi.continuousOn_fderiv_QSet.clm_apply
    (continuousOn_const (c := ((1 : ℝ), (0 : Spatial))))
  exact continuousOn_iff_continuous_domRestrict.mp h

theorem continuous_dxPhiQ (Phi : ClosedC1Field) (j : Fin 2) : Continuous (dxPhiQ Phi j) := by
  have h := Phi.continuousOn_fderiv_QSet.clm_apply
    (continuousOn_const (c := ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))))
  exact continuousOn_iff_continuous_domRestrict.mp h

theorem measurable_dtPhiQ (Phi : ClosedC1Field) : Measurable (dtPhiQ Phi) :=
  (continuous_dtPhiQ Phi).measurable

theorem measurable_dxPhiQ (Phi : ClosedC1Field) (j : Fin 2) : Measurable (dxPhiQ Phi j) :=
  (continuous_dxPhiQ Phi j).measurable

#print axioms ClosedC1Field.differentiableAt_QSet
#print axioms continuous_dtPhiQ
#print axioms continuous_dxPhiQ

end MatrixTransport

namespace MatrixTransport

theorem ClosedC1Field.fderiv_isHermitian (Phi : ClosedC1Field) {p : Ambient}
    (hp : p ∈ QSet) (v : Ambient) :
    (fderiv ℝ Phi.toFun p v).IsHermitian := by
  have hd : DifferentiableAt ℝ Phi.toFun p := Phi.differentiableAt_QSet hp
  have e : ∀ a b : Fin 2,
      fderiv ℝ (fun x => Phi.toFun x a b) p v = fderiv ℝ Phi.toFun p v a b := by
    intro a b
    have h2 : DifferentiableAt ℝ (fun x => Phi.toFun x a) p := differentiableAt_pi.1 hd a
    have e1 : fderiv ℝ (fun x => Phi.toFun x a b) p =
        (ContinuousLinearMap.proj b).comp (fderiv ℝ (fun x => Phi.toFun x a) p) :=
      fderiv_apply h2 b
    have e2 : fderiv ℝ (fun x => Phi.toFun x a) p =
        (ContinuousLinearMap.proj a).comp (fderiv ℝ Phi.toFun p) :=
      fderiv_apply hd a
    rw [e1, e2]
    first | rfl | simp
  refine Matrix.IsHermitian.ext fun i j => ?_
  rw [star_trivial]
  have hsym : (fun x => Phi.toFun x i j) = (fun x => Phi.toFun x j i) := by
    funext x
    have h := (Phi.globallyHermitian x).apply i j
    rw [star_trivial] at h
    exact h.symm
  exact (e j i).symm.trans
    ((congrArg (fun f :Ambient → ℝ => fderiv ℝ f p v) hsym.symm).trans (e i j))

theorem dtPhiQ_isHermitian (Phi : ClosedC1Field) (q : Q) : (dtPhiQ Phi q).IsHermitian :=
  Phi.fderiv_isHermitian q.2 _

theorem dxPhiQ_isHermitian (Phi : ClosedC1Field) (j : Fin 2) (q : Q) :
    (dxPhiQ Phi j q).IsHermitian :=
  Phi.fderiv_isHermitian q.2 _

theorem exists_coord_bound {ι : Type*} [Fintype ι] (a : Q → (ι → ℝ)) (ha : Continuous a) :
    ∃ C : ℝ, ∀ q c, |a q c| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_norm.comp ha)).bddAbove
  refine ⟨C, fun q c => ?_⟩
  have h1 : ‖a q c‖ ≤ ‖a q‖ := norm_le_pi_norm (a q) c
  have h2 : ‖a q‖ ≤ C := hC (Set.mem_range_self q)
  rw [← Real.norm_eq_abs]
  exact h1.trans h2

#print axioms ClosedC1Field.fderiv_isHermitian
#print axioms dtPhiQ_isHermitian
#print axioms dxPhiQ_isHermitian
#print axioms exists_coord_bound

end MatrixTransport
