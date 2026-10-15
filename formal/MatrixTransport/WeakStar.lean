import Mathlib
import MatrixTransport.EndpointLimits

set_option autoImplicit false

noncomputable section

namespace MatrixTransport

open MeasureTheory Filter Topology

abbrev Disk := ↥disk

noncomputable instance : MeasureSpace Disk := Measure.Subtype.measureSpace

noncomputable def diskIntrinsicVolume : Measure Disk := volume

instance Disk_compactSpace : CompactSpace Disk :=
  isCompact_iff_compactSpace.mp disk_isCompact

theorem diskIntrinsicVolume_univ_eq_pi :
    diskIntrinsicVolume Set.univ = ENNReal.ofReal Real.pi := by
  unfold diskIntrinsicVolume
  rw [Measure.Subtype.volume_univ disk_measurableSet.nullMeasurableSet]
  exact disk_volume_eq_pi

instance Disk_volume_isFinite : IsFiniteMeasure (volume : Measure Disk) :=
  ⟨by
    have h := diskIntrinsicVolume_univ_eq_pi
    unfold diskIntrinsicVolume at h
    rw [h]
    exact ENNReal.ofReal_lt_top⟩

instance diskIntrinsicVolume_isFinite : IsFiniteMeasure diskIntrinsicVolume :=
  ⟨by
    rw [diskIntrinsicVolume_univ_eq_pi]
    exact ENNReal.ofReal_lt_top⟩

theorem integral_diskIntrinsicVolume (F : Spatial → ℝ) :
    (∫ x : Disk, F (x : Spatial) ∂diskIntrinsicVolume) = ∫ x, F x ∂diskVolume := by
  unfold diskIntrinsicVolume
  rw [Measure.Subtype.volume_def]
  exact integral_subtype_comap disk_measurableSet F

theorem exists_scalarDiskTest_extension (f : C(Disk, ℝ)) :
    ∃ g : C(Spatial, ℝ), ∀ x : Disk, g (x : Spatial) = f x := by
  have hc : IsClosed disk := by
    unfold disk
    exact Metric.isClosed_closedBall
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (X := Spatial) hc f
  exact ⟨g, fun x => DFunLike.congr_fun hg x⟩

theorem tendsto_integral_endpointWave_diskTest (f : C(Disk, ℝ)) :
    Tendsto (fun n : ℕ => ∫ x : Disk, endpointWave n (x : Spatial) * f x ∂diskIntrinsicVolume)
      atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := exists_scalarDiskTest_extension f
  have h1 : ∀ n : ℕ, (∫ x : Disk, endpointWave n (x : Spatial) * f x ∂diskIntrinsicVolume)
      = ∫ x, endpointWave n x * g x := by
    intro n
    have e : (fun x : Disk => endpointWave n (x : Spatial) * f x)
        = fun x : Disk => (fun y : Spatial => endpointWave n y * g y) (x : Spatial) := by
      funext x
      simp only [hg x]
    rw [e]
    exact (integral_diskIntrinsicVolume (fun y => endpointWave n y * g y)).trans
      (integral_diskVolume_eq _ (fun x hx => by
        simp [endpointWave_eq_zero_outside n hx]))
  have h2 : (fun n : ℕ => ∫ x : Disk, endpointWave n (x : Spatial) * f x ∂diskIntrinsicVolume)
      = fun n : ℕ => ∫ x, endpointWave n x * g x := funext h1
  rw [h2]
  exact tendsto_integral_endpointWave_mul g.continuous

#print axioms integral_diskIntrinsicVolume
#print axioms tendsto_integral_endpointWave_diskTest

end MatrixTransport

end

noncomputable section

namespace MatrixTransport

open MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def baseEndpoint (x : Spatial) : Mat2 := density 0

def waveEndpoint (n : ℕ) (x : Spatial) : Mat2 := density ((1 / 4 : ℝ) * endpointWave n x)

def weakStarConverges (g : ℕ → Spatial → Mat2) (g0 : Spatial → Mat2) : Prop :=
  ∀ Φ : C(Disk, Mat2),
    Tendsto (fun n => ∫ x : Disk, frob (g n (x : Spatial)) (Φ x) ∂diskIntrinsicVolume) atTop
      (𝓝 (∫ x : Disk, frob (g0 (x : Spatial)) (Φ x) ∂diskIntrinsicVolume))

theorem baseEndpoint_isHermitian (x : Spatial) : Matrix.IsHermitian (baseEndpoint x) :=
  density_isHermitian 0

theorem waveEndpoint_isHermitian (n : ℕ) (x : Spatial) : Matrix.IsHermitian (waveEndpoint n x) :=
  density_isHermitian _

theorem integrable_disk_continuous (f : Disk → ℝ) (hf : Continuous f) :
    Integrable f diskIntrinsicVolume :=
  hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport f) (Set.subset_univ _))

theorem waveEndpoint_weakStarConverges : weakStarConverges waveEndpoint baseEndpoint := by
  intro Φ
  let φ : C(Disk, ℝ) := ⟨fun x => Φ x 1 1, Φ.continuous.matrix_elem 1 1⟩
  have hφ : ∀ x : Disk, φ x = Φ x 1 1 := fun x => rfl
  have hpt : ∀ (n : ℕ) (x : Disk),
      frob (waveEndpoint n (x : Spatial)) (Φ x)
        = frob (baseEndpoint (x : Spatial)) (Φ x)
          + (1 / 4 : ℝ) * (endpointWave n (x : Spatial) * φ x) := by
    intro n x
    rw [hφ]
    simp only [waveEndpoint, baseEndpoint, frob_density_diag]
    ring
  have hbase_eq : (fun x : Disk => frob (baseEndpoint (x : Spatial)) (Φ x))
      = fun x : Disk => Φ x 0 0 + (1 + 0) * Φ x 1 1 := by
    funext x
    simp only [baseEndpoint, frob_density_diag]
  have hbase_cont : Continuous (fun x : Disk => frob (baseEndpoint (x : Spatial)) (Φ x)) := by
    rw [hbase_eq]
    exact (Φ.continuous.matrix_elem 0 0).add
      (continuous_const.mul (Φ.continuous.matrix_elem 1 1))
  have hbase_int : Integrable (fun x : Disk => frob (baseEndpoint (x : Spatial)) (Φ x))
      diskIntrinsicVolume := integrable_disk_continuous _ hbase_cont
  have hpert_int : ∀ n : ℕ, Integrable
      (fun x : Disk => (1 / 4 : ℝ) * (endpointWave n (x : Spatial) * φ x)) diskIntrinsicVolume := by
    intro n
    have hc : Continuous (fun x : Disk => endpointWave n (x : Spatial) * φ x) :=
      ((endpointWave_continuous n).comp continuous_subtype_val).mul φ.continuous
    exact integrable_disk_continuous _ (continuous_const.mul hc)
  have hsplit : ∀ n : ℕ,
      (∫ x : Disk, frob (waveEndpoint n (x : Spatial)) (Φ x) ∂diskIntrinsicVolume)
        = (∫ x : Disk, frob (baseEndpoint (x : Spatial)) (Φ x) ∂diskIntrinsicVolume)
          + (1 / 4 : ℝ) * ∫ x : Disk, endpointWave n (x : Spatial) * φ x ∂diskIntrinsicVolume := by
    intro n
    have e : (fun x : Disk => frob (waveEndpoint n (x : Spatial)) (Φ x))
        = fun x : Disk => frob (baseEndpoint (x : Spatial)) (Φ x)
          + (1 / 4 : ℝ) * (endpointWave n (x : Spatial) * φ x) := funext (hpt n)
    rw [e, integral_add hbase_int (hpert_int n), integral_const_mul]
  have hfun :
      (fun n : ℕ => ∫ x : Disk, frob (waveEndpoint n (x : Spatial)) (Φ x) ∂diskIntrinsicVolume)
      = fun n : ℕ =>
        (∫ x : Disk, frob (baseEndpoint (x : Spatial)) (Φ x) ∂diskIntrinsicVolume)
          + (1 / 4 : ℝ) * ∫ x : Disk, endpointWave n (x : Spatial) * φ x ∂diskIntrinsicVolume :=
    funext hsplit
  rw [hfun]
  have h := ((tendsto_integral_endpointWave_diskTest φ).const_mul (1 / 4 : ℝ)).const_add
    (∫ x : Disk, frob (baseEndpoint (x : Spatial)) (Φ x) ∂diskIntrinsicVolume)
  rw [mul_zero, add_zero] at h
  exact h

theorem exists_uniform_waveEndpoint_bounds :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : Spatial,
      LoewnerLE ((1 / 2 : ℝ) • (1 : Mat2)) (waveEndpoint n x) ∧
      LoewnerLE (waveEndpoint n x) ((3 / 2 : ℝ) • (1 : Mat2)) := by
  obtain ⟨N, hN⟩ := exists_uniform_endpointWave_bound
  refine ⟨N, fun n hn x => ?_⟩
  have hb : |(1 / 4 : ℝ) * endpointWave n x| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have := hN n hn x
    linarith
  exact ⟨loewner_density_lower _ hb, loewner_density_upper _ hb⟩

#print axioms waveEndpoint_weakStarConverges
#print axioms exists_uniform_waveEndpoint_bounds

end MatrixTransport

end

noncomputable section

namespace MatrixTransport

open scoped ContDiff Matrix.Norms.Elementwise

theorem dChi_contDiff : ContDiff ℝ ∞ dChi :=
  show ContDiff ℝ ∞ (fun x => fderiv ℝ chi x e1) from
    (chi_contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem endpointWave_contDiff (n : ℕ) : ContDiff ℝ ∞ (endpointWave n) := by
  have hs : ContDiff ℝ ∞ (fun x : Spatial => Real.sin (waveNumber n * x 0)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_coord)
  have hc : ContDiff ℝ ∞ (fun x : Spatial => Real.cos (waveNumber n * x 0)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_coord)
  show ContDiff ℝ ∞ (fun x : Spatial =>
    dChi x * Real.sin (waveNumber n * x 0) / waveNumber n
      + chi x * Real.cos (waveNumber n * x 0))
  exact ((dChi_contDiff.mul hs).div_const _).add (chi_contDiff.mul hc)

theorem baseEndpoint_contDiff : ContDiff ℝ ∞ baseEndpoint :=
  contDiff_const

theorem waveEndpoint_contDiff (n : ℕ) : ContDiff ℝ ∞ (waveEndpoint n) := by
  have h : waveEndpoint n
      = fun x : Spatial => (1 : Mat2) + ((1 / 4 : ℝ) * endpointWave n x) • E := by
    funext x
    simp only [waveEndpoint, density_eq]
  rw [h]
  exact contDiff_const.add
    ((contDiff_const.mul (endpointWave_contDiff n)).smul contDiff_const)

#print axioms endpointWave_contDiff
#print axioms waveEndpoint_contDiff

end MatrixTransport

end
