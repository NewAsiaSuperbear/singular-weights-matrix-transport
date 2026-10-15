import MatrixTransport.Continuity
import MatrixTransport.Oscillation

set_option autoImplicit false

open scoped Matrix.Norms.Elementwise

noncomputable section

namespace MatrixTransport

def certificateScalar (n : ℕ) (s : ℝ) (p : Ambient) : ℝ :=
  s * Real.cos (waveNumber n * p.2 0) - s ^ 2 * p.1

def certificateMatrix (n : ℕ) (s : ℝ) (p : Ambient) : Mat2 :=
  certificateScalar n s p • E

def certificateFDeriv (n : ℕ) (s : ℝ) (p : Ambient) : Ambient →L[ℝ] Mat2 :=
  ((s • (-Real.sin (waveNumber n * p.2 0) •
      (waveNumber n • coord0.comp (ContinuousLinearMap.snd ℝ ℝ Spatial))) -
    s ^ 2 • ContinuousLinearMap.fst ℝ ℝ Spatial)).smulRight E

theorem certificateMatrix_hasFDerivAt (n : ℕ) (s : ℝ) (p : Ambient) :
    HasFDerivAt (certificateMatrix n s) (certificateFDeriv n s p) p := by
  have h1 : HasFDerivAt (fun x : Ambient => x.2 0)
      (coord0.comp (ContinuousLinearMap.snd ℝ ℝ Spatial)) p :=
    HasFDerivAt.comp p (coord0.hasFDerivAt) ((ContinuousLinearMap.snd ℝ ℝ Spatial).hasFDerivAt)
  have h2 : HasFDerivAt (fun x : Ambient => x.1) (ContinuousLinearMap.fst ℝ ℝ Spatial) p :=
    (ContinuousLinearMap.fst ℝ ℝ Spatial).hasFDerivAt
  have h3 := (h1.const_mul (waveNumber n)).cos
  have h4 := (h3.const_mul s).sub (h2.const_mul (s ^ 2))
  have h5 := h4.smul_const E
  exact h5

theorem certificateMatrix_isHermitian (n : ℕ) (s : ℝ) (p : Ambient) :
    (certificateMatrix n s p).IsHermitian :=
  E_posSemidef.isHermitian.smul (star_trivial _)

theorem certificateMatrix_contDiff (n : ℕ) (s : ℝ) : ContDiff ℝ 1 (certificateMatrix n s) := by
  have h1 : ContDiff ℝ 1 (fun x : Ambient => x.2 0) :=
    coord0.contDiff.comp contDiff_snd
  have h3 : ContDiff ℝ 1 (fun x : Ambient => Real.cos (waveNumber n * x.2 0)) :=
    Real.contDiff_cos.comp (contDiff_const.mul h1)
  have h4 : ContDiff ℝ 1 (certificateScalar n s) :=
    (contDiff_const.mul h3).sub (contDiff_const.mul contDiff_fst)
  exact h4.smul contDiff_const

def certificateField (n : ℕ) (s : ℝ) : ClosedC1Field where
  toFun := certificateMatrix n s
  globallyHermitian := certificateMatrix_isHermitian n s
  c1_neighborhood :=
    ⟨Set.univ, isOpen_univ, Set.subset_univ _, (certificateMatrix_contDiff n s).contDiffOn⟩

theorem certificateField_dtPhi (n : ℕ) (s : ℝ) (p : Ambient) :
    dtPhi (certificateField n s) p = (-(s ^ 2)) • E := by
  show fderiv ℝ (certificateMatrix n s) p ((1 : ℝ), (0 : Spatial)) = _
  rw [(certificateMatrix_hasFDerivAt n s p).fderiv]
  unfold certificateFDeriv
  rw [ContinuousLinearMap.smulRight_apply]
  congr 1
  simp

theorem certificateField_dxPhi (n : ℕ) (s : ℝ) (j : Fin 2) (p : Ambient) :
    dxPhi (certificateField n s) j p =
      (-s * waveNumber n * Real.sin (waveNumber n * p.2 0) *
        (EuclideanSpace.single j (1 : ℝ)) 0) • E := by
  show fderiv ℝ (certificateMatrix n s) p ((0 : ℝ), EuclideanSpace.single j (1 : ℝ)) = _
  rw [(certificateMatrix_hasFDerivAt n s p).fderiv]
  unfold certificateFDeriv
  rw [ContinuousLinearMap.smulRight_apply]
  congr 1
  have hc : coord0 (EuclideanSpace.single j (1 : ℝ)) = (EuclideanSpace.single j (1 : ℝ)) 0 := by
    rfl
  simp [hc, mul_comm, mul_left_comm, mul_assoc]

theorem certificateField_KBstar (n : ℕ) (s : ℝ) (q : Q) :
    KBstar (certificateField n s) q = 0 := by
  ext i k
  simp only [KBstar, Fin.sum_univ_two, dxPhiQ, certificateField_dxPhi, Matrix.smul_apply,
    Matrix.zero_apply]
  fin_cases i <;> simp [E_zero_zero, E_zero_one, E_one_zero, E_one_one]

theorem certificateField_localHJ (n : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 8) :
    LocalHJ KBDstar (certificateField n s) := by
  intro q
  have h1 : dtPhiQ (certificateField n s) q = (-(s ^ 2)) • E :=
    certificateField_dtPhi n s (q : Ambient)
  have h2 : KBDstar (certificateField n s) q = 0 := certificateField_KBstar n s q
  have ht : (q : Ambient).1 ∈ Set.Icc (0 : ℝ) 1 := q.property.1
  have hc : |Real.cos (waveNumber n * (q : Ambient).2 0)| ≤ 1 := Real.abs_cos_le_one _
  show LocalDualConstraint (dtPhiQ (certificateField n s) q)
    (KBDstar (certificateField n s) q) (certificateScalar n s (q : Ambient) • E)
  rw [h1, h2]
  exact local_dual_certificate (r := 1) s _ _ hs0 hs hc ht.1 ht.2

#print axioms certificateField_dtPhi
#print axioms certificateField_dxPhi
#print axioms certificateField_KBstar
#print axioms certificateField_localHJ

end MatrixTransport

end

noncomputable section

namespace MatrixTransport

open MeasureTheory
open scoped ENNReal

theorem frob_density_smul_E (u a : ℝ) : frob (density u) (a • E) = (1 + u) * a := by
  simp [frob, density, E, Matrix.diagonal_apply]

theorem certificateField_endpointDifference (n : ℕ) (s : ℝ) (ρ : Spatial → ℝ)
    (hρ : Integrable ρ diskVolume) (hmean : (∫ x, ρ x ∂diskVolume) = 0) :
    endpointDifference (fun _ => density 0) (fun x => density (ρ x)) (certificateField n s)
      = s * (∫ x, ρ x * Real.cos (waveNumber n * x 0) ∂diskVolume) - s ^ 2 * Real.pi := by
  have hcont : Continuous fun x : Spatial => Real.cos (waveNumber n * x 0) := by
    fun_prop
  have hc : Integrable (fun x : Spatial => Real.cos (waveNumber n * x 0)) diskVolume := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hρc : Integrable (fun x : Spatial => ρ x * Real.cos (waveNumber n * x 0)) diskVolume := by
    refine Integrable.mono' hρ.norm (hρ.aestronglyMeasurable.mul hc.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖ρ x * Real.cos (waveNumber n * x 0)‖ ≤ ‖ρ x‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have h1 : Integrable (fun x : Spatial => s * Real.cos (waveNumber n * x 0)) diskVolume :=
    hc.const_mul s
  have h2 : Integrable (fun x : Spatial => s * (ρ x * Real.cos (waveNumber n * x 0)))
      diskVolume := hρc.const_mul s
  have hA : Integrable (fun x : Spatial => s * Real.cos (waveNumber n * x 0)
      + s * (ρ x * Real.cos (waveNumber n * x 0))) diskVolume := h1.add h2
  have hB : Integrable (fun x : Spatial => s * Real.cos (waveNumber n * x 0)
      + s * (ρ x * Real.cos (waveNumber n * x 0)) - s ^ 2) diskVolume :=
    hA.sub (integrable_const _)
  have key1 : ∀ x : Spatial,
      frob (density (ρ x)) ((certificateField n s).toFun (1, x))
        = s * Real.cos (waveNumber n * x 0) + s * (ρ x * Real.cos (waveNumber n * x 0))
          - s ^ 2 - s ^ 2 * ρ x := by
    intro x
    show frob (density (ρ x)) (certificateScalar n s (1, x) • E) = _
    rw [frob_density_smul_E]
    simp only [certificateScalar]
    ring
  have key0 : ∀ x : Spatial,
      frob (density 0) ((certificateField n s).toFun (0, x))
        = s * Real.cos (waveNumber n * x 0) := by
    intro x
    show frob (density 0) (certificateScalar n s (0, x) • E) = _
    rw [frob_density_smul_E]
    simp only [certificateScalar]
    ring
  have e1 : endpointPair (fun x => density (ρ x)) (certificateField n s) 1
      = ∫ x, (s * Real.cos (waveNumber n * x 0) + s * (ρ x * Real.cos (waveNumber n * x 0))
          - s ^ 2 - s ^ 2 * ρ x) ∂diskVolume := by
    unfold endpointPair
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => key1 x)
  have e0 : endpointPair (fun _ => density 0) (certificateField n s) 0
      = ∫ x, s * Real.cos (waveNumber n * x 0) ∂diskVolume := by
    unfold endpointPair
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => key0 x)
  unfold endpointDifference
  rw [e1, e0, integral_sub hB (hρ.const_mul _), integral_sub hA (integrable_const _),
    integral_add h1 h2]
  simp only [integral_const_mul, integral_const, hmean, diskVolume_real_univ_eq_pi,
    smul_eq_mul]
  ring

theorem certificateField_lower_bound (n : ℕ) (s : ℝ) (ρ : Spatial → ℝ)
    (hρ : Integrable ρ diskVolume) (hmean : (∫ x, ρ x ∂diskVolume) = 0)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 8) :
    ENNReal.ofReal (s * (∫ x, ρ x * Real.cos (waveNumber n * x 0) ∂diskVolume)
        - s ^ 2 * Real.pi)
      ≤ wbSquared KBDstar (fun _ => density 0) (fun x => density (ρ x)) := by
  have h := ofReal_endpointDifference_le_wbSquared_KB (fun _ => density 0)
    (fun x => density (ρ x)) (certificateField n s) (certificateField_localHJ n s hs0 hs)
  rwa [certificateField_endpointDifference n s ρ hρ hmean] at h

#print axioms certificateField_endpointDifference
#print axioms certificateField_lower_bound

end MatrixTransport

end
