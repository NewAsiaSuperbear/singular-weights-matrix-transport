import MatrixTransport.Continuity
import MatrixTransport.Oscillation

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace MatrixTransport

def affineTriplet (n : ℕ) (eps : ℝ) (q : Q) : TransportCoord 8 → ℝ :=
  packTriplet (density ((q : Ambient).1 * eps * endpointWave n (q : Ambient).2))
    (singleFlux (1 : Fin 8) (-eps * primitiveWave n (q : Ambient).2)) 0

theorem affineTriplet_inl (n : ℕ) (eps : ℝ) (q : Q) (i j : Fin 2) :
    affineTriplet n eps q (Sum.inl (i, j)) =
      density ((q : Ambient).1 * eps * endpointWave n (q : Ambient).2) i j := rfl

def affinePath (n : ℕ) (eps : ℝ) : MatrixPath 8 :=
  { coords := fun c ↦ volumeQ.withDensityᵥ (fun q ↦ affineTriplet n eps q c)
    massSymmetry := by
      intro i j
      show volumeQ.withDensityᵥ (fun q ↦ affineTriplet n eps q (Sum.inl (i, j))) =
        volumeQ.withDensityᵥ (fun q ↦ affineTriplet n eps q (Sum.inl (j, i)))
      congr 1
      funext q
      rw [affineTriplet_inl, affineTriplet_inl, density_apply, density_apply]
      by_cases h : i = j
      · subst h
        rfl
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)] }

@[simp] theorem affinePath_coords (n : ℕ) (eps : ℝ) :
    (affinePath n eps).coords =
      fun c ↦ volumeQ.withDensityᵥ (fun q ↦ affineTriplet n eps q c) := rfl

theorem continuous_affine_u (n : ℕ) (eps : ℝ) :
    Continuous (fun q : Q ↦ (q : Ambient).1 * eps * endpointWave n (q : Ambient).2) := by
  have h1 : Continuous fun q : Q ↦ (q : Ambient).1 := continuous_fst.comp continuous_subtype_val
  have h2 : Continuous fun q : Q ↦ (q : Ambient).2 := continuous_snd.comp continuous_subtype_val
  exact (h1.mul continuous_const).mul ((endpointWave_continuous n).comp h2)

theorem continuous_affine_v (n : ℕ) (eps : ℝ) :
    Continuous (fun q : Q ↦ -eps * primitiveWave n (q : Ambient).2) := by
  have h2 : Continuous fun q : Q ↦ (q : Ambient).2 := continuous_snd.comp continuous_subtype_val
  exact continuous_const.mul ((primitiveWave_continuous n).comp h2)

theorem continuous_affineTriplet (n : ℕ) (eps : ℝ) : Continuous (affineTriplet n eps) := by
  refine continuous_pi fun c ↦ ?_
  have hu := continuous_affine_u n eps
  have hv := continuous_affine_v n eps
  rcases c with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · show Continuous fun q : Q ↦
      density ((q : Ambient).1 * eps * endpointWave n (q : Ambient).2) i j
    simp only [density_apply]
    split_ifs <;> first | exact continuous_const | exact continuous_const.add hu
  · show Continuous fun q : Q ↦
      singleFlux (1 : Fin 8) (-eps * primitiveWave n (q : Ambient).2) i j
    by_cases h : i = 1 ∧ j = 1
    · simp only [singleFlux, ite_eq_left h]
      exact hv
    · simp only [singleFlux, ite_eq_right h]
      exact continuous_const
  · show Continuous fun _ : Q ↦ (0 : Mat2) i j
    exact continuous_const

theorem continuous_affineTriplet_coord (n : ℕ) (eps : ℝ) (c : TransportCoord 8) :
    Continuous (fun q : Q ↦ affineTriplet n eps q c) :=
  (continuous_apply c).comp (continuous_affineTriplet n eps)

theorem measurable_affineTriplet_coord (n : ℕ) (eps : ℝ) (c : TransportCoord 8) :
    Measurable (fun q : Q ↦ affineTriplet n eps q c) :=
  (continuous_affineTriplet_coord n eps c).measurable

theorem integrable_affineTriplet_coord (n : ℕ) (eps : ℝ) (c : TransportCoord 8) :
    Integrable (fun q : Q ↦ affineTriplet n eps q c) volumeQ := by
  have h := continuous_affineTriplet_coord n eps c
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem affineTriplet_coordinateWeight_one_le (n : ℕ) (eps : ℝ) (q : Q) :
    1 ≤ coordinateWeight (fun c q ↦ affineTriplet n eps q c) q := by
  have h : |affineTriplet n eps q (Sum.inl ((0 : Fin 2), (0 : Fin 2)))| ≤
      coordinateWeight (fun c q ↦ affineTriplet n eps q c) q :=
    abs_le_coordinateWeight (fun c q ↦ affineTriplet n eps q c) _ q
  have e : affineTriplet n eps q (Sum.inl ((0 : Fin 2), (0 : Fin 2))) = 1 := by
    rw [affineTriplet_inl]
    exact density_zero_zero _
  rw [e, abs_one] at h
  exact h

theorem affinePath_action_eq (n : ℕ) (eps : ℝ) :
    matrixAction 8 (affinePath n eps).coords =
      ∫⁻ q, matrixCost 8 (affineTriplet n eps q) ∂volumeQ := by
  have h := lintegral_canonicalDensity_withDensity (ν := volumeQ)
    (fun c q ↦ affineTriplet n eps q c)
    (fun c ↦ measurable_affineTriplet_coord n eps c)
    (fun c ↦ integrable_affineTriplet_coord n eps c)
    (fun q ↦ affineTriplet_coordinateWeight_one_le n eps q)
    (matrixCost 8) (measurable_matrixCost 8)
    (fun t ht v ↦ matrixCost_smul_nonneg 8 v ht)
  exact h

theorem affinePath_action_le (n : ℕ) (eps : ℝ)
    (hb : ∀ x : Spatial, |eps * endpointWave n x| ≤ (1 / 2 : ℝ)) :
    matrixAction 8 (affinePath n eps).coords ≤
      ENNReal.ofReal (Real.pi * eps ^ 2 / waveNumber n ^ 2) := by
  rw [affinePath_action_eq]
  have hpt : ∀ q : Q, matrixCost 8 (affineTriplet n eps q) ≤
      ENNReal.ofReal (eps ^ 2 / waveNumber n ^ 2) := by
    intro q
    have hq : (q : Ambient) ∈ Set.Icc (0 : ℝ) 1 ×ˢ disk := q.2
    have ht : (q : Ambient).1 ∈ Set.Icc (0 : ℝ) 1 := hq.1
    have hu : |(q : Ambient).1 * eps * endpointWave n (q : Ambient).2| ≤ 1 / 2 := by
      rw [mul_assoc, abs_mul, abs_of_nonneg ht.1]
      have h2 := hb (q : Ambient).2
      nlinarith [mul_nonneg (sub_nonneg.2 ht.2) (abs_nonneg (eps * endpointWave n (q : Ambient).2))]
    have h1 := matrixCost_single_flux_upper (r := 8) (1 : Fin 8)
      ((q : Ambient).1 * eps * endpointWave n (q : Ambient).2)
      (-eps * primitiveWave n (q : Ambient).2) hu
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hk : 0 ≤ waveNumber n ^ 2 := sq_nonneg _
    have hc2 : chi (q : Ambient).2 ^ 2 ≤ 1 := pow_le_one₀ (chi_nonneg _) (chi_le_one _)
    have hh1 := primitiveWave_sq_le n (q : Ambient).2
    have hh2 : chi (q : Ambient).2 ^ 2 / waveNumber n ^ 2 ≤ 1 / waveNumber n ^ 2 := by
      exact div_le_div_of_nonneg_right hc2 hk
    have hh : primitiveWave n (q : Ambient).2 ^ 2 ≤ 1 / waveNumber n ^ 2 := hh1.trans hh2
    calc (-eps * primitiveWave n (q : Ambient).2) ^ 2
        = eps ^ 2 * primitiveWave n (q : Ambient).2 ^ 2 := by ring
      _ ≤ eps ^ 2 * (1 / waveNumber n ^ 2) := mul_le_mul_of_nonneg_left hh (sq_nonneg eps)
      _ = eps ^ 2 / waveNumber n ^ 2 := by ring
  calc ∫⁻ q, matrixCost 8 (affineTriplet n eps q) ∂volumeQ
      ≤ ∫⁻ _q : Q, ENNReal.ofReal (eps ^ 2 / waveNumber n ^ 2) ∂volumeQ := lintegral_mono hpt
    _ = ENNReal.ofReal (eps ^ 2 / waveNumber n ^ 2) * volumeQ Set.univ := lintegral_const _
    _ = ENNReal.ofReal (Real.pi * eps ^ 2 / waveNumber n ^ 2) := by
        rw [volumeQ_univ_eq_pi, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end MatrixTransport

end
