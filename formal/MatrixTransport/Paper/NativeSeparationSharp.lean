import MatrixTransport.Paper.NativeSeparationRegime

/-!
# The literal cutoff-dependent action bound in the smooth separation proof

The spatial integral in the first bound is over the disk. The final cutoff integral
is over the whole spatial space, as in the manuscript's squared L² norm.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport

theorem lintegral_volumeQ_time_indep (F : Spatial → ℝ)
    (hF : ContinuousOn F disk) (h0 : ∀ x, 0 ≤ F x) :
    (∫⁻ q : Q, ENNReal.ofReal (F (q : Ambient).2) ∂volumeQ) =
      ENNReal.ofReal (∫ x, F x ∂diskVolume) := by
  have hc : ContinuousOn (fun p : Ambient ↦ F p.2) QSet :=
    hF.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hcont : Continuous (fun q : Q ↦ F (q : Ambient).2) :=
    continuousOn_iff_continuous_domRestrict.mp hc
  have hi : Integrable (fun q : Q ↦ F (q : Ambient).2) volumeQ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ h0 _),
    integral_volumeQ_eq_space_time _ hc]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  simp [integral_const, measureReal_def, Real.volume_Icc]

theorem affinePath_action_le_L2 (m : ℕ) (ε : ℝ)
    (hb : ∀ x : Spatial, |ε * endpointWave m x| ≤ (1 / 2 : ℝ)) :
    matrixAction 8 (affinePath m ε).coords ≤
      ENNReal.ofReal (ε ^ 2 * ∫ x, primitiveWave m x ^ 2 ∂diskVolume) := by
  rw [affinePath_action_eq]
  have hpt : ∀ q : Q, matrixCost 8 (affineTriplet m ε q) ≤
      ENNReal.ofReal (ε ^ 2 * primitiveWave m (q : Ambient).2 ^ 2) := by
    intro q
    have ht := q.property.1
    have hu : |(q : Ambient).1 * ε * endpointWave m (q : Ambient).2| ≤ 1 / 2 := by
      rw [mul_assoc, abs_mul, abs_of_nonneg ht.1]
      have h2 := hb (q : Ambient).2
      nlinarith [mul_nonneg (sub_nonneg.2 ht.2)
        (abs_nonneg (ε * endpointWave m (q : Ambient).2))]
    have h := matrixCost_single_flux_upper (r := 8) (1 : Fin 8)
      ((q : Ambient).1 * ε * endpointWave m (q : Ambient).2)
      (-ε * primitiveWave m (q : Ambient).2) hu
    convert h using 1 <;> congr 1 <;> ring
  calc
    (∫⁻ q : Q, matrixCost 8 (affineTriplet m ε q) ∂volumeQ) ≤
        ∫⁻ q : Q, ENNReal.ofReal (ε ^ 2 * primitiveWave m (q : Ambient).2 ^ 2)
          ∂volumeQ := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ x, ε ^ 2 * primitiveWave m x ^ 2 ∂diskVolume) :=
      lintegral_volumeQ_time_indep _
        (continuous_const.mul ((primitiveWave_continuous m).pow 2)).continuousOn
        (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by rw [integral_const_mul]

theorem integral_primitiveWave_sq_le (m : ℕ) :
    (∫ x, primitiveWave m x ^ 2 ∂diskVolume) ≤
      (∫ x : Spatial, chi x ^ 2) / waveNumber m ^ 2 := by
  have hc : Integrable (fun x : Spatial ↦ chi x ^ 2) volume :=
    chi_sq_integrable
  have hh : Integrable (fun x : Spatial ↦ primitiveWave m x ^ 2) diskVolume :=
    ((primitiveWave_continuous m).pow 2).continuousOn.integrableOn_compact disk_isCompact
  have hcs : Integrable (fun x : Spatial ↦ chi x ^ 2 / waveNumber m ^ 2) diskVolume :=
    (hc.integrableOn).div_const _
  have he : (∫ x, chi x ^ 2 ∂diskVolume) = ∫ x : Spatial, chi x ^ 2 :=
    integral_diskVolume_eq _ (fun x hx ↦ by
      have hz : chi x = 0 := by
        by_contra hn
        exact hx (chi_tsupport_subset_disk
          (subset_tsupport _ (Function.mem_support.2 hn)))
      simp [hz])
  calc
    (∫ x, primitiveWave m x ^ 2 ∂diskVolume) ≤
        ∫ x, chi x ^ 2 / waveNumber m ^ 2 ∂diskVolume :=
      integral_mono hh hcs (fun x ↦ primitiveWave_sq_le m x)
    _ = _ := by rw [integral_div, he]

end MatrixTransport

namespace LiZouTransport.NativeSeparation

open MatrixTransport

theorem full_native_upper_L2 (m : ℕ)
    (hb : ∀ x : Spatial, |(1 / 4 : ℝ) * endpointWave m x| ≤ (1 / 2 : ℝ)) :
    smoothValue fullOperator (fun x ↦ (1 / 4 : ℝ) * endpointWave m x)
        (continuous_const.mul (endpointWave_continuous m)) hb ≤
      ENNReal.ofReal ((1 / 16 : ℝ) * ∫ x, primitiveWave m x ^ 2 ∂diskVolume) ∧
    (1 / 16 : ℝ) * (∫ x, primitiveWave m x ^ 2 ∂diskVolume) ≤
      (∫ x : Spatial, chi x ^ 2) / (16 * waveNumber m ^ 2) := by
  constructor
  · have hGood : MatrixTransport.ReactionZero.Limit.Good
        (smoothProblem fullOperator (fun x ↦ (1 / 4 : ℝ) * endpointWave m x)
          (continuous_const.mul (endpointWave_continuous m)) hb) (affinePath m (1 / 4)).coords :=
      ⟨(affinePath m (1 / 4)).massSymmetry, affinePath_nativeCE m (1 / 4)⟩
    have hmin : smoothValue fullOperator (fun x ↦ (1 / 4 : ℝ) * endpointWave m x)
        (continuous_const.mul (endpointWave_continuous m)) hb ≤
        MatrixTransport.ReactionZero.action (1 : Matrix (Fin 8) (Fin 8) ℝ) 1
          (affinePath m (1 / 4)).coords :=
      iInf_le_of_le _ (iInf_le_of_le hGood le_rfl)
    have hbound := affinePath_action_le_L2 m (1 / 4) hb
    rw [show (1 / 4 : ℝ) ^ 2 = 1 / 16 by norm_num] at hbound
    exact hmin.trans ((action_identity 8 _).le.trans hbound)
  · have h := mul_le_mul_of_nonneg_left (integral_primitiveWave_sq_le m)
        (by norm_num : (0 : ℝ) ≤ 1 / 16)
    calc
      _ ≤ (1 / 16 : ℝ) * ((∫ x : Spatial, chi x ^ 2) / waveNumber m ^ 2) := h
      _ = _ := by ring

theorem tendsto_chi_L2_bound (N : ℕ) :
    Tendsto (fun j : ℕ ↦ (∫ x : Spatial, chi x ^ 2) / (16 * waveNumber (j + N) ^ 2))
      atTop (𝓝 0) := by
  have hk : Tendsto (fun j : ℕ ↦ waveNumber (j + N)) atTop atTop :=
    tendsto_waveNumber_atTop.comp (tendsto_add_atTop_nat N)
  have h := ((tendsto_inv_atTop_zero.comp hk).pow 2).const_mul
    ((∫ x : Spatial, chi x ^ 2) / 16)
  have h2 : Tendsto
      (fun j : ℕ ↦ ((∫ x : Spatial, chi x ^ 2) / 16) * (waveNumber (j + N))⁻¹ ^ 2)
      atTop (𝓝 0) := by simpa using h
  exact h2.congr (fun _ ↦ by ring)

#print axioms full_native_upper_L2
#print axioms tendsto_chi_L2_bound

end LiZouTransport.NativeSeparation

