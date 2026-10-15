import MatrixTransport.Continuity
import MatrixTransport.TimeTest

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace MatrixTransport

theorem frob_reaction_E (v : ℝ) (C : Mat2) : frob (v • E) C = v * C 1 1 := by
  simp only [frob, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, E_zero_zero, E_zero_one,
    E_one_zero, E_one_one]
  ring

theorem single_reaction_upper {r : ℕ} (u v : ℝ) (A : Mat2) (B : Flux r) (C : Mat2)
    (hu : |u| ≤ 1 / 2) (hd : LocalDualConstraint A B C) :
    frob (density u) A + frob (v • E) C ≤ v ^ 2 := by
  have h0 := local_diag_bound A B C hd 0
  have h1 := local_diag_bound A B C hd 1
  have hb0 : 0 ≤ ∑ j, B 0 j * B 0 j := Finset.sum_nonneg (fun j _ ↦ mul_self_nonneg _)
  have hb1 : 0 ≤ ∑ j, B 1 j * B 1 j := Finset.sum_nonneg (fun j _ ↦ mul_self_nonneg _)
  have hc0 : 0 ≤ ∑ j, C 0 j * C 0 j := Finset.sum_nonneg (fun j _ ↦ mul_self_nonneg _)
  have hc1 : 0 ≤ ∑ j, C 1 j * C 1 j := Finset.sum_nonneg (fun j _ ↦ mul_self_nonneg _)
  have hle : C 1 1 * C 1 1 ≤ ∑ j, C 1 j * C 1 j :=
    Finset.single_le_sum (f := fun j ↦ C 1 j * C 1 j) (fun j _ ↦ mul_self_nonneg _)
      (Finset.mem_univ (1 : Fin 2))
  rw [frob_density_diag, frob_reaction_E]
  have hu' := abs_le.mp hu
  have ha1 : A 1 1 ≤ 0 := by linarith
  have hprod : 0 ≤ (1 / 2 + u) * (-(A 1 1)) :=
    mul_nonneg (by linarith [hu'.1]) (by linarith)
  have hsq : 0 ≤ (C 1 1 / 2 - v) * (C 1 1 / 2 - v) := mul_self_nonneg _
  nlinarith [h0, h1, hb0, hb1, hc0, hc1, hle, hprod, hsq]

theorem matrixCost_single_reaction_upper {r : ℕ} (u v : ℝ) (hu : |u| ≤ 1 / 2) :
    matrixCost r (packTriplet (density u) (0 : Flux r) (v • E)) ≤
      ENNReal.ofReal (v ^ 2) := by
  unfold matrixCost supportFunction
  refine iSup_le fun a ↦ iSup_le fun ha ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  rw [weightedPair_packTriplet]
  have h := single_reaction_upper u v (mass a) (flux a) (reaction a) hu ha.2
  have hz : frob (0 : Flux r) (flux a) = 0 := by simp [frob]
  linarith

end MatrixTransport

end

namespace MatrixTransport

noncomputable section

def reactionTriplet (rho : Spatial → ℝ) (q : Q) : TransportCoord 1 → ℝ :=
  packTriplet (density ((q : Ambient).1 * rho (q : Ambient).2))
    (0 : Flux 1) ((rho (q : Ambient).2) • E)

theorem reactionTriplet_inl (rho : Spatial → ℝ) (q : Q) (i j : Fin 2) :
    reactionTriplet rho q (Sum.inl (i, j)) =
      density ((q : Ambient).1 * rho (q : Ambient).2) i j := rfl

def reactionPath (rho : Spatial → ℝ) : MatrixPath 1 :=
  { coords := fun c ↦ volumeQ.withDensityᵥ (fun q ↦ reactionTriplet rho q c)
    massSymmetry := by
      intro i j
      show volumeQ.withDensityᵥ (fun q ↦ reactionTriplet rho q (Sum.inl (i, j))) =
        volumeQ.withDensityᵥ (fun q ↦ reactionTriplet rho q (Sum.inl (j, i)))
      congr 1
      funext q
      rw [reactionTriplet_inl, reactionTriplet_inl, density_apply, density_apply]
      by_cases h : i = j
      · subst h
        rfl
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)] }

@[simp] theorem reactionPath_coords (rho : Spatial → ℝ) :
    (reactionPath rho).coords =
      fun c ↦ volumeQ.withDensityᵥ (fun q ↦ reactionTriplet rho q c) := rfl

theorem continuous_reactionTriplet (rho : Spatial → ℝ) (hrho : Continuous rho) :
    Continuous (reactionTriplet rho) := by
  refine continuous_pi fun c ↦ ?_
  have h1 : Continuous fun q : Q ↦ (q : Ambient).1 := continuous_fst.comp continuous_subtype_val
  have h2 : Continuous fun q : Q ↦ (q : Ambient).2 := continuous_snd.comp continuous_subtype_val
  have hv : Continuous fun q : Q ↦ rho (q : Ambient).2 := hrho.comp h2
  have hu : Continuous fun q : Q ↦ (q : Ambient).1 * rho (q : Ambient).2 := h1.mul hv
  rcases c with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · show Continuous fun q : Q ↦
      density ((q : Ambient).1 * rho (q : Ambient).2) i j
    simp only [density_apply]
    split_ifs <;> first | exact continuous_const | exact continuous_const.add hu
  · show Continuous fun _ : Q ↦ (0 : Flux 1) i j
    exact continuous_const
  · show Continuous fun q : Q ↦ (rho (q : Ambient).2 • E) i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hv.mul continuous_const

theorem continuous_reactionTriplet_coord (rho : Spatial → ℝ) (hrho : Continuous rho)
    (c : TransportCoord 1) :
    Continuous (fun q : Q ↦ reactionTriplet rho q c) :=
  (continuous_apply c).comp (continuous_reactionTriplet rho hrho)

theorem measurable_reactionTriplet_coord (rho : Spatial → ℝ) (hrho : Continuous rho)
    (c : TransportCoord 1) :
    Measurable (fun q : Q ↦ reactionTriplet rho q c) :=
  (continuous_reactionTriplet_coord rho hrho c).measurable

theorem integrable_reactionTriplet_coord (rho : Spatial → ℝ) (hrho : Continuous rho)
    (c : TransportCoord 1) :
    Integrable (fun q : Q ↦ reactionTriplet rho q c) volumeQ := by
  have h := continuous_reactionTriplet_coord rho hrho c
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem reactionTriplet_coordinateWeight_one_le (rho : Spatial → ℝ) (q : Q) :
    1 ≤ coordinateWeight (fun c q ↦ reactionTriplet rho q c) q := by
  have h : |reactionTriplet rho q (Sum.inl ((0 : Fin 2), (0 : Fin 2)))| ≤
      coordinateWeight (fun c q ↦ reactionTriplet rho q c) q :=
    abs_le_coordinateWeight (fun c q ↦ reactionTriplet rho q c) _ q
  have e : reactionTriplet rho q (Sum.inl ((0 : Fin 2), (0 : Fin 2))) = 1 := by
    rw [reactionTriplet_inl]
    exact density_zero_zero _
  rw [e, abs_one] at h
  exact h

theorem reactionPath_action_eq (rho : Spatial → ℝ) (hrho : Continuous rho) :
    matrixAction 1 (reactionPath rho).coords =
      ∫⁻ q, matrixCost 1 (reactionTriplet rho q) ∂volumeQ := by
  have h := lintegral_canonicalDensity_withDensity (ν := volumeQ)
    (fun c q ↦ reactionTriplet rho q c)
    (fun c ↦ measurable_reactionTriplet_coord rho hrho c)
    (fun c ↦ integrable_reactionTriplet_coord rho hrho c)
    (fun q ↦ reactionTriplet_coordinateWeight_one_le rho q)
    (matrixCost 1) (measurable_matrixCost 1)
    (fun t ht v ↦ matrixCost_smul_nonneg 1 v ht)
  exact h

theorem reactionPath_action_le (rho : Spatial → ℝ) (hrho : Continuous rho)
    (hb : ∀ x : Spatial, |rho x| ≤ (1 / 2 : ℝ)) :
    matrixAction 1 (reactionPath rho).coords ≤ ENNReal.ofReal (Real.pi / 4) := by
  rw [reactionPath_action_eq rho hrho]
  have hpt : ∀ q : Q, matrixCost 1 (reactionTriplet rho q) ≤
      ENNReal.ofReal (1 / 4 : ℝ) := by
    intro q
    have hq : (q : Ambient) ∈ Set.Icc (0 : ℝ) 1 ×ˢ disk := q.2
    have ht : (q : Ambient).1 ∈ Set.Icc (0 : ℝ) 1 := hq.1
    have h2 := hb (q : Ambient).2
    have hu : |(q : Ambient).1 * rho (q : Ambient).2| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      nlinarith [mul_nonneg (sub_nonneg.2 ht.2) (abs_nonneg (rho (q : Ambient).2))]
    have h1 := matrixCost_single_reaction_upper (r := 1)
      ((q : Ambient).1 * rho (q : Ambient).2) (rho (q : Ambient).2) hu
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [sq_abs (rho (q : Ambient).2), abs_nonneg (rho (q : Ambient).2), h2]
  calc ∫⁻ q, matrixCost 1 (reactionTriplet rho q) ∂volumeQ
      ≤ ∫⁻ _q : Q, ENNReal.ofReal (1 / 4 : ℝ) ∂volumeQ := lintegral_mono hpt
    _ = ENNReal.ofReal (1 / 4 : ℝ) * volumeQ Set.univ := lintegral_const _
    _ = ENNReal.ofReal (Real.pi / 4) := by
        rw [volumeQ_univ_eq_pi, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end

end MatrixTransport

namespace MatrixTransport

noncomputable section

def reactionPotential (rho : Spatial → ℝ) (Phi : ClosedC1Field) (p : Ambient) : ℝ :=
  timePotential Phi (rho p.2) p.2 p.1

def reactionPairIntegrand (rho : Spatial → ℝ) (Phi : ClosedC1Field) (p : Ambient) : ℝ :=
  timePotentialDerivative Phi (rho p.2) p.2 p.1

theorem frob_comm_mat2 (A B : Mat2) : frob A B = frob B A := by
  simp only [frob, Fin.sum_univ_two]
  ring

theorem frob_density_expand (u : ℝ) (A : Mat2) :
    frob (density u) A = Matrix.trace A + u * A 1 1 := by
  rw [frob_density_diag, Matrix.trace_fin_two]
  ring

theorem frob_flux_zero (B : Flux 1) : frob B (0 : Flux 1) = 0 := by
  simp [frob]

theorem weightedPair_reaction (rho : Spatial → ℝ) (Phi : ClosedC1Field) (q : Q) :
    weightedPair (fun _ ↦ 1) (testTriplet KBDstar Phi q) (reactionTriplet rho q)
      = reactionPairIntegrand rho Phi (q : Ambient) := by
  have h1 : frob (dtPhiQ Phi q) (density ((q : Ambient).1 * rho (q : Ambient).2))
      = Matrix.trace (dtPhi Phi (q : Ambient))
        + (q : Ambient).1 * rho (q : Ambient).2 * dtPhi Phi (q : Ambient) 1 1 :=
    (frob_comm_mat2 _ _).trans (frob_density_expand _ _)
  have h2 : frob (0 : Flux 1) (KBDstar Phi q) = 0 := by simp [frob]
  have h3 : frob (Phi.toFun (q : Ambient)) ((rho (q : Ambient).2) • E)
      = rho (q : Ambient).2 * Phi.toFun (q : Ambient) 1 1 := by
    rw [frob_comm_mat2, frob_reaction_E]
  have e : (((q : Ambient).1, (q : Ambient).2) : Ambient) = (q : Ambient) := rfl
  unfold testTriplet reactionTriplet
  rw [weightedPair_packTriplet]
  simp only [mass_packTriplet, flux_packTriplet, reaction_packTriplet]
  rw [frob_comm_mat2 (density _) (dtPhiQ Phi q),
    frob_comm_mat2 ((rho (q : Ambient).2) • E) (Phi.toFun (q : Ambient))]
  unfold reactionPairIntegrand timePotentialDerivative
  rw [e]
  linear_combination h1 + h2 + h3

theorem continuousOn_phi_entry_Q (Phi : ClosedC1Field) (i j : Fin 2) :
    ContinuousOn (fun p : Ambient ↦ Phi.toFun p i j) QSet :=
  continuousOn_pi.mp (continuousOn_pi.mp Phi.continuousOn_QSet i) j

theorem continuousOn_dtPhi_entry_Q (Phi : ClosedC1Field) (i j : Fin 2) :
    ContinuousOn (fun p : Ambient ↦ dtPhi Phi p i j) QSet := by
  have hdt' := Phi.continuousOn_fderiv_QSet.clm_apply
    (continuousOn_const (c := ((1 : ℝ), (0 : Spatial))))
  have hdt : ContinuousOn (fun p : Ambient ↦ dtPhi Phi p) QSet := hdt'
  exact continuousOn_pi.mp (continuousOn_pi.mp hdt i) j

theorem continuousOn_reactionPairIntegrand (rho : Spatial → ℝ) (hrho : Continuous rho)
    (Phi : ClosedC1Field) :
    ContinuousOn (reactionPairIntegrand rho Phi) QSet := by
  have hr : Continuous fun p : Ambient ↦ rho p.2 := hrho.comp continuous_snd
  have hf : reactionPairIntegrand rho Phi = fun p : Ambient ↦
      (dtPhi Phi p 0 0 + dtPhi Phi p 1 1) + rho p.2 * Phi.toFun p 1 1
        + p.1 * rho p.2 * dtPhi Phi p 1 1 := by
    funext p
    simp only [reactionPairIntegrand, timePotentialDerivative, Prod.mk.eta,
      Matrix.trace_fin_two]
    try ring
  rw [hf]
  have d00 := continuousOn_dtPhi_entry_Q Phi 0 0
  have d11 := continuousOn_dtPhi_entry_Q Phi 1 1
  have p11 := continuousOn_phi_entry_Q Phi 1 1
  exact ((d00.add d11).add (hr.continuousOn.mul p11)).add
    ((continuous_fst.mul hr).continuousOn.mul d11)

theorem continuousOn_reactionPotential (rho : Spatial → ℝ) (hrho : Continuous rho)
    (Phi : ClosedC1Field) :
    ContinuousOn (reactionPotential rho Phi) QSet := by
  have hr : Continuous fun p : Ambient ↦ rho p.2 := hrho.comp continuous_snd
  have hf : reactionPotential rho Phi = fun p : Ambient ↦
      (Phi.toFun p 0 0 + Phi.toFun p 1 1) + p.1 * rho p.2 * Phi.toFun p 1 1 := by
    funext p
    simp only [reactionPotential, timePotential, Prod.mk.eta, Matrix.trace_fin_two]
    try ring
  rw [hf]
  have p00 := continuousOn_phi_entry_Q Phi 0 0
  have p11 := continuousOn_phi_entry_Q Phi 1 1
  exact (p00.add p11).add ((continuous_fst.mul hr).continuousOn.mul p11)

theorem integrable_reactionPotential_slice (rho : Spatial → ℝ) (hrho : Continuous rho)
    (Phi : ClosedC1Field) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun x : Spatial ↦ reactionPotential rho Phi (t, x)) diskVolume := by
  have hc : Continuous (fun x : Spatial ↦ ((t, x) : Ambient)) :=
    continuous_const.prodMk continuous_id
  have h : ContinuousOn (fun x : Spatial ↦ reactionPotential rho Phi (t, x)) disk :=
    (continuousOn_reactionPotential rho hrho Phi).comp hc.continuousOn
      (fun x hx ↦ mem_QSet_of_Icc_disk ht hx)
  exact h.integrableOn_compact disk_isCompact

theorem integral_reactionPair (rho : Spatial → ℝ) (hrho : Continuous rho)
    (Phi : ClosedC1Field) :
    (∫ q : Q, reactionPairIntegrand rho Phi (q : Ambient) ∂volumeQ)
      = endpointDifference (fun _ : Spatial ↦ density 0) (fun x ↦ density (rho x)) Phi := by
  rw [integral_volumeQ_eq_space_time _ (continuousOn_reactionPairIntegrand rho hrho Phi)]
  have hm : ∀ᵐ x ∂diskVolume, x ∈ disk := ae_restrict_mem disk_measurableSet
  have hae : (fun x : Spatial ↦ ∫ t in Set.Icc (0 : ℝ) 1,
        reactionPairIntegrand rho Phi (t, x))
      =ᵐ[diskVolume] (fun x : Spatial ↦
        reactionPotential rho Phi (1, x) - reactionPotential rho Phi (0, x)) := by
    filter_upwards [hm] with x hx
    have h := integral_timePotentialDerivative Phi (rho x) hx
    show (∫ t in Set.Icc (0 : ℝ) 1, timePotentialDerivative Phi (rho x) x t)
      = timePotential Phi (rho x) x 1 - timePotential Phi (rho x) x 0
    rw [h]
    simp only [timePotential]
    ring
  refine (integral_congr_ae hae).trans ?_
  have i1 := integrable_reactionPotential_slice rho hrho Phi
    (Set.right_mem_Icc.2 (zero_le_one : (0 : ℝ) ≤ 1))
  have i0 := integrable_reactionPotential_slice rho hrho Phi
    (Set.left_mem_Icc.2 (zero_le_one : (0 : ℝ) ≤ 1))
  rw [integral_sub i1 i0]
  have e1 : ∀ x : Spatial, frob (density (rho x)) (Phi.toFun (1, x))
      = reactionPotential rho Phi (1, x) := by
    intro x
    rw [frob_density_expand]
    simp only [reactionPotential, timePotential]
    ring
  have e0 : ∀ x : Spatial, frob (density 0) (Phi.toFun (0, x))
      = reactionPotential rho Phi (0, x) := by
    intro x
    rw [frob_density_expand]
    simp only [reactionPotential, timePotential]
    ring
  simp only [endpointDifference, endpointPair, e1, e0]

theorem reactionPath_continuityEquation (rho : Spatial → ℝ) (hrho : Continuous rho) :
    ContinuityEquation KBDstar (fun _ : Spatial ↦ density 0) (fun x ↦ density (rho x))
      (reactionPath rho) := by
  refine (continuityEquation_iff_integral_of_density KBDstar
    (fun _ : Spatial ↦ density 0) (fun x ↦ density (rho x)) (reactionPath rho)
    (fun c q ↦ reactionTriplet rho q c)
    (fun c ↦ measurable_reactionTriplet_coord rho hrho c)
    (fun c ↦ integrable_reactionTriplet_coord rho hrho c)
    (fun c ↦ rfl)
    (fun Phi ↦ continuous_KBstar Phi)).mpr ?_
  intro Phi
  refine Eq.trans ?_ (integral_reactionPair rho hrho Phi)
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun q ↦ weightedPair_reaction rho Phi q)

theorem kbSquared_le_pi_quarter (rho : Spatial → ℝ) (hrho : Continuous rho)
    (hb : ∀ x : Spatial, |rho x| ≤ (1 / 2 : ℝ)) :
    wbSquared KBDstar (fun _ : Spatial ↦ density 0) (fun x ↦ density (rho x))
      ≤ ENNReal.ofReal (Real.pi / 4) :=
  (wbSquared_le_action KBDstar _ _ (reactionPath rho)
    (reactionPath_continuityEquation rho hrho)).trans (reactionPath_action_le rho hrho hb)

theorem kbSquared_lt_top_of_endpointBound (rho : Spatial → ℝ) (hrho : Continuous rho)
    (hb : ∀ x : Spatial, |rho x| ≤ (1 / 2 : ℝ)) :
    wbSquared KBDstar (fun _ : Spatial ↦ density 0) (fun x ↦ density (rho x)) < ⊤ :=
  lt_of_le_of_lt (kbSquared_le_pi_quarter rho hrho hb) ENNReal.ofReal_lt_top

end

end MatrixTransport
