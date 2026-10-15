import MatrixTransport.Paper.NativeSeparationSharp

/-! # The square-root reaction competitor on the disk

The spatially varying square-root interpolation is tested against the full native
closed-domain C¹ class. Its action is computed from the original local support function.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.NativeSeparation
open MatrixTransport MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures

/-- Increment of the scalar square-root factor. -/
def sqrtIncrement (ρ : Spatial → ℝ) (x : Spatial) : ℝ := Real.sqrt (1 + ρ x) - 1

/-- The positive factor whose square is the moving second diagonal entry. -/
def sqrtFactor (ρ : Spatial → ℝ) (t : ℝ) (x : Spatial) : ℝ := 1 + t * sqrtIncrement ρ x

def sqrtReactionTriplet (ρ : Spatial → ℝ) (q : MatrixTransport.Q) : TransportCoord 1 → ℝ :=
  packTriplet (MatrixTransport.density (sqrtFactor ρ q.val.1 q.val.2 ^ 2 - 1))
    (0 : Flux 1) ((2 * sqrtFactor ρ q.val.1 q.val.2 * sqrtIncrement ρ q.val.2) • E)

def sqrtReactionPath (ρ : Spatial → ℝ) : MatrixPath 1 where
  coords := fun c ↦ volumeQ.withDensityᵥ (fun q ↦ sqrtReactionTriplet ρ q c)
  massSymmetry := by
    intro i j
    congr 1
    funext q
    change MatrixTransport.density _ i j = MatrixTransport.density _ j i
    rw [MatrixTransport.density_apply, MatrixTransport.density_apply]
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]

theorem continuous_sqrtIncrement (ρ : Spatial → ℝ) (hρ : Continuous ρ) :
    Continuous (sqrtIncrement ρ) :=
  (Real.continuous_sqrt.comp (continuous_const.add hρ)).sub continuous_const

theorem continuous_sqrtReactionTriplet (ρ : Spatial → ℝ) (hρ : Continuous ρ) :
    Continuous (sqrtReactionTriplet ρ) := by
  have ht : Continuous (fun q : MatrixTransport.Q ↦ q.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hx : Continuous (fun q : MatrixTransport.Q ↦ q.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hd := (continuous_sqrtIncrement ρ hρ).comp hx
  have hp : Continuous (fun q : MatrixTransport.Q ↦ sqrtFactor ρ q.val.1 q.val.2) :=
    continuous_const.add (ht.mul hd)
  apply continuous_pi
  intro c
  rcases c with ⟨i,j⟩ | ⟨i,j⟩ | ⟨i,j⟩
  · change Continuous (fun q : MatrixTransport.Q ↦ MatrixTransport.density _ i j)
    simp only [MatrixTransport.density_apply]
    split_ifs <;> first
    | exact continuous_const
    | exact continuous_const.add ((hp.pow 2).sub continuous_const)
  · exact continuous_const
  · change Continuous (fun q : MatrixTransport.Q ↦ (2 * sqrtFactor ρ q.val.1 q.val.2 *
        sqrtIncrement ρ q.val.2) * E i j)
    exact ((continuous_const.mul hp).mul hd).mul continuous_const

theorem sqrtFactor_positive (ρ : Spatial → ℝ)
    (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (x : Spatial) : 0 < sqrtFactor ρ t x := by
  have hr : 0 < 1 + ρ x := by have h := (abs_le.mp (hb x)).1; linarith
  have hs := Real.sqrt_pos.2 hr
  unfold sqrtFactor sqrtIncrement
  have h := mul_nonneg (sub_nonneg.2 ht.2) (zero_le_one : (0 : ℝ) ≤ 1)
  have hprod := mul_nonneg ht.1 (le_of_lt hs)
  by_cases hlt : t < 1
  · have hleft : 0 < 1 - t := by linarith
    nlinarith
  · have he : t = 1 := by linarith [ht.2]
    rw [he]
    simpa using hs

/-- Exact local cost of the second-coordinate square-root factor. -/
theorem matrixCost_sqrt_reaction (p δ : ℝ) (hp : 0 < p) :
    matrixCost 1 (packTriplet (MatrixTransport.density (p ^ 2 - 1))
      (0 : Flux 1) ((2 * p * δ) • E)) = ENNReal.ofReal (2 * δ ^ 2) := by
  apply le_antisymm
  · unfold matrixCost supportFunction
    refine iSup_le fun a ↦ iSup_le fun ha ↦ ENNReal.ofReal_le_ofReal ?_
    rw [weightedPair_packTriplet, frob_density_diag, frob_reaction_E]
    have hz : frob (0 : Flux 1) (flux a) = 0 := by simp [frob]
    rw [hz]
    have h0 := local_diag_bound (mass a) (flux a) (reaction a) ha.2 0
    have h1 := local_diag_bound (mass a) (flux a) (reaction a) ha.2 1
    have hb0 : 0 ≤ ∑ j, flux a 0 j * flux a 0 j := Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
    have hb1 : 0 ≤ ∑ j, flux a 1 j * flux a 1 j := Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
    have hc0 : 0 ≤ ∑ j, reaction a 0 j * reaction a 0 j :=
      Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
    have hc1 : reaction a 1 1 ^ 2 ≤ ∑ j, reaction a 1 j * reaction a 1 j := by
      simpa only [pow_two] using Finset.single_le_sum
        (f := fun j ↦ reaction a 1 j * reaction a 1 j)
        (fun _ _ ↦ mul_self_nonneg _) (Finset.mem_univ (1 : Fin 2))
    have hA : mass a 0 0 ≤ 0 := by linarith
    have hB : mass a 1 1 + (reaction a 1 1) ^ 2 / 2 ≤ 0 := by linarith
    have hmul := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg p) hB
    nlinarith [sq_nonneg (p * reaction a 1 1 - 2 * δ)]
  · let c := 2 * δ / p
    let a : TransportCoord 1 → ℝ := packTriplet ((-(c ^ 2 / 2)) • E)
      (0 : Flux 1) (c • E)
    have ha : a ∈ dualSet 1 := by
      constructor
      · rw [mass_packTriplet]
        exact (show E.IsHermitian by simpa [Matrix.IsHermitian] using E_transpose).smul
          (by simp [IsSelfAdjoint])
      · simp only [a, mass_packTriplet, flux_packTriplet, reaction_packTriplet]
        exact local_cert_aux (c ^ 2 / 2) c (by nlinarith)
    have h := matrixCost_fenchel_packTriplet 1 (MatrixTransport.density (p ^ 2 - 1))
      (0 : Flux 1) ((2 * p * δ) • E) a ha
    have he : frob (MatrixTransport.density (p ^ 2 - 1)) (mass a) +
        frob (0 : Flux 1) (flux a) + frob ((2 * p * δ) • E) (reaction a) = 2 * δ ^ 2 := by
      simp only [a, mass_packTriplet, flux_packTriplet, reaction_packTriplet,
        frob_density_diag, frob_reaction_E, Matrix.smul_apply, smul_eq_mul,
        E_zero_zero, E_one_one]
      simp only [frob, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      dsimp [c]
      field_simp
      ring
    rw [he] at h
    exact h

/-- The native time integrand for the nonlinear reaction curve. -/
def nativeSqrtIntegrand (ρ : Spatial → ℝ) (φ : ClosedC1Jet disk 2)
    (p : MatrixTransport.Ambient) : ℝ :=
  zeroExtend φ.dt p 0 0 + sqrtFactor ρ p.1 p.2 ^ 2 * zeroExtend φ.dt p 1 1 +
    2 * sqrtFactor ρ p.1 p.2 * sqrtIncrement ρ p.2 * zeroExtend φ.value p 1 1

theorem continuousOn_nativeSqrtIntegrand (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (φ : ClosedC1Jet disk 2) : ContinuousOn (nativeSqrtIntegrand ρ φ) QSet := by
  have hd (i j : Fin 2) : ContinuousOn (fun p ↦ zeroExtend φ.dt p i j) QSet :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_zeroExtend φ.dt) i) j
  have hv : ContinuousOn (fun p ↦ zeroExtend φ.value p 1 1) QSet :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_zeroExtend φ.value) 1) 1
  have hδ : ContinuousOn (fun p : MatrixTransport.Ambient ↦ sqrtIncrement ρ p.2) QSet :=
    ((continuous_sqrtIncrement ρ hρ).comp continuous_snd).continuousOn
  have hp : ContinuousOn (fun p : MatrixTransport.Ambient ↦ sqrtFactor ρ p.1 p.2) QSet :=
    continuousOn_const.add (continuous_fst.continuousOn.mul hδ)
  exact ((hd 0 0).add ((hp.pow 2).mul (hd 1 1))).add
    (((continuousOn_const.mul hp).mul hδ).mul hv)

/-- The mass density is literally the manuscript's diagonal square-root formula. -/
theorem sqrtMass_eq (ρ : Spatial → ℝ) (t : ℝ) (x : Spatial) :
    MatrixTransport.density (sqrtFactor ρ t x ^ 2 - 1) =
      Matrix.diagonal (fun i : Fin 2 ↦ if i = 1 then
        (1 + t * (Real.sqrt (1 + ρ x) - 1)) ^ 2 else 1) := by
  ext i j
  simp [MatrixTransport.density,Matrix.diagonal_apply,sqrtFactor,sqrtIncrement]

/-- The reaction density is the time derivative of the moving diagonal entry. -/
theorem sqrtFactor_squared_deriv (ρ : Spatial → ℝ) (x : Spatial) (t : ℝ) :
    HasDerivAt (fun s ↦ sqrtFactor ρ s x ^ 2)
      (2 * sqrtFactor ρ t x * sqrtIncrement ρ x) t := by
  have h := ((hasDerivAt_id t).mul_const (sqrtIncrement ρ x)).const_add 1
  have hd := h.mul h
  have he : (1 * sqrtIncrement ρ x) * (1 + id t * sqrtIncrement ρ x) +
      (1 + id t * sqrtIncrement ρ x) * (1 * sqrtIncrement ρ x) =
      2 * sqrtFactor ρ t x * sqrtIncrement ρ x := by
    dsimp [sqrtFactor,id]
    ring
  rw [he] at hd
  simpa only [sqrtFactor,id_eq,pow_two] using! hd

/-- The literal matrix reaction density is the derivative of the literal mass density. -/
theorem sqrtMass_deriv (ρ : Spatial → ℝ) (x : Spatial) (t : ℝ) :
    HasDerivAt (fun s ↦ MatrixTransport.density (sqrtFactor ρ s x ^ 2 - 1))
      ((2 * sqrtFactor ρ t x * sqrtIncrement ρ x) • E) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [MatrixTransport.density,E,Matrix.diagonal_apply] using hasDerivAt_const t (1 : ℝ)
  · simpa [MatrixTransport.density,E,Matrix.diagonal_apply] using hasDerivAt_const t (0 : ℝ)
  · simpa [MatrixTransport.density,E,Matrix.diagonal_apply] using hasDerivAt_const t (0 : ℝ)
  · simpa [MatrixTransport.density,E,Matrix.diagonal_apply] using sqrtFactor_squared_deriv ρ x t

/-- The constructed signed Radon flux is exactly zero. -/
theorem sqrtReactionPath_flux_zero (ρ : Spatial → ℝ) (i : Fin 2) (j : Fin 1) :
    (sqrtReactionPath ρ).coords (Sum.inr (Sum.inl (i,j))) = 0 := by
  change volumeQ.withDensityᵥ (0 : MatrixTransport.Q → ℝ) = 0
  exact withDensityᵥ_zero

/-- Time FTC for each spatially varying square-root factor, including boundary points. -/
theorem integral_nativeSqrtIntegrand (ρ : Spatial → ℝ)
    (hρpos : ∀ x, 0 ≤ 1 + ρ x) (φ : ClosedC1Jet disk 2)
    {x : Spatial} (hx : x ∈ disk) :
    (∫ s in Icc (0 : ℝ) 1, nativeSqrtIntegrand ρ φ (s,x)) =
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
  let f : ℝ → ℝ := fun s ↦ sqrtFactor ρ s x ^ 2
  let f' : ℝ → ℝ := fun s ↦ 2 * sqrtFactor ρ s x * sqrtIncrement ρ x
  have hf : Continuous f := (continuous_const.add (continuous_id.mul continuous_const)).pow 2
  have hf' : Continuous f' :=
    (continuous_const.mul (continuous_const.add (continuous_id.mul continuous_const))).mul
      continuous_const
  have hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' t) t :=
    fun t _ ↦ sqrtFactor_squared_deriv ρ x t
  have h1 := weighted_time_FTC diskHub φ f f' hf.continuousOn hf'.continuousOn hder 1 1 x'
  have h0 := weighted_time_FTC diskHub φ (fun _ ↦ 1) (fun _ ↦ 0)
    continuousOn_const continuousOn_const (fun t _ ↦ hasDerivAt_const t 1) 0 0 x'
  simp only [zero_mul, one_mul, zero_add] at h0
  have hip : Integrable (fun s : UnitI ↦ f' s.val * φ.value (ins s) 1 1 +
      f s.val * φ.dt (ins s) 1 1) unitTime :=
    ((((hf'.comp continuous_subtype_val).mul (hc φ.value 1 1)).add
      ((hf.comp continuous_subtype_val).mul (hc φ.dt 1 1)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_unitTime_Icc]
  have he : (fun s : UnitI ↦ nativeSqrtIntegrand ρ φ (s.val,x)) =
      fun s ↦ φ.dt (ins s) 0 0 +
        (f' s.val * φ.value (ins s) 1 1 + f s.val * φ.dt (ins s) 1 1) := by
    funext s
    unfold nativeSqrtIntegrand
    rw [zeroExtend_of_mem φ.dt (q := (s.val,x)) ⟨s.property,hx⟩,
      zeroExtend_of_mem φ.value (q := (s.val,x)) ⟨s.property,hx⟩]
    dsimp [f,f',ins,x',LiZouTransport.Boundary.timeInsert]
    ring
  rw [he, integral_add (hi φ.dt 0 0) hip, h0, h1]
  have hf1 : f 1 = 1 + ρ x := by
    dsimp [f,sqrtFactor,sqrtIncrement]
    simpa only [one_mul, add_sub_cancel] using Real.sq_sqrt (hρpos x)
  have hf0 : f 0 = 1 := by simp [f,sqrtFactor]
  rw [hf1,hf0]
  rw [frob_density_diag, frob_density_diag]
  erw [zeroExtend_of_mem φ.value (q := ((1 : ℝ),x)) ⟨⟨zero_le_one,le_rfl⟩,hx⟩,
    zeroExtend_of_mem φ.value (q := ((0 : ℝ),x)) ⟨⟨le_rfl,zero_le_one⟩,hx⟩]
  simp only [x',timeBoundary,ContinuousMap.coe_mk,one_mul]
  ring

/-- Cylinder integration of the full nonlinear native continuity identity. -/
theorem integral_nativeSqrt_eq_endpoint (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 ≤ 1 + ρ x) (φ : ClosedC1Jet disk 2) :
    (∫ q : MatrixTransport.Q, nativeSqrtIntegrand ρ φ q.val ∂volumeQ) =
      nativeEndpointPair (fun x ↦ MatrixTransport.density (ρ x)) φ 1 -
        nativeEndpointPair (fun _ ↦ MatrixTransport.density 0) φ 0 := by
  rw [integral_volumeQ_eq_space_time _ (continuousOn_nativeSqrtIntegrand ρ hρ φ)]
  have he : ∀ᵐ x ∂diskVolume,
      (∫ t in Icc (0 : ℝ) 1, nativeSqrtIntegrand ρ φ (t,x)) =
      frob (MatrixTransport.density (ρ x)) (zeroExtend φ.value (1,x)) -
        frob (MatrixTransport.density 0) (zeroExtend φ.value (0,x)) := by
    filter_upwards [ae_restrict_mem disk_measurableSet] with x hx
    exact integral_nativeSqrtIntegrand ρ hρpos φ hx
  rw [integral_congr_ae he]
  exact integral_sub
    (integrable_nativeEndpoint _ (continuous_density_comp ρ hρ) φ ⟨zero_le_one,le_rfl⟩)
    (integrable_nativeEndpoint _ continuous_const φ ⟨le_rfl,zero_le_one⟩)

/-- The exact displayed square-root curve satisfies every original closed-domain C¹ test. -/
theorem sqrtReactionPath_nativeCE (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 ≤ 1 + ρ x) :
    PaperContinuityEquation LiZouTransport.Examples.kbOp
      (densityEndpoint (fun _ ↦ MatrixTransport.density 0))
      (densityEndpoint (fun x ↦ MatrixTransport.density (ρ x)))
      (sqrtReactionPath ρ).coords := by
  have hc := continuous_sqrtReactionTriplet ρ hρ
  have hm : ∀ c, Measurable (fun q ↦ sqrtReactionTriplet ρ q c) :=
    fun c ↦ ((continuous_apply c).comp hc).measurable
  have hi : ∀ c, Integrable (fun q ↦ sqrtReactionTriplet ρ q c) volumeQ :=
    fun c ↦ ((continuous_apply c).comp hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply nativeCE_of_density_integral LiZouTransport.Examples.kbOp _ _ continuous_const
    (continuous_density_comp ρ hρ) (sqrtReactionPath ρ) _ hm hi (fun _ ↦ rfl)
  intro φ
  rw [← integral_nativeSqrt_eq_endpoint ρ hρ hρpos φ]
  apply integral_congr_ae
  apply ae_of_all
  intro q
  have hp : testField LiZouTransport.Examples.kbOp φ q =
      packTriplet (φ.dt q) (LiZouTransport.Examples.kbOp.apply φ q) (φ.value q) := by
    funext c
    rcases c with ⟨i,j⟩ | ⟨i,j⟩ | ⟨i,j⟩ <;> rfl
  dsimp only
  erw [hp]
  unfold sqrtReactionTriplet
  rw [weightedPair_packTriplet]
  simp only [mass_packTriplet, flux_packTriplet, reaction_packTriplet,
    frob_density_diag, frob_reaction_E]
  have hz : frob (0 : Flux 1) (LiZouTransport.Examples.kbOp.apply φ q) = 0 := by simp [frob]
  rw [hz]
  unfold nativeSqrtIntegrand
  erw [zeroExtend_val φ.dt q,zeroExtend_val φ.value q]
  ring


/-- The mass matrix of the displayed competitor is positive semidefinite at each point. -/
theorem sqrtReaction_mass_posSemidef (ρ : Spatial → ℝ) (q : MatrixTransport.Q) :
    (mass (sqrtReactionTriplet ρ q)).PosSemidef := by
  rw [sqrtReactionTriplet, mass_packTriplet]
  convert psd_diag2 1 (sqrtFactor ρ q.val.1 q.val.2 ^ 2) zero_le_one (sq_nonneg _) using 1
  ext i j
  simp [MatrixTransport.density,Matrix.diagonal_apply]

/-- Reference independence computes the action from the constructed continuous densities. -/
theorem sqrtReactionPath_action_eq_density (ρ : Spatial → ℝ) (hρ : Continuous ρ) :
    matrixAction 1 (sqrtReactionPath ρ).coords =
      ∫⁻ q : MatrixTransport.Q, matrixCost 1 (sqrtReactionTriplet ρ q) ∂volumeQ := by
  have hc := continuous_sqrtReactionTriplet ρ hρ
  have hm : ∀ c, Measurable (fun q ↦ sqrtReactionTriplet ρ q c) :=
    fun c ↦ ((continuous_apply c).comp hc).measurable
  have hi : ∀ c, Integrable (fun q ↦ sqrtReactionTriplet ρ q c) volumeQ :=
    fun c ↦ ((continuous_apply c).comp hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hw : ∀ q : MatrixTransport.Q, 1 ≤ coordinateWeight
      (fun c q ↦ sqrtReactionTriplet ρ q c) q := by
    intro q
    have h := abs_le_coordinateWeight (fun c q ↦ sqrtReactionTriplet ρ q c)
      (Sum.inl ((0 : Fin 2),(0 : Fin 2))) q
    simpa only [sqrtReactionTriplet,packTriplet,MatrixTransport.density_zero_zero,abs_one] using h
  exact lintegral_canonicalDensity_withDensity (ν := volumeQ)
    (fun c q ↦ sqrtReactionTriplet ρ q c) hm hi hw (matrixCost 1)
    (measurable_matrixCost 1) (fun t ht v ↦ matrixCost_smul_nonneg 1 v ht)

/-- The constructed square-root competitor has exactly the displayed spatial reaction cost. -/
theorem sqrtReactionPath_action_eq (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ)) :
    matrixAction 1 (sqrtReactionPath ρ).coords =
      ENNReal.ofReal (2 * ∫ x, (Real.sqrt (1 + ρ x) - 1) ^ 2 ∂diskVolume) := by
  rw [sqrtReactionPath_action_eq_density ρ hρ]
  have he : ∀ q : MatrixTransport.Q,
      matrixCost 1 (sqrtReactionTriplet ρ q) =
        ENNReal.ofReal (2 * sqrtIncrement ρ q.val.2 ^ 2) := by
    intro q
    exact matrixCost_sqrt_reaction _ _ (sqrtFactor_positive ρ hb _ q.property.1 _)
  simp_rw [he]
  rw [MatrixTransport.lintegral_volumeQ_time_indep
    (fun x ↦ 2 * sqrtIncrement ρ x ^ 2)
    (continuous_const.mul ((continuous_sqrtIncrement ρ hρ).pow 2)).continuousOn
    (fun _ ↦ mul_nonneg (by norm_num) (sq_nonneg _)),integral_const_mul]
  rfl

/-- A scalar bound sufficient for the retained uniform disk estimate. -/
theorem sqrtIncrement_cost_le_quarter (u : ℝ) (hu : |u| ≤ (1 / 2 : ℝ)) :
    2 * (Real.sqrt (1 + u) - 1) ^ 2 ≤ 1 / 4 := by
  have hh := abs_le.mp hu
  have hs := Real.sqrt_nonneg (1 + u)
  have he := Real.sq_sqrt (show 0 ≤ 1 + u by linarith)
  have hlo : (1 / 2 : ℝ) ≤ Real.sqrt (1 + u) := by nlinarith
  have hup : Real.sqrt (1 + u) ≤ (3 / 2 : ℝ) := by nlinarith
  have hprod : (Real.sqrt (1 + u) - 1) * (Real.sqrt (1 + u) + 1) = u := by nlinarith
  have ha : |Real.sqrt (1 + u) - 1| ≤ (1 / 3 : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith
  have hsq : (Real.sqrt (1 + u) - 1) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    nlinarith [sq_abs (Real.sqrt (1 + u) - 1),abs_nonneg (Real.sqrt (1 + u) - 1)]
  nlinarith

/-- The exact nonlinear path retains the original pi/4 upper bound. -/
theorem sqrtReactionPath_action_le (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ)) :
    matrixAction 1 (sqrtReactionPath ρ).coords ≤ ENNReal.ofReal (Real.pi / 4) := by
  rw [sqrtReactionPath_action_eq_density ρ hρ]
  calc
    (∫⁻ q : MatrixTransport.Q, matrixCost 1 (sqrtReactionTriplet ρ q) ∂volumeQ) ≤
        ∫⁻ _q : MatrixTransport.Q, ENNReal.ofReal (1 / 4 : ℝ) ∂volumeQ := by
      apply lintegral_mono
      intro q
      dsimp only
      rw [show matrixCost 1 (sqrtReactionTriplet ρ q) =
          ENNReal.ofReal (2 * sqrtIncrement ρ q.val.2 ^ 2) from
        matrixCost_sqrt_reaction _ _ (sqrtFactor_positive ρ hb _ q.property.1 _)]
      exact ENNReal.ofReal_le_ofReal (sqrtIncrement_cost_le_quarter _ (hb q.val.2))
    _ = ENNReal.ofReal (Real.pi / 4) := by
      rw [lintegral_const,volumeQ_univ_eq_pi,← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

/-- Native admissibility and the exact action of the original nonlinear competitor. -/
theorem sqrtReactionPath_good_action (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ)) :
    MatrixTransport.ReactionZero.Limit.Good
        (smoothProblem LiZouTransport.Examples.kbOp ρ hρ hb) (sqrtReactionPath ρ).coords ∧
    MatrixTransport.ReactionZero.action (1 : Matrix (Fin 1) (Fin 1) ℝ) 1
        (sqrtReactionPath ρ).coords =
      ENNReal.ofReal (2 * ∫ x, (Real.sqrt (1 + ρ x) - 1) ^ 2 ∂diskVolume) := by
  constructor
  · exact ⟨(sqrtReactionPath ρ).massSymmetry,
      sqrtReactionPath_nativeCE ρ hρ (fun x ↦ by have h := (abs_le.mp (hb x)).1; linarith)⟩
  · rw [action_identity]
    exact sqrtReactionPath_action_eq ρ hρ hb

/-- The retained KB upper estimate is obtained from this exact nonlinear native path. -/
theorem kb_native_upper_sqrt (ρ : Spatial → ℝ) (hρ : Continuous ρ)
    (hb : ∀ x, |ρ x| ≤ (1 / 2 : ℝ)) :
    smoothValue LiZouTransport.Examples.kbOp ρ hρ hb ≤ ENNReal.ofReal (Real.pi / 4) := by
  have hg := (sqrtReactionPath_good_action ρ hρ hb).1
  have hmin : smoothValue LiZouTransport.Examples.kbOp ρ hρ hb ≤
      MatrixTransport.ReactionZero.action (1 : Matrix (Fin 1) (Fin 1) ℝ) 1
        (sqrtReactionPath ρ).coords := iInf_le_of_le _ (iInf_le_of_le hg le_rfl)
  rw [action_identity] at hmin
  exact hmin.trans (sqrtReactionPath_action_le ρ hρ hb)

#print axioms sqrtMass_eq
#print axioms sqrtFactor_squared_deriv
#print axioms sqrtMass_deriv
#print axioms sqrtReactionPath_flux_zero
#print axioms matrixCost_sqrt_reaction
#print axioms sqrtReactionPath_nativeCE
#print axioms sqrtReactionPath_action_eq
#print axioms sqrtReactionPath_action_le
#print axioms kb_native_upper_sqrt
#print axioms sqrtReactionPath_good_action
end LiZouTransport.NativeSeparation
