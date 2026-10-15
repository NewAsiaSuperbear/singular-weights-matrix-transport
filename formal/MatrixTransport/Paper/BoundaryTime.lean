import MatrixTransport.EntrywiseBures.LagrangianPiece

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.Boundary
open MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures
variable {d n : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

/-- Time insertion into the closed cylinder. -/
def timeInsert (s : UnitI) (x : ↥Ω) : Q Ω := ⟨(s.val, x.val), s.property, x.property⟩

theorem continuous_timeInsert : Continuous (fun p : UnitI × ↥Ω ↦ timeInsert p.1 p.2) :=
  ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def timeResidual (φ : ClosedC1Jet Ω n) (i j : Fin n) (x : ↥Ω) : ℝ :=
  (∫ s, φ.dt (timeInsert s x) i j ∂unitTime) -
    φ.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ x) i j +
    φ.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ x) i j

theorem continuous_timeResidual (φ : ClosedC1Jet Ω n) (i j : Fin n) :
    Continuous (timeResidual φ i j) := by
  have hc : Continuous (fun p : ↥Ω × UnitI ↦ φ.dt (timeInsert p.2 p.1) i j) := by
    have hm := (continuous_timeInsert (Ω := Ω)).comp continuous_swap
    exact (continuous_apply j).comp ((continuous_apply i).comp (φ.dt.continuous.comp hm))
  have hint : Continuous (fun x : ↥Ω ↦ ∫ s, φ.dt (timeInsert s x) i j ∂unitTime) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous (μ := unitTime)
        (f := fun x : ↥Ω ↦ fun s : UnitI ↦ φ.dt (timeInsert s x) i j) hc
        (isCompact_univ : IsCompact (univ : Set UnitI)))
  unfold timeResidual
  exact (hint.sub ((continuous_apply j).comp ((continuous_apply i).comp
    (φ.value.continuous.comp (timeBoundary 1 ⟨zero_le_one, le_rfl⟩).continuous)))).add
    ((continuous_apply j).comp ((continuous_apply i).comp
      (φ.value.continuous.comp (timeBoundary 0 ⟨le_rfl, zero_le_one⟩).continuous)))

theorem timeResidual_zero_of_interior (φ : ClosedC1Jet Ω n) (i j : Fin n)
    (x : ↥Ω) (hx : x.val ∈ interior Ω) : timeResidual φ i j x = 0 := by
  let f : ℝ → ℝ := fun s ↦ zeroExtend φ.value (s, x.val) i j
  let f' : ℝ → ℝ := fun s ↦ zeroExtend φ.dt (s, x.val) i j
  have hv : ∀ s : UnitI, f s.val = φ.value (timeInsert s x) i j := by
    intro s
    dsimp [f, timeInsert]
    rw [zeroExtend_of_mem φ.value ⟨s.property, x.property⟩]
  have ht : ∀ s : UnitI, f' s.val = φ.dt (timeInsert s x) i j := by
    intro s
    dsimp [f', timeInsert]
    rw [zeroExtend_of_mem φ.dt ⟨s.property, x.property⟩]
  have hfc : ContinuousOn f (Icc 0 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h : Continuous (fun s : UnitI ↦ φ.value (timeInsert s x) i j) := by
      have hm : Continuous (fun s : UnitI ↦ timeInsert s x) :=
        continuous_timeInsert.comp (continuous_id.prodMk continuous_const)
      exact (continuous_apply j).comp ((continuous_apply i).comp (φ.value.continuous.comp hm))
    exact h.congr (fun s ↦ (hv s).symm)
  have htc : ContinuousOn f' (Icc 0 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h : Continuous (fun s : UnitI ↦ φ.dt (timeInsert s x) i j) := by
      have hm : Continuous (fun s : UnitI ↦ timeInsert s x) :=
        continuous_timeInsert.comp (continuous_id.prodMk continuous_const)
      exact (continuous_apply j).comp ((continuous_apply i).comp (φ.dt.continuous.comp hm))
    exact h.congr (fun s ↦ (ht s).symm)
  have hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' s) s := by
    intro s hs
    let p : Q Ω := ⟨(s, x.val), Ioo_subset_Icc_self hs, x.property⟩
    have hp : p.val ∈ interior (domain Ω) := by
      rw [interior_domain_eq]
      exact ⟨hs, hx⟩
    have h0 := φ.time_deriv p hp
    have h1 : HasDerivAt (fun u : ℝ ↦ u - s) 1 s :=
      (hasDerivAt_id s).sub_const s
    have h2 : HasDerivAt (fun u : ℝ ↦ zeroExtend φ.value (timeLine p.val u) i j)
        (φ.dt p i j) (s - s) := by
      simpa only [sub_self] using hasDerivAt_entry h0 i j
    have h3 := h2.comp (h := fun u : ℝ ↦ u - s) s h1
    have h4 : HasDerivAt (fun u : ℝ ↦ zeroExtend φ.value (u, x.val) i j)
        (φ.dt p i j) s := by
      convert h3 using 1 <;> try rfl
      all_goals try simp only [mul_one]
      funext u
      congr 1
      simp [Function.comp_def, timeLine, p]
    have he : zeroExtend φ.dt (s, x.val) = φ.dt p := zeroExtend_val φ.dt p
    simpa only [f, f', he] using h4
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hfc hd
    (htc.intervalIntegrable_of_Icc zero_le_one)
  have hI : (∫ s, φ.dt (timeInsert s x) i j ∂unitTime) = f 1 - f 0 := by
    calc
      (∫ s, φ.dt (timeInsert s x) i j ∂unitTime) = ∫ s, f' s.val ∂unitTime :=
        integral_congr_ae (ae_of_all _ fun s ↦ (ht s).symm)
      _ = ∫ s in (0 : ℝ)..1, f' s := integral_unitTime f'
      _ = f 1 - f 0 := hi
  unfold timeResidual
  rw [hI, hv ⟨1, ⟨zero_le_one, le_rfl⟩⟩, hv ⟨0, ⟨le_rfl, zero_le_one⟩⟩]
  change _ - _ - _ + _ = (0 : ℝ)
  simp only [timeInsert, timeBoundary, ContinuousMap.coe_mk]
  ring

theorem regSeq_le_one (j : ℕ) : regSeq j ≤ 1 := by
  unfold regSeq
  apply (div_le_one (by positivity : 0 < (j : ℝ) + 1)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) j]

/-- Interior approximation along the existing hub contraction. -/
def spatialApprox (G : HubGeometry d Ω) (x : ↥Ω) (j : ℕ) : ↥Ω :=
  ⟨(1 - regSeq j) • x.val + regSeq j • G.hub,
    G.convex x.property (interior_subset G.hub_mem)
      (sub_nonneg.mpr (regSeq_le_one j)) (regSeq_pos j).le (by ring)⟩

theorem spatialApprox_interior (G : HubGeometry d Ω) (x : ↥Ω) (j : ℕ) :
    (spatialApprox G x j).val ∈ interior Ω := by
  have h := G.convex.combo_interior_self_mem_interior G.hub_mem x.property
    (regSeq_pos j) (sub_nonneg.mpr (regSeq_le_one j)) (by ring)
  simpa only [spatialApprox, add_comm] using h

theorem tendsto_spatialApprox (G : HubGeometry d Ω) (x : ↥Ω) :
    Tendsto (spatialApprox G x) atTop (𝓝 x) := by
  apply tendsto_subtype_rng.mpr
  have hc : Tendsto (fun j ↦ (1 : ℝ) - regSeq j) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_regSeq
  have h := (hc.smul_const x.val).add
    (tendsto_regSeq.smul_const G.hub)
  simpa only [spatialApprox, sub_zero, one_smul, zero_smul, add_zero] using h

/-- The time FTC also holds at boundary points for the native test convention. -/
theorem timeResidual_zero (G : HubGeometry d Ω) (φ : ClosedC1Jet Ω n)
    (i j : Fin n) (x : ↥Ω) : timeResidual φ i j x = 0 := by
  have ht := ((continuous_timeResidual φ i j).tendsto x).comp (tendsto_spatialApprox G x)
  have he : (fun k ↦ timeResidual φ i j (spatialApprox G x k)) = fun _ ↦ (0 : ℝ) :=
    funext fun k ↦ timeResidual_zero_of_interior φ i j _ (spatialApprox_interior G x k)
  change Tendsto (fun k ↦ timeResidual φ i j (spatialApprox G x k)) atTop
    (𝓝 (timeResidual φ i j x)) at ht
  rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

#print axioms continuous_timeResidual
#print axioms timeResidual_zero_of_interior
#print axioms timeResidual_zero
end LiZouTransport.Boundary
