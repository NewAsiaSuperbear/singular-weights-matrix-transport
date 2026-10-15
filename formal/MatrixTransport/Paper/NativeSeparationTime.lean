import MatrixTransport.Paper.NativeSeparation
import MatrixTransport.Paper.BoundaryTime

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.NativeSeparation
open MatrixTransport MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures

variable {d n : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

/-- Scalar time weighting preserves the native jet convention. -/
def timeWeightedJet (φ : ClosedC1Jet Ω n) (f f' : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf' : ContinuousOn f' (Icc (0 : ℝ) 1))
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' t) t) : ClosedC1Jet Ω n := by
  let F : C(Q Ω, ℝ) := ⟨fun p ↦ f p.val.1, by
    exact hf.comp_continuous (continuous_fst.comp continuous_subtype_val)
      (fun p ↦ p.property.1)⟩
  let F' : C(Q Ω, ℝ) := ⟨fun p ↦ f' p.val.1, by
    exact hf'.comp_continuous (continuous_fst.comp continuous_subtype_val)
      (fun p ↦ p.property.1)⟩
  let v : C(Q Ω, Mat n) := ⟨fun p ↦ F p • φ.value p, F.continuous.smul φ.value.continuous⟩
  let t : C(Q Ω, Mat n) := ⟨fun p ↦ F' p • φ.value p + F p • φ.dt p,
    (F'.continuous.smul φ.value.continuous).add (F.continuous.smul φ.dt.continuous)⟩
  let x : Fin d → C(Q Ω, Mat n) := fun j ↦
    ⟨fun p ↦ F p • φ.dx j p, F.continuous.smul (φ.dx j).continuous⟩
  refine ClosedC1Jet.ofAmbient (fun p ↦ f p.1 • zeroExtend φ.value p) v t x ?_ ?_ ?_ ?_ ?_ ?_
  · intro p; dsimp [v, F]; rw [zeroExtend_val]
  · intro p; exact (φ.value_symmetric p).smul (by simp [IsSelfAdjoint])
  · intro p; exact ((φ.value_symmetric p).smul (by simp [IsSelfAdjoint])).add
      ((φ.dt_symmetric p).smul (by simp [IsSelfAdjoint]))
  · intro j p; exact (φ.dx_symmetric j p).smul (by simp [IsSelfAdjoint])
  · intro p hp
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have hs : HasDerivAt (fun s : ℝ ↦ p.val.1 + s) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add p.val.1
    have hpt : p.val.1 ∈ Ioo (0 : ℝ) 1 := by
      rw [interior_domain_eq] at hp
      exact hp.1
    have hd : HasDerivAt f (f' p.val.1) (p.val.1 + 0) := by
      simpa using hder p.val.1 hpt
    have hc := hd.comp (h := fun s : ℝ ↦ p.val.1 + s) (0 : ℝ) hs
    have he := hasDerivAt_pi.mp (hasDerivAt_pi.mp (φ.time_deriv p hp) i) j
    have h := hc.mul he
    have hz : zeroExtend φ.value (timeLine p.val 0) = φ.value p := by
      simpa [timeLine] using zeroExtend_val φ.value p
    change HasDerivAt (fun s ↦ f (p.val.1 + s) * zeroExtend φ.value (timeLine p.val s) i j)
      (f' p.val.1 * φ.value p i j + f p.val.1 * φ.dt p i j) 0
    convert h using 1 <;> try rfl
    simp only [Function.comp_def, add_zero, mul_one, hz]
  · intro p j hp
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro k
    have he := hasDerivAt_pi.mp (hasDerivAt_pi.mp (φ.space_deriv p j hp) i) k
    exact he.const_mul (f p.val.1)

@[simp] theorem timeWeightedJet_value (φ : ClosedC1Jet Ω n) (f f' : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hf' : ContinuousOn f' (Icc (0 : ℝ) 1))
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' t) t) (p : Q Ω) :
    (timeWeightedJet φ f f' hf hf' hder).value p = f p.val.1 • φ.value p := rfl

@[simp] theorem timeWeightedJet_dt (φ : ClosedC1Jet Ω n) (f f' : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hf' : ContinuousOn f' (Icc (0 : ℝ) 1))
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' t) t) (p : Q Ω) :
    (timeWeightedJet φ f f' hf hf' hder).dt p =
      f' p.val.1 • φ.value p + f p.val.1 • φ.dt p := rfl

/-- Weighted time FTC for the entire original boundary test convention. -/
theorem weighted_time_FTC (G : HubGeometry d Ω) (φ : ClosedC1Jet Ω n) (f f' : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hf' : ContinuousOn f' (Icc (0 : ℝ) 1))
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (i j : Fin n) (x : ↥Ω) :
    (∫ s, (f' s.val * φ.value (LiZouTransport.Boundary.timeInsert s x) i j +
      f s.val * φ.dt (LiZouTransport.Boundary.timeInsert s x) i j) ∂unitTime) =
      f 1 * φ.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ x) i j -
        f 0 * φ.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ x) i j := by
  have h := LiZouTransport.Boundary.timeResidual_zero G
    (timeWeightedJet φ f f' hf hf' hder) i j x
  simp only [LiZouTransport.Boundary.timeResidual, timeWeightedJet_dt, timeWeightedJet_value,
    LiZouTransport.Boundary.timeInsert, timeBoundary, ContinuousMap.coe_mk,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
  change (∫ s, (f' s.val * φ.value (LiZouTransport.Boundary.timeInsert s x) i j +
      f s.val * φ.dt (LiZouTransport.Boundary.timeInsert s x) i j) ∂unitTime) -
      f 1 * φ.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ x) i j +
      f 0 * φ.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ x) i j = 0 at h
  linarith

/-- Multiplication by the physical time coordinate. -/
def timeMulJet (φ : ClosedC1Jet Ω n) : ClosedC1Jet Ω n :=
  timeWeightedJet φ id (fun _ ↦ 1) continuousOn_id continuousOn_const
    (fun t _ ↦ hasDerivAt_id t)

@[simp] theorem timeMulJet_value (φ : ClosedC1Jet Ω n) (p : Q Ω) :
    (timeMulJet φ).value p = p.val.1 • φ.value p := rfl
@[simp] theorem timeMulJet_dt (φ : ClosedC1Jet Ω n) (p : Q Ω) :
    (timeMulJet φ).dt p = φ.value p + p.val.1 • φ.dt p := by
  simp [timeMulJet]

/-- The time-product FTC includes boundary spatial points. -/
theorem integral_timeProduct (G : HubGeometry d Ω) (φ : ClosedC1Jet Ω n)
    (i j : Fin n) (x : ↥Ω) :
    (∫ s, (φ.value (LiZouTransport.Boundary.timeInsert s x) i j +
      s.val * φ.dt (LiZouTransport.Boundary.timeInsert s x) i j) ∂unitTime) =
      φ.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ x) i j := by
  simpa only [id_eq, one_mul, zero_mul, sub_zero] using
    weighted_time_FTC G φ id (fun _ ↦ 1) continuousOn_id continuousOn_const
      (fun t _ ↦ hasDerivAt_id t) i j x

/-- The disk has an interior hub at its centre. -/
def diskHub : HubGeometry 2 disk where
  hub := 0
  convex := convex_closedBall (0 : Spatial) 1
  hub_mem := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : Spatial) (by norm_num : (0 : ℝ) < 1))
      Metric.ball_subset_closedBall

#print axioms timeWeightedJet
#print axioms weighted_time_FTC
#print axioms timeMulJet
#print axioms integral_timeProduct
#print axioms diskHub
end LiZouTransport.NativeSeparation
