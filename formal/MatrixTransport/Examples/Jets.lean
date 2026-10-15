import MatrixTransport.Examples.Core

/-!
# Scalar closed-domain tests and Dirac endpoints

The scalar operator is `D*Φ = ∇Φ`, represented by `gradOp d`. The native test
constructor uses interior coordinate-line derivatives with continuous boundary
values and derivatives. Dirac endpoints are genuine signed Radon measures, with
an exact endpoint pairing. The closed unit disk provides the counterexample domain.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace LiZouTransport.Examples

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain

/-! ### Closed-domain interior -/

section Domain

variable {d : ℕ} {Ω : Set (Space d)}

theorem mem_interior_domain {s : ℝ} {y : Space d} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ interior Ω) : ((s, y) : Ambient d) ∈ interior (domain Ω) := by
  unfold domain
  rw [interior_prod_eq, interior_Icc]
  exact ⟨hs, hy⟩

theorem continuous_coord (j : Fin d) : Continuous (fun x : Space d => x j) := by
  first
    | exact (EuclideanSpace.proj j).continuous
    | fun_prop

end Domain

/-! ### The closed unit disk -/

/-- Points of the plane, built only from `EuclideanSpace.single`. -/
def pt2 (x y : ℝ) : Space 2 := EuclideanSpace.single 0 x + EuclideanSpace.single 1 y

@[simp] theorem pt2_zero (x y : ℝ) : pt2 x y 0 = x := by
  simp [pt2, EuclideanSpace.single_apply]

@[simp] theorem pt2_one (x y : ℝ) : pt2 x y 1 = y := by
  simp [pt2, EuclideanSpace.single_apply]

theorem pt2_add_single_one (x y t : ℝ) :
    pt2 x y + t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) = pt2 x (y + t) := by
  ext i
  fin_cases i <;> simp [pt2, EuclideanSpace.single_apply]

theorem pt2_add_single_zero (x y t : ℝ) :
    pt2 x y + t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) = pt2 (x + t) y := by
  ext i
  fin_cases i <;> simp [pt2, EuclideanSpace.single_apply]

theorem norm_sq_space_two (v : Space 2) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- The closed unit disk, the spatial domain `Ω` of the counterexamples. -/
def disk2 : Set (Space 2) := Metric.closedBall (0 : Space 2) 1

instance disk2_fact : Fact (IsCompact disk2) := ⟨isCompact_closedBall _ _⟩

theorem mem_disk2_iff (v : Space 2) : v ∈ disk2 ↔ v 0 ^ 2 + v 1 ^ 2 ≤ 1 := by
  unfold disk2
  rw [mem_closedBall_zero_iff]
  have h := norm_sq_space_two v
  constructor
  · intro h1
    nlinarith [norm_nonneg v]
  · intro h1
    nlinarith [norm_nonneg v]

theorem mem_interior_disk2 {v : Space 2} (h : v 0 ^ 2 + v 1 ^ 2 < 1) : v ∈ interior disk2 := by
  unfold disk2
  rw [interior_closedBall _ one_ne_zero, mem_ball_zero_iff]
  have h2 := norm_sq_space_two v
  nlinarith [norm_nonneg v]

/-! ### The scalar gradient operator `D*Φ = ∇Φ` -/

section Grad

variable {d : ℕ} {Ω : Set (Space d)}

/-- Column `j` of the row vector `(0,…,M₀₀,…,0)`. -/
def gradRowLinear (d : ℕ) (j : Fin d) : Mat 1 →ₗ[ℝ] Matrix (Fin 1) (Fin d) ℝ where
  toFun M := Matrix.of fun (_ : Fin 1) (l : Fin d) => if l = j then M 0 0 else 0
  map_add' := by
    intro M N
    ext i l
    by_cases h : l = j <;> simp [h]
  map_smul' := by
    intro c M
    ext i l
    by_cases h : l = j <;> simp [h]

/-- The original operator with `D0 = 0` (so `D* I = 0`) and `Dj j M = M ⊗ eⱼ`; for scalar tests
`D*Φ = ∇Φ`, the scalar Wasserstein–Fisher–Rao model of Li–Zou §7. -/
def gradOp (d : ℕ) : AdjointOperator d 1 d where
  D0 := 0
  Dj j := (gradRowLinear d j).toContinuousLinearMap
  D0_one := by simp

theorem gradOp_apply (φ : ClosedC1Jet Ω 1) (p : Q Ω) (l : Fin d) :
    (gradOp d).apply φ p 0 l = φ.dx l p 0 0 := by
  first
    | simp [AdjointOperator.apply, gradOp, gradRowLinear, Matrix.sum_apply, Finset.sum_ite_eq]
    | simp [AdjointOperator.apply, gradOp, gradRowLinear, Finset.sum_apply, Finset.sum_ite_eq]

end Grad

/-! ### Scalar jets -/

section ScalarJet

variable {d : ℕ} {Ω : Set (Space d)}

/-- A genuine `ClosedC1Jet Ω 1` from scalar closed-domain data: continuous value and partial
derivative extensions on the closed domain, with the derivative certificates required only at
interior points, exactly as in the original test class. -/
def scalarJet (F Ft : Ambient d → ℝ) (Fx : Fin d → Ambient d → ℝ)
    (hF : ContinuousOn F (domain Ω)) (hFt : ContinuousOn Ft (domain Ω))
    (hFx : ∀ j, ContinuousOn (Fx j) (domain Ω))
    (hdt : ∀ p : Q Ω, p.val ∈ interior (domain Ω) →
      HasDerivAt (fun s ↦ F (timeLine p.val s)) (Ft p.val) 0)
    (hdx : ∀ (p : Q Ω) (j : Fin d), p.val ∈ interior (domain Ω) →
      HasDerivAt (fun s ↦ F (spaceLine p.val j s)) (Fx j p.val) 0) :
    ClosedC1Jet Ω 1 := by
  have hcF : Continuous fun q : Q Ω ↦ F q.val • (1 : Mat 1) :=
    (hF.comp_continuous continuous_subtype_val (fun q ↦ q.property)).smul continuous_const
  have hcFt : Continuous fun q : Q Ω ↦ Ft q.val • (1 : Mat 1) :=
    (hFt.comp_continuous continuous_subtype_val (fun q ↦ q.property)).smul continuous_const
  have hcFx : ∀ j, Continuous fun q : Q Ω ↦ Fx j q.val • (1 : Mat 1) := fun j ↦
    ((hFx j).comp_continuous continuous_subtype_val (fun q ↦ q.property)).smul continuous_const
  refine ClosedC1Jet.ofAmbient (fun p ↦ F p • (1 : Mat 1))
    ⟨fun q ↦ F q.val • (1 : Mat 1), hcF⟩ ⟨fun q ↦ Ft q.val • (1 : Mat 1), hcFt⟩
    (fun j ↦ ⟨fun q ↦ Fx j q.val • (1 : Mat 1), hcFx j⟩) (fun _ ↦ rfl) ?_ ?_ ?_ ?_ ?_
  · intro p
    exact Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)
  · intro p
    exact Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)
  · intro j p
    exact Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)
  · intro p hp
    first
      | exact (hdt p hp).smul_const (1 : Mat 1)
      | (convert (hdt p hp).smul_const (1 : Mat 1) using 1 <;> first | rfl | simp)
  · intro p j hp
    first
      | exact (hdx p j hp).smul_const (1 : Mat 1)
      | (convert (hdx p j hp).smul_const (1 : Mat 1) using 1 <;> first | rfl | simp)

variable (F Ft : Ambient d → ℝ) (Fx : Fin d → Ambient d → ℝ)

theorem scalarJet_value_apply (hF hFt hFx hdt hdx) (q : Q Ω) :
    (scalarJet (Ω := Ω) F Ft Fx hF hFt hFx hdt hdx).value q 0 0 = F q.val := by
  first
    | (show (F q.val • (1 : Mat 1)) 0 0 = F q.val; simp)
    | simp [scalarJet, ClosedC1Jet.ofAmbient]

theorem scalarJet_dt_apply (hF hFt hFx hdt hdx) (q : Q Ω) :
    (scalarJet (Ω := Ω) F Ft Fx hF hFt hFx hdt hdx).dt q 0 0 = Ft q.val := by
  first
    | (show (Ft q.val • (1 : Mat 1)) 0 0 = Ft q.val; simp)
    | simp [scalarJet, ClosedC1Jet.ofAmbient]

theorem scalarJet_dx_apply (hF hFt hFx hdt hdx) (j : Fin d) (q : Q Ω) :
    (scalarJet (Ω := Ω) F Ft Fx hF hFt hFx hdt hdx).dx j q 0 0 = Fx j q.val := by
  first
    | (show (Fx j q.val • (1 : Mat 1)) 0 0 = Fx j q.val; simp)
    | simp [scalarJet, ClosedC1Jet.ofAmbient]

end ScalarJet

/-! ### The dual-set criterion for a scalar test under the gradient operator -/

section Dual

variable {d : ℕ} {Ω : Set (Space d)}

theorem testField_mem_dualSet_gradOp (L : Matrix (Fin d) (Fin d) ℝ) (φ : ClosedC1Jet Ω 1)
    (q : Q Ω)
    (h : φ.dt q 0 0 + (1 / 2 : ℝ) * (∑ l, (∑ l', φ.dx l' q 0 0 * L l' l) ^ 2) +
      (1 / 2 : ℝ) * (φ.value q 0 0) ^ 2 ≤ 0) :
    testField (gradOp d) φ q ∈ dualSet L (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  apply mem_dualSet_fin_one
  have hm : mass (testField (gradOp d) φ q) 0 0 = φ.dt q 0 0 := rfl
  have hr : (reaction (testField (gradOp d) φ q) * (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0 =
      φ.value q 0 0 := by
    simp [reaction, testField, pack]
  have hf : ∀ l, (flux (testField (gradOp d) φ q) * L) 0 l =
      ∑ l', φ.dx l' q 0 0 * L l' l := by
    intro l
    simp [Matrix.mul_apply, flux, testField, pack, gradOp_apply]
  rw [hm, hr]
  simp only [hf]
  exact h

/-- Converse extraction used for upper bounds: the scalar slack of a dual-set member. -/
theorem dualSet_bound_gradOp (L : Matrix (Fin d) (Fin d) ℝ)
    (a : Coord 1 d → ℝ) (ha : a ∈ dualSet L (1 : Matrix (Fin 1) (Fin 1) ℝ)) :
    mass a 0 0 + (1 / 2 : ℝ) * (∑ l, (∑ l', flux a 0 l' * L l' l) ^ 2) +
      (1 / 2 : ℝ) * (reaction a 0 0) ^ 2 ≤ 0 := by
  have h := dualSet_fin_one_bound L (1 : Matrix (Fin 1) (Fin 1) ℝ) a ha
  simpa [Matrix.mul_apply] using h

end Dual

/-! ### Dirac endpoints -/

section Dirac

variable {d : ℕ} {Ω : Set (Space d)}

/-- The signed Radon measure `m δₓ` on `↥Ω`. -/
def diracAt (x : ↥Ω) (m : ℝ) : SignedMeasure ↥Ω :=
  (Measure.dirac x).withDensityᵥ (fun _ => m)

theorem signedPair_diracAt (x : ↥Ω) (m : ℝ) (f : ↥Ω → ℝ) (hf : Measurable f)
    (hB : ∃ C : ℝ, ∀ y, |f y| ≤ C) :
    MatrixTransport.signedPair (diracAt x m) f = f x * m := by
  unfold diracAt
  rw [MatrixTransport.signedPair_withDensityᵥ (Measure.dirac x) measurable_const
    (integrable_const m) hf hB]
  exact integral_dirac' (fun y => f y * m) x (hf.mul measurable_const).stronglyMeasurable

theorem diracAt_nonneg (x : ↥Ω) {m : ℝ} (hm : 0 ≤ m) (s : Set ↥Ω) (hs : MeasurableSet s) :
    0 ≤ diracAt x m s := by
  unfold diracAt
  have hI : Integrable (fun _ : ↥Ω => m) (Measure.dirac x) := integrable_const m
  rw [withDensityᵥ_apply hI hs]
  exact integral_nonneg (fun _ => hm)

theorem diracAt_posSemidef (x : ↥Ω) {m : ℝ} (hm : 0 ≤ m) :
    EndpointPositiveSemidefinite (fun _ : Fin 1 × Fin 1 => diracAt x m) := by
  intro s hs
  exact posSemidef_fin_one _ (diracAt_nonneg x hm s hs)

variable [Fact (IsCompact Ω)]

/-- Exact evaluation of the original endpoint pairing on a (scalar) Dirac endpoint. -/
theorem endpointPair_diracAt (x : ↥Ω) (m : ℝ) (φ : ClosedC1Jet Ω 1) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    endpointPair (fun _ : Fin 1 × Fin 1 => diracAt x m) φ t ht =
      φ.value (timeBoundary t ht x) 0 0 * m := by
  haveI : CompactSpace ↥Ω := isCompact_iff_compactSpace.mp (Fact.out : IsCompact Ω)
  have hcont : Continuous fun y : ↥Ω => φ.value (timeBoundary t ht y) 0 0 :=
    (continuous_apply 0).comp ((continuous_apply 0).comp
      (φ.value.continuous.comp (timeBoundary t ht).continuous))
  have hB : ∃ C : ℝ, ∀ y : ↥Ω, |φ.value (timeBoundary t ht y) 0 0| ≤ C :=
    exists_abs_bound_of_continuous (fun y : ↥Ω => φ.value (timeBoundary t ht y) 0 0) hcont
  unfold endpointPair
  rw [sum_fin_one, sum_fin_one]
  exact signedPair_diracAt x m _ hcont.measurable hB

/-- A Dirac endpoint of mass `m` has total mass `m`. -/
theorem endpointMass_diracAt (x : ↥Ω) (m : ℝ) :
    endpointMass (fun _ : Fin 1 × Fin 1 => diracAt x m) = m := by
  haveI : CompactSpace ↥Ω := isCompact_iff_compactSpace.mp (Fact.out : IsCompact Ω)
  unfold endpointMass
  rw [sum_fin_one]
  rw [signedPair_diracAt x m (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩]
  ring

end Dirac

end LiZouTransport.Examples

end
