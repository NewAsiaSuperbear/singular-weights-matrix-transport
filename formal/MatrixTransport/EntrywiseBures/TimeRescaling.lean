import MatrixTransport.Paper.BoundaryTime

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace MatrixTransport.EntrywiseBures
open MatrixTransport.ReactionZero.ClosedDomain
variable {d n : ℕ} {Ω : Set (Space d)}

def timeScalePoint (a r : ℝ) (p : Ambient d) : Ambient d := (a + r * p.1, p.2)

theorem timeScale_mem {a r : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) (p : Q Ω) :
    timeScalePoint a r p.val ∈ domain Ω := by
  refine ⟨⟨?_, ?_⟩, p.property.2⟩
  · dsimp [timeScalePoint]
    nlinarith [mul_nonneg hr.le p.property.1.1, ha.1]
  · dsimp [timeScalePoint]
    nlinarith [mul_le_mul_of_nonneg_left p.property.1.2 hr.le, hab.2]

def timeScale (a r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) : C(Q Ω, Q Ω) :=
  ⟨fun p ↦ ⟨timeScalePoint a r p.val, timeScale_mem ha hab hr p⟩,
    ((continuous_const.add (continuous_const.mul (continuous_fst.comp continuous_subtype_val))).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

theorem timeScale_interior {a r : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) {p : Q Ω}
    (hp : p.val ∈ interior (domain Ω)) : timeScalePoint a r p.val ∈ interior (domain Ω) := by
  rw [interior_domain_eq] at hp ⊢
  refine ⟨⟨?_, ?_⟩, hp.2⟩
  · dsimp [timeScalePoint]
    nlinarith [mul_pos hr hp.1.1, ha.1]
  · dsimp [timeScalePoint]
    nlinarith [mul_lt_mul_of_pos_left hp.1.2 hr, hab.2]

/-- Pullback of the entire native jet under an affine time segment. -/
def timePullbackJet (φ : ClosedC1Jet Ω n) (a r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) :
    ClosedC1Jet Ω n := by
  let T := timeScale (Ω := Ω) a r ha hab hr
  let v : C(Q Ω, Mat n) := φ.value.comp T
  let dt : C(Q Ω, Mat n) := ⟨fun p ↦ r • φ.dt (T p),
    (φ.dt.continuous.comp T.continuous).const_smul r⟩
  let dx : Fin d → C(Q Ω, Mat n) := fun j ↦ (φ.dx j).comp T
  refine ClosedC1Jet.ofAmbient (fun p ↦ zeroExtend φ.value (timeScalePoint a r p))
    v dt dx ?_ ?_ ?_ ?_ ?_ ?_
  · intro p
    exact zeroExtend_val φ.value (T p)
  · intro p
    exact φ.value_symmetric (T p)
  · intro p
    exact (φ.dt_symmetric (T p)).smul (IsSelfAdjoint.all r)
  · intro j p
    exact φ.dx_symmetric j (T p)
  · intro p hp
    have hq := timeScale_interior ha hab hr hp
    have h0 := φ.time_deriv (T p) hq
    have hi : HasDerivAt (fun u : ℝ ↦ r * u) r 0 := by
      convert (hasDerivAt_id (0 : ℝ)).const_mul r using 1 <;> first | rfl | simp
    have h0' : HasDerivAt (fun u : ℝ ↦ zeroExtend φ.value (timeLine (T p).val u))
        (φ.dt (T p)) ((fun u : ℝ ↦ r * u) 0) := by simpa only [mul_zero] using h0
    have h := h0'.scomp (h := fun u : ℝ ↦ r * u) 0 hi
    convert h using 1 <;> try rfl
    funext u
    congr 1
    refine Prod.ext ?_ rfl
    change a + r * (p.val.1 + u) = a + r * p.val.1 + r * u
    ring
  · intro p j hp
    have hq := timeScale_interior ha hab hr hp
    have h0 := φ.space_deriv (T p) j hq
    convert h0 using 1 <;> first | rfl | simp [timeScalePoint, timeScale, T, spaceLine]

@[simp] theorem timePullbackJet_value (φ : ClosedC1Jet Ω n) (a r : ℝ)
    (ha hab hr) (p : Q Ω) :
    (timePullbackJet φ a r ha hab hr).value p = φ.value (timeScale a r ha hab hr p) := rfl

@[simp] theorem timePullbackJet_dt (φ : ClosedC1Jet Ω n) (a r : ℝ)
    (ha hab hr) (p : Q Ω) :
    (timePullbackJet φ a r ha hab hr).dt p = r • φ.dt (timeScale a r ha hab hr p) := rfl

@[simp] theorem timePullbackJet_dx (φ : ClosedC1Jet Ω n) (a r : ℝ)
    (ha hab hr) (j : Fin d) (p : Q Ω) :
    (timePullbackJet φ a r ha hab hr).dx j p = φ.dx j (timeScale a r ha hab hr p) := rfl

#print axioms timePullbackJet
end MatrixTransport.EntrywiseBures
