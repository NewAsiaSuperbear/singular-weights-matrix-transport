import MatrixTransport.ReactionZero.ContinuityEquation
import MatrixTransport.ReactionZero.MatrixSymmetry

/-!
# C¹ tests on the whole closed space-time domain

The test type has continuous values and partial derivatives on `[0,1] × Ω`. Its
derivative assertions hold on the interior, using the zero extension only as a
local representative. There is no requirement of smoothness on an open neighborhood.
The continuity equation is instantiated with every object of this test type and
with the actual coordinate signed-measure endpoint integrals.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal Matrix BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace MatrixTransport.ReactionZero.ClosedDomain

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Ambient (d : ℕ) := ℝ × Space d
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def domain {d : ℕ} (Ω : Set (Space d)) : Set (Ambient d) := Icc 0 1 ×ˢ Ω
abbrev Q {d : ℕ} (Ω : Set (Space d)) := ↥(domain Ω)

variable {d n k : ℕ} {Ω : Set (Space d)}

instance domainCompactSpace [Fact (IsCompact Ω)] : CompactSpace (Q Ω) :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod (Fact.out : IsCompact Ω))

/-- No regularity is imposed on the extension outside the closed domain. -/
def zeroExtend (f : C(Q Ω, Mat n)) (p : Ambient d) : Mat n :=
  @dite _ (p ∈ domain Ω) (Classical.propDecidable _) (fun hp ↦ f ⟨p, hp⟩) (fun _ ↦ 0)

def timeLine (p : Ambient d) (s : ℝ) : Ambient d := (p.1 + s, p.2)

def spaceLine (p : Ambient d) (j : Fin d) (s : ℝ) : Ambient d :=
  (p.1, p.2 + s • EuclideanSpace.single j 1)

theorem continuous_timeLine (p : Ambient d) : Continuous (timeLine p) := by
  exact (continuous_const.add continuous_id).prodMk continuous_const

theorem continuous_spaceLine (p : Ambient d) (j : Fin d) :
    Continuous (spaceLine p j) := by
  exact continuous_const.prodMk (continuous_const.add
    (continuous_id.smul continuous_const))

/-- The native closed-domain C¹ convention: derivatives in the interior, continuous
extensions to the whole boundary, with symmetric matrix values and derivatives. -/
structure ClosedC1Jet (Ω : Set (Space d)) (n : ℕ) where
  value : C(Q Ω, Mat n)
  dt : C(Q Ω, Mat n)
  dx : Fin d → C(Q Ω, Mat n)
  value_symmetric : ∀ p, (value p).IsHermitian
  dt_symmetric : ∀ p, (dt p).IsHermitian
  dx_symmetric : ∀ j p, (dx j p).IsHermitian
  time_deriv : ∀ p : Q Ω, p.val ∈ interior (domain Ω) →
    HasDerivAt (fun s ↦ zeroExtend value (timeLine p.val s)) (dt p) 0
  space_deriv : ∀ (p : Q Ω) (j : Fin d), p.val ∈ interior (domain Ω) →
    HasDerivAt (fun s ↦ zeroExtend value (spaceLine p.val j s)) (dx j p) 0

/-- A continuous line through an interior point remains in the domain near zero;
the arbitrary ambient representative and native zero extension agree there. -/
theorem zeroExtend_eventuallyEq (v : C(Q Ω, Mat n)) (F : Ambient d → Mat n)
    (hF : ∀ p : Q Ω, F p.val = v p) (p : Q Ω)
    (hp : p.val ∈ interior (domain Ω)) (line : ℝ → Ambient d)
    (hline : Continuous line) (hzero : line 0 = p.val) :
    (fun s ↦ zeroExtend v (line s)) =ᶠ[𝓝 0] (fun s ↦ F (line s)) := by
  have ht : Tendsto line (𝓝 0) (𝓝 p.val) := hzero ▸ hline.continuousAt
  have hmem : ∀ᶠ s in 𝓝 0, line s ∈ domain Ω :=
    ht.eventually (mem_of_superset (isOpen_interior.mem_nhds hp) interior_subset)
  filter_upwards [hmem] with s hs
  simp only [zeroExtend, dite_eq_left hs]
  exact (hF ⟨line s, hs⟩).symm

/-- Constructor from a function whose partial derivatives exist only in the interior.
The hypotheses contain the actual derivative statements, rather than a smooth ambient
extension hypothesis or an assumed inclusion of all paper tests. -/
def ClosedC1Jet.ofAmbient (F : Ambient d → Mat n)
    (v t : C(Q Ω, Mat n)) (x : Fin d → C(Q Ω, Mat n))
    (hF : ∀ p : Q Ω, F p.val = v p)
    (hv : ∀ p, (v p).IsHermitian) (ht : ∀ p, (t p).IsHermitian)
    (hx : ∀ j p, (x j p).IsHermitian)
    (hdt : ∀ p : Q Ω, p.val ∈ interior (domain Ω) →
      HasDerivAt (fun s ↦ F (timeLine p.val s)) (t p) 0)
    (hdx : ∀ (p : Q Ω) (j : Fin d), p.val ∈ interior (domain Ω) →
      HasDerivAt (fun s ↦ F (spaceLine p.val j s)) (x j p) 0) :
    ClosedC1Jet Ω n where
  value := v
  dt := t
  dx := x
  value_symmetric := hv
  dt_symmetric := ht
  dx_symmetric := hx
  time_deriv := fun p hp ↦ (hdt p hp).congr_of_eventuallyEq
    (zeroExtend_eventuallyEq v F hF p hp _ (continuous_timeLine p.val) (by simp [timeLine]))
  space_deriv := fun p j hp ↦ (hdx p j hp).congr_of_eventuallyEq
    (zeroExtend_eventuallyEq v F hF p hp _ (continuous_spaceLine p.val j)
      (by simp [spaceLine]))

/-- Actual constant-coefficient adjoint operator. The zero-order coefficient kills `I`. -/
structure AdjointOperator (d n k : ℕ) where
  D0 : Mat n →L[ℝ] Matrix (Fin n) (Fin k) ℝ
  Dj : Fin d → Mat n →L[ℝ] Matrix (Fin n) (Fin k) ℝ
  D0_one : D0 1 = 0

/-- The actual real symmetric matrix space, as a linear subspace of all matrices. -/
abbrev SymMat (n : ℕ) := ↥(selfAdjoint.submodule ℝ (Mat n))

/-- Every symmetric-valued paper test given by its continuous closed-domain values and
partial-derivative extensions maps to the entire native jet class. Only interior derivative
certificates are required; symmetry of the derivative extensions is a codomain fact. -/
def ClosedC1Jet.ofSymmetricPartials (F : Ambient d → SymMat n)
    (v t : C(Q Ω, SymMat n)) (x : Fin d → C(Q Ω, SymMat n))
    (hF : ∀ p : Q Ω, F p.val = v p)
    (hdt : ∀ p : Q Ω, p.val ∈ interior (domain Ω) →
      HasDerivAt (fun s ↦ F (timeLine p.val s)) (t p) 0)
    (hdx : ∀ (p : Q Ω) (j : Fin d), p.val ∈ interior (domain Ω) →
      HasDerivAt (fun s ↦ F (spaceLine p.val j s)) (x j p) 0) : ClosedC1Jet Ω n := by
  let incl : SymMat n →L[ℝ] Mat n := (selfAdjoint.submodule ℝ (Mat n)).subtypeL
  let vf : C(Q Ω, Mat n) :=
    ⟨fun p ↦ incl (v p), incl.continuous.comp v.continuous⟩
  let tf : C(Q Ω, Mat n) :=
    ⟨fun p ↦ incl (t p), incl.continuous.comp t.continuous⟩
  let xf : Fin d → C(Q Ω, Mat n) := fun j ↦
    ⟨fun p ↦ incl (x j p), incl.continuous.comp (x j).continuous⟩
  refine ClosedC1Jet.ofAmbient (fun p ↦ incl (F p)) vf tf xf ?_ ?_ ?_ ?_ ?_ ?_
  · intro p
    change incl (F p.val) = incl (v p)
    rw [hF p]
  · intro p
    exact (v p).property
  · intro p
    exact (t p).property
  · intro j p
    exact (x j p).property
  · intro p hp
    convert incl.hasFDerivAt.comp_hasDerivAt 0 (hdt p hp) using 1 <;> rfl
  · intro p j hp
    convert incl.hasFDerivAt.comp_hasDerivAt 0 (hdx p j hp) using 1 <;> rfl

@[simp] theorem ClosedC1Jet.ofSymmetricPartials_value
    (F : Ambient d → SymMat n) (v t : C(Q Ω, SymMat n))
    (x : Fin d → C(Q Ω, SymMat n)) (hF hdt hdx) (p : Q Ω) :
    (ClosedC1Jet.ofSymmetricPartials F v t x hF hdt hdx).value p = (v p : Mat n) := rfl

@[simp] theorem ClosedC1Jet.ofSymmetricPartials_dt
    (F : Ambient d → SymMat n) (v t : C(Q Ω, SymMat n))
    (x : Fin d → C(Q Ω, SymMat n)) (hF hdt hdx) (p : Q Ω) :
    (ClosedC1Jet.ofSymmetricPartials F v t x hF hdt hdx).dt p = (t p : Mat n) := rfl

@[simp] theorem ClosedC1Jet.ofSymmetricPartials_dx
    (F : Ambient d → SymMat n) (v t : C(Q Ω, SymMat n))
    (x : Fin d → C(Q Ω, SymMat n)) (hF hdt hdx) (j : Fin d) (p : Q Ω) :
    (ClosedC1Jet.ofSymmetricPartials F v t x hF hdt hdx).dx j p = (x j p : Mat n) := rfl

/-- Constructor from a genuine symmetric-valued interior Fréchet derivative with continuous
closed-domain value and derivative extensions. Symmetry of every derivative is supplied by
its actual codomain, rather than an additional constraint imposed on paper tests. -/
def ClosedC1Jet.ofSymmetricFrechet (F : Ambient d → SymMat n)
    (v : C(Q Ω, SymMat n)) (dF : C(Q Ω, Ambient d →L[ℝ] SymMat n))
    (hF : ∀ p : Q Ω, F p.val = v p)
    (hderiv : ∀ p : Q Ω, p.val ∈ interior (domain Ω) → HasFDerivAt F (dF p) p.val) :
    ClosedC1Jet Ω n := by
  let incl : SymMat n →L[ℝ] Mat n := (selfAdjoint.submodule ℝ (Mat n)).subtypeL
  let vf : C(Q Ω, Mat n) :=
    ⟨fun p ↦ incl (v p), incl.continuous.comp v.continuous⟩
  let tf : C(Q Ω, Mat n) :=
    ⟨fun p ↦ incl (dF p (1, 0)), incl.continuous.comp
      (dF.continuous.clm_apply continuous_const)⟩
  let xf : Fin d → C(Q Ω, Mat n) := fun j ↦
    ⟨fun p ↦ incl (dF p (0, EuclideanSpace.single j 1)), incl.continuous.comp
      (dF.continuous.clm_apply continuous_const)⟩
  refine ClosedC1Jet.ofAmbient (fun p ↦ incl (F p)) vf tf xf ?_ ?_ ?_ ?_ ?_ ?_
  · intro p
    change incl (F p.val) = incl (v p)
    rw [hF p]
  · intro p
    exact (v p).property
  · intro p
    exact (dF p (1, 0)).property
  · intro j p
    exact (dF p (0, EuclideanSpace.single j 1)).property
  · intro p hp
    have hl : HasDerivAt (timeLine p.val) (1, 0) 0 := by
      convert ((hasDerivAt_const (0 : ℝ) p.val.1).add (hasDerivAt_id (0 : ℝ))).prodMk
        (hasDerivAt_const (0 : ℝ) p.val.2) using 1 <;> first | rfl | simp
    have hd := (incl.hasFDerivAt.comp p.val (hderiv p hp))
    have hd' : HasFDerivAt (fun p ↦ incl (F p)) (incl.comp (dF p)) (timeLine p.val 0) := by
      convert hd using 1 <;> first | rfl | simp [timeLine]
    convert hd'.comp_hasDerivAt 0 hl using 1 <;> rfl
  · intro p j hp
    have hl : HasDerivAt (spaceLine p.val j) (0, EuclideanSpace.single j 1) 0 := by
      convert (hasDerivAt_const (0 : ℝ) p.val.1).prodMk
        ((hasDerivAt_const (0 : ℝ) p.val.2).add
          ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j 1)))
        using 1 <;> first | rfl | simp
    have hd := (incl.hasFDerivAt.comp p.val (hderiv p hp))
    have hd' : HasFDerivAt (fun p ↦ incl (F p)) (incl.comp (dF p)) (spaceLine p.val j 0) := by
      convert hd using 1 <;> first | rfl | simp [spaceLine]
    convert hd'.comp_hasDerivAt 0 hl using 1 <;> rfl

/-- Symmetric projection is defined on every matrix; its range certificate is proved. -/
def symmetricProjectionLinear : Mat n →ₗ[ℝ] SymMat n where
  toFun A := ⟨(1 / 2 : ℝ) • (A + A.transpose), by
    change Matrix.IsHermitian ((1 / 2 : ℝ) • (A + A.transpose))
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      smul_eq_mul]
    ring⟩
  map_add' A B := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • ((A + B) + (A + B).transpose) =
      (1 / 2 : ℝ) • (A + A.transpose) + (1 / 2 : ℝ) • (B + B.transpose)
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  map_smul' a A := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • ((a • A) + (a • A).transpose) =
      a • ((1 / 2 : ℝ) • (A + A.transpose))
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    ring

def symmetricProjection : Mat n →L[ℝ] SymMat n :=
  symmetricProjectionLinear.toContinuousLinearMap

theorem symmetricProjection_eq_self (A : Mat n) (hA : A.IsHermitian) :
    symmetricProjection A = (⟨A, hA⟩ : SymMat n) := by
  apply Subtype.ext
  ext i j
  have h := hA.apply i j
  simp only [star_trivial] at h
  change (1 / 2 : ℝ) * (A i j + A j i) = A i j
  rw [h]
  ring

/-- Arbitrary original constant-coefficient maps on symmetric matrices. They need only
be linear: their finite-dimensional domain proves continuity. -/
structure SymmetricAdjointOperator (d n k : ℕ) where
  D0 : SymMat n →ₗ[ℝ] Matrix (Fin n) (Fin k) ℝ
  Dj : Fin d → SymMat n →ₗ[ℝ] Matrix (Fin n) (Fin k) ℝ
  D0_one : D0 ⟨1, Matrix.isHermitian_one⟩ = 0

/-- Every original operator on the symmetric matrix space has an actual full-matrix
extension, with equality on every symmetric value proved below. -/
def SymmetricAdjointOperator.extend (D : SymmetricAdjointOperator d n k) :
    AdjointOperator d n k where
  D0 := D.D0.toContinuousLinearMap.comp symmetricProjection
  Dj := fun j ↦ (D.Dj j).toContinuousLinearMap.comp symmetricProjection
  D0_one := by
    simp only [ContinuousLinearMap.comp_apply, symmetricProjection_eq_self _
      Matrix.isHermitian_one, LinearMap.coe_toContinuousLinearMap']
    exact D.D0_one

theorem SymmetricAdjointOperator.extend_D0 (D : SymmetricAdjointOperator d n k)
    (A : Mat n) (hA : A.IsHermitian) : D.extend.D0 A = D.D0 ⟨A, hA⟩ := by
  simp only [SymmetricAdjointOperator.extend, ContinuousLinearMap.comp_apply,
    symmetricProjection_eq_self _ hA, LinearMap.coe_toContinuousLinearMap']

theorem SymmetricAdjointOperator.extend_Dj (D : SymmetricAdjointOperator d n k)
    (j : Fin d) (A : Mat n) (hA : A.IsHermitian) : D.extend.Dj j A = D.Dj j ⟨A, hA⟩ := by
  simp only [SymmetricAdjointOperator.extend, ContinuousLinearMap.comp_apply,
    symmetricProjection_eq_self _ hA, LinearMap.coe_toContinuousLinearMap']

def AdjointOperator.apply (D : AdjointOperator d n k) (φ : ClosedC1Jet Ω n) :
    C(Q Ω, Matrix (Fin n) (Fin k) ℝ) :=
  ⟨fun p ↦ D.D0 (φ.value p) + ∑ j, D.Dj j (φ.dx j p), by
    apply Continuous.add (D.D0.continuous.comp φ.value.continuous)
    exact continuous_finsetSum _ fun j _ ↦ (D.Dj j).continuous.comp (φ.dx j).continuous⟩

theorem SymmetricAdjointOperator.extend_apply (D : SymmetricAdjointOperator d n k)
    (φ : ClosedC1Jet Ω n) (p : Q Ω) :
    D.extend.apply φ p = D.D0 ⟨φ.value p, φ.value_symmetric p⟩ +
      ∑ j, D.Dj j ⟨φ.dx j p, φ.dx_symmetric j p⟩ := by
  simp only [AdjointOperator.apply, ContinuousMap.coe_mk,
    SymmetricAdjointOperator.extend_D0 _ _ (φ.value_symmetric p),
    SymmetricAdjointOperator.extend_Dj _ _ _ (φ.dx_symmetric _ p)]

def testField (D : AdjointOperator d n k) (φ : ClosedC1Jet Ω n) :
    C(Q Ω, Coord n k → ℝ) :=
  ⟨fun p ↦ pack (φ.dt p) (D.apply φ p) (φ.value p), by
    apply continuous_pi
    intro c
    rcases c with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
    · exact (continuous_apply j).comp ((continuous_apply i).comp φ.dt.continuous)
    · exact (continuous_apply j).comp ((continuous_apply i).comp (D.apply φ).continuous)
    · exact (continuous_apply j).comp ((continuous_apply i).comp φ.value.continuous)⟩

def timeBoundary (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : C(↥Ω, Q Ω) :=
  ⟨fun x ↦ ⟨(t, x.val), ht, x.property⟩,
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩

def endpointPair (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (φ : ClosedC1Jet Ω n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ℝ :=
  ∑ i, ∑ j, MatrixTransport.signedPair (g (i, j))
    (fun x ↦ φ.value (timeBoundary t ht x) i j)

def paperTestFamily (D : AdjointOperator d n k)
    (g0 g1 : (Fin n × Fin n) → SignedMeasure ↥Ω) :
    ContinuousTestFamily (Q Ω) (Coord n k) (ClosedC1Jet Ω n) where
  field := testField D
  endpoint := fun φ ↦ endpointPair g1 φ 1 ⟨zero_le_one, le_rfl⟩ -
    endpointPair g0 φ 0 ⟨le_rfl, zero_le_one⟩

/-- The CE quantifies over the entire native boundary-C¹ test type. -/
def PaperContinuityEquation (D : AdjointOperator d n k)
    (g0 g1 : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (μ : Coord n k → SignedMeasure (Q Ω)) : Prop :=
  SatisfiesContinuityEquation (paperTestFamily D g0 g1) μ

/-- Actual closure with all closed-domain C¹ tests and the same possibly singular endpoints. -/
theorem paperContinuityEquation_of_signedWeakStar
    (D : AdjointOperator d n k) (g0 g1 : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (μ : ℕ → Coord n k → SignedMeasure (Q Ω)) (ν : Coord n k → SignedMeasure (Q Ω))
    (hμ : SignedWeakStarTendsto μ ν) (hCE : ∀ l, PaperContinuityEquation D g0 g1 (μ l)) :
    PaperContinuityEquation D g0 g1 ν :=
  satisfiesContinuityEquation_of_signedWeakStar (paperTestFamily D g0 g1) μ ν hμ hCE

def timeWeight : C(Q Ω, ℝ) :=
  ⟨fun p ↦ 1 - p.val.1, continuous_const.sub (continuous_fst.comp continuous_subtype_val)⟩

theorem timeWeight_nonneg (p : Q Ω) : 0 ≤ timeWeight p := by
  exact sub_nonneg.mpr p.property.1.2

theorem timeWeight_le_one (p : Q Ω) : timeWeight p ≤ 1 := by
  have hp := p.property.1.1
  change 1 - p.val.1 ≤ 1
  linarith

def affineTimeValue : C(Q Ω, Mat n) :=
  ⟨fun p ↦ timeWeight p • (1 : Mat n), timeWeight.continuous.smul continuous_const⟩

/-- The real test Φ=(1−t)I with actual derivative certificates, including the boundary
extensions. It exists for every closed domain, including singular or empty domains. -/
def affineTimeJet : ClosedC1Jet Ω n := by
  refine ClosedC1Jet.ofAmbient (fun p ↦ (1 - p.1) • (1 : Mat n))
    affineTimeValue (ContinuousMap.const _ (-1)) (fun _ ↦ ContinuousMap.const _ 0)
    (fun _ ↦ rfl) ?_ ?_ ?_ ?_ ?_
  · intro p
    exact Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)
  · intro p
    exact Matrix.isHermitian_one.neg
  · intro j p
    exact Matrix.isHermitian_zero
  · intro p hp
    have hscalar : HasDerivAt (fun s : ℝ ↦ 1 - (p.val.1 + s)) (-1) 0 := by
      convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
        ((hasDerivAt_const (0 : ℝ) p.val.1).add (hasDerivAt_id (0 : ℝ)))
        using 1 <;> first | rfl | simp
    convert hscalar.smul_const (1 : Mat n) using 1 <;> first | rfl | simp
  · intro p j hp
    convert (hasDerivAt_const (0 : ℝ) ((1 - p.val.1) • (1 : Mat n)))
      using 1 <;> rfl

@[simp] theorem affineTimeJet_value (p : Q Ω) :
    affineTimeJet.value p = timeWeight p • (1 : Mat n) := rfl

@[simp] theorem affineTimeJet_dt (p : Q Ω) :
    affineTimeJet.dt p = (-1 : Mat n) := rfl

@[simp] theorem affineTimeJet_dx (j : Fin d) (p : Q Ω) :
    affineTimeJet.dx j p = (0 : Mat n) := rfl

@[simp] theorem affineTimeJet_adjoint (D : AdjointOperator d n k) (p : Q Ω) :
    D.apply affineTimeJet p = 0 := by
  simp only [AdjointOperator.apply, ContinuousMap.coe_mk, affineTimeJet_value,
    affineTimeJet_dx, map_smul, map_zero, Finset.sum_const_zero, add_zero, D.D0_one, smul_zero]

theorem signedPair_zero {X : Type*} [MeasurableSpace X] (s : SignedMeasure X) :
    MatrixTransport.signedPair s (fun _ ↦ 0) = 0 := by
  simp [MatrixTransport.signedPair]

theorem signedPair_neg {X : Type*} [MeasurableSpace X] (s : SignedMeasure X) (f : X → ℝ) :
    MatrixTransport.signedPair s (fun x ↦ -f x) = -MatrixTransport.signedPair s f := by
  simp only [MatrixTransport.signedPair, integral_neg]
  ring

@[simp] theorem signedPair_ite_zero {X : Type*} [MeasurableSpace X] (s : SignedMeasure X)
    (p : Prop) [Decidable p] (f : X → ℝ) :
    MatrixTransport.signedPair s (fun x ↦ if p then f x else 0) =
      if p then MatrixTransport.signedPair s f else 0 := by
  by_cases hp : p <;> simp [hp, signedPair_zero]

def massTracePair (μ : Coord n k → SignedMeasure (Q Ω)) : ℝ :=
  ∑ i, MatrixTransport.signedPair (μ (Sum.inl (i, i))) (fun _ ↦ 1)

def reactionTracePair (μ : Coord n k → SignedMeasure (Q Ω)) : ℝ :=
  ∑ i, MatrixTransport.signedPair (μ (Sum.inr (Sum.inr (i, i)))) timeWeight

def endpointMass (g : (Fin n × Fin n) → SignedMeasure ↥Ω) : ℝ :=
  ∑ i, MatrixTransport.signedPair (g (i, i)) (fun _ ↦ 1)

theorem affineTimeJet_coordinatePair (D : AdjointOperator d n k)
    (μ : Coord n k → SignedMeasure (Q Ω)) :
    Duality.coordinatePair (fun _ ↦ 1) μ (testField D affineTimeJet) =
      -massTracePair μ + reactionTracePair μ := by
  unfold Duality.coordinatePair
  simp only [one_mul, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [testField, pack, affineTimeJet_dt, affineTimeJet_adjoint, affineTimeJet_value,
    Matrix.one_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
    signedPair_zero, signedPair_neg, massTracePair, reactionTracePair]

theorem affineTimeJet_endpointPair_zero
    (g : (Fin n × Fin n) → SignedMeasure ↥Ω) :
    endpointPair g affineTimeJet 0 ⟨le_rfl, zero_le_one⟩ = endpointMass g := by
  simp [endpointPair, affineTimeJet_value, timeWeight, timeBoundary, Matrix.one_apply,
    endpointMass]

theorem affineTimeJet_endpointPair_one
    (g : (Fin n × Fin n) → SignedMeasure ↥Ω) :
    endpointPair g affineTimeJet 1 ⟨zero_le_one, le_rfl⟩ = 0 := by
  simp [endpointPair, affineTimeJet_value, timeWeight, timeBoundary, signedPair_zero]

/-- The source of the mass bound is the real weak CE tested with Φ=(1−t)I. -/
theorem massTracePair_eq_endpoint_add_reaction (D : AdjointOperator d n k)
    (g0 g1 : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (μ : Coord n k → SignedMeasure (Q Ω)) (hCE : PaperContinuityEquation D g0 g1 μ) :
    massTracePair μ = endpointMass g0 + reactionTracePair μ := by
  have ht := hCE affineTimeJet
  change Duality.coordinatePair (fun _ ↦ 1) μ (testField D affineTimeJet) =
    endpointPair g1 affineTimeJet 1 ⟨zero_le_one, le_rfl⟩ -
    endpointPair g0 affineTimeJet 0 ⟨le_rfl, zero_le_one⟩ at ht
  rw [affineTimeJet_coordinatePair, affineTimeJet_endpointPair_one,
    affineTimeJet_endpointPair_zero] at ht
  linarith

/-- Actual PSD matrix-valued endpoint condition, evaluated on every measurable set. -/
def EndpointPositiveSemidefinite
    (g : (Fin n × Fin n) → SignedMeasure ↥Ω) : Prop :=
  ∀ s : Set ↥Ω, MeasurableSet s → Matrix.PosSemidef (fun i j ↦ g (i, j) s)

theorem signedPair_one_eq_univ {X : Type*} [MeasurableSpace X] (s : SignedMeasure X) :
    MatrixTransport.signedPair s (fun _ ↦ 1) = s univ := by
  unfold MatrixTransport.signedPair
  rw [integral_const, integral_const]
  simpa using (SignedMeasure.apply_eq_posPart_real_sub_negPart_real s MeasurableSet.univ).symm

theorem endpointMass_eq_trace (g : (Fin n × Fin n) → SignedMeasure ↥Ω) :
    endpointMass g = Matrix.trace (fun i j ↦ g (i, j) univ) := by
  simp [endpointMass, signedPair_one_eq_univ, Matrix.trace, Matrix.diag]

theorem endpointMass_nonneg (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (hg : EndpointPositiveSemidefinite g) : 0 ≤ endpointMass g := by
  rw [endpointMass_eq_trace]
  exact (hg univ MeasurableSet.univ).trace_nonneg

/-- The trace pairing in the actual CE equals the RN-integrated mass trace used by the
weighted action estimates. -/
theorem massTracePair_eq_integral (μ : Coord n k → SignedMeasure (Q Ω)) :
    massTracePair μ =
      ∫ p, (mass (Duality.density μ p)).trace ∂MatrixTransport.jointReference μ := by
  unfold massTracePair
  have hpair (i : Fin n) :
      MatrixTransport.signedPair (μ (Sum.inl (i, i))) (fun _ ↦ 1) =
        ∫ p, (μ (Sum.inl (i, i))).rnDeriv (MatrixTransport.jointReference μ) p
          ∂MatrixTransport.jointReference μ := by
    rw [MatrixTransport.signedPair_rnDeriv (MatrixTransport.jointReference μ)
      (μ (Sum.inl (i, i))) (MatrixTransport.absolutelyContinuous_jointReference μ _)
      measurable_const ⟨1, fun _ ↦ by norm_num⟩]
    simp
  simp_rw [hpair]
  rw [← integral_finsetSum _ (fun i _ ↦
    MatrixTransport.integrable_rnDeriv_jointReference μ (Sum.inl (i, i)))]
  rfl

#print axioms zeroExtend_eventuallyEq
#print axioms ClosedC1Jet.ofAmbient
#print axioms symmetricProjectionLinear
#print axioms ClosedC1Jet.ofSymmetricPartials
#print axioms ClosedC1Jet.ofSymmetricFrechet
#print axioms SymmetricAdjointOperator.extend
#print axioms SymmetricAdjointOperator.extend_apply
#print axioms paperContinuityEquation_of_signedWeakStar
#print axioms affineTimeJet
#print axioms affineTimeJet_adjoint
#print axioms massTracePair_eq_endpoint_add_reaction
#print axioms endpointMass_nonneg
#print axioms massTracePair_eq_integral

end MatrixTransport.ReactionZero.ClosedDomain
