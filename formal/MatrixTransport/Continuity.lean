import MatrixTransport.ClosedDomain
import MatrixTransport.ActionBound
import MatrixTransport.Pairing

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace MatrixTransport

structure MatrixPath (r : ℕ) where
  coords : TransportCoord r → SignedMeasure Q
  massSymmetry : ∀ i j, coords (Sum.inl (i, j)) = coords (Sum.inl (j, i))

abbrev DStar (r : ℕ) := ClosedC1Field → Q → Flux r

def testTriplet {r : ℕ} (Dstar : DStar r) (Phi : ClosedC1Field) (q : Q) :
    TransportCoord r → ℝ :=
  packTriplet (dtPhiQ Phi q) (Dstar Phi q) (Phi.toFun (q : Ambient))

def endpointPair (g : Spatial → Mat2) (Phi : ClosedC1Field) (t : ℝ) : ℝ :=
  ∫ x, frob (g x) (Phi.toFun (t, x)) ∂diskVolume

def endpointDifference (g0 g1 : Spatial → Mat2) (Phi : ClosedC1Field) : ℝ :=
  endpointPair g1 Phi 1 - endpointPair g0 Phi 0

def ContinuityEquation {r : ℕ} (Dstar : DStar r) (g0 g1 : Spatial → Mat2)
    (path : MatrixPath r) : Prop :=
  ∀ Phi : ClosedC1Field,
    canonicalPair r path.coords (testTriplet Dstar Phi) = endpointDifference g0 g1 Phi

def wbSquared {r : ℕ} (Dstar : DStar r) (g0 g1 : Spatial → Mat2) : ℝ≥0∞ :=
  ⨅ path : {p : MatrixPath r // ContinuityEquation Dstar g0 g1 p},
    matrixAction r path.val.coords

theorem wbSquared_le_action {r : ℕ} (Dstar : DStar r) (g0 g1 : Spatial → Mat2)
    (path : MatrixPath r) (h : ContinuityEquation Dstar g0 g1 path) :
    wbSquared Dstar g0 g1 ≤ matrixAction r path.coords :=
  iInf_le (fun p : {p : MatrixPath r // ContinuityEquation Dstar g0 g1 p} =>
    matrixAction r p.val.coords) ⟨path, h⟩

def LocalHJ {r : ℕ} (Dstar : DStar r) (Phi : ClosedC1Field) : Prop :=
  ∀ q : Q, LocalDualConstraint (dtPhiQ Phi q) (Dstar Phi q) (Phi.toFun (q : Ambient))

/-! ### Generic bounds -/

theorem continuous_testTriplet {r : ℕ} (Dstar : DStar r) (Phi : ClosedC1Field)
    (hD : Continuous (Dstar Phi)) : Continuous (testTriplet Dstar Phi) := by
  refine continuous_pi fun c => ?_
  rcases c with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · first
      | exact (continuous_dtPhiQ Phi).matrix_elem i j
      | simpa [testTriplet, packTriplet] using (continuous_dtPhiQ Phi).matrix_elem i j
  · first
      | exact hD.matrix_elem i j
      | exact (continuous_apply j).comp ((continuous_apply i).comp hD)
      | simpa [testTriplet, packTriplet] using hD.matrix_elem i j
  · first
      | exact Phi.continuous_Q.matrix_elem i j
      | simpa [testTriplet, packTriplet] using Phi.continuous_Q.matrix_elem i j

theorem testTriplet_measurable {r : ℕ} (Dstar : DStar r) (Phi : ClosedC1Field)
    (hD : Continuous (Dstar Phi)) (c : TransportCoord r) :
    Measurable (fun q : Q => testTriplet Dstar Phi q c) :=
  ((continuous_apply c).comp (continuous_testTriplet Dstar Phi hD)).measurable

theorem testTriplet_bounded {r : ℕ} (Dstar : DStar r) (Phi : ClosedC1Field)
    (hD : Continuous (Dstar Phi)) :
    ∃ C : ℝ, ∀ (q : Q) (c : TransportCoord r), |testTriplet Dstar Phi q c| ≤ C :=
  exists_coord_bound _ (continuous_testTriplet Dstar Phi hD)

theorem testTriplet_mem_dualSet {r : ℕ} (Dstar : DStar r) (Phi : ClosedC1Field)
    (hHJ : LocalHJ Dstar Phi) (q : Q) : testTriplet Dstar Phi q ∈ dualSet r := by
  have hm : mass (testTriplet Dstar Phi q) = dtPhiQ Phi q := mass_packTriplet _ _ _
  have hf : flux (testTriplet Dstar Phi q) = Dstar Phi q := flux_packTriplet _ _ _
  have hr : reaction (testTriplet Dstar Phi q) = Phi.toFun (q : Ambient) :=
    reaction_packTriplet _ _ _
  change (mass (testTriplet Dstar Phi q)).IsHermitian ∧
    LocalDualConstraint (mass (testTriplet Dstar Phi q)) (flux (testTriplet Dstar Phi q))
      (reaction (testTriplet Dstar Phi q))
  rw [hm, hf, hr]
  exact ⟨dtPhiQ_isHermitian Phi q, hHJ q⟩

theorem dual_bound_each_path {r : ℕ} (Dstar : DStar r) (g0 g1 : Spatial → Mat2)
    (path : MatrixPath r) (Phi : ClosedC1Field) (hD : Continuous (Dstar Phi))
    (hHJ : LocalHJ Dstar Phi) (hCE : ContinuityEquation Dstar g0 g1 path) :
    ENNReal.ofReal (endpointDifference g0 g1 Phi) ≤ matrixAction r path.coords := by
  have h := canonicalPair_le_matrixAction r path.coords (testTriplet Dstar Phi)
    (testTriplet_measurable Dstar Phi hD) (testTriplet_bounded Dstar Phi hD)
    (testTriplet_mem_dualSet Dstar Phi hHJ)
  rwa [hCE Phi] at h

theorem ofReal_endpointDifference_le_wbSquared {r : ℕ} (Dstar : DStar r)
    (g0 g1 : Spatial → Mat2) (Phi : ClosedC1Field) (hD : Continuous (Dstar Phi))
    (hHJ : LocalHJ Dstar Phi) :
    ENNReal.ofReal (endpointDifference g0 g1 Phi) ≤ wbSquared Dstar g0 g1 := by
  unfold wbSquared
  refine le_iInf fun path => ?_
  exact dual_bound_each_path Dstar g0 g1 path.val Phi hD hHJ path.property

/-! ### Concrete operators -/

def KBstar (Phi : ClosedC1Field) (q : Q) : Flux 1 :=
  fun i _ => ∑ j : Fin 2, (dxPhiQ Phi j q) i j

def KBDstar : DStar 1 := KBstar

def fullL0 : Mat2 := !![1, 0; 0, -1]

def fullL1 : Mat2 := !![0, 1; 1, 0]

def fullCol (k : Fin 8) : Fin 2 := ⟨k.val % 2, Nat.mod_lt _ (by norm_num)⟩

def fullStar (Phi : ClosedC1Field) (q : Q) : Flux 8 :=
  fun i k =>
    if k.val < 2 then dxPhiQ Phi 0 q i (fullCol k)
    else if k.val < 4 then dxPhiQ Phi 1 q i (fullCol k)
    else if k.val < 6 then
      (fullL0 * Phi.toFun (q : Ambient) - Phi.toFun (q : Ambient) * fullL0) i (fullCol k)
    else
      (fullL1 * Phi.toFun (q : Ambient) - Phi.toFun (q : Ambient) * fullL1) i (fullCol k)

def fullDstar : DStar 8 := fullStar

theorem continuous_KBstar (Phi : ClosedC1Field) : Continuous (KBstar Phi) := by
  first
    | refine continuous_matrix fun i k => ?_
    | refine continuous_pi fun i => continuous_pi fun k => ?_
  show Continuous fun q : Q => ∑ j : Fin 2, (dxPhiQ Phi j q) i j
  exact continuous_finsetSum _ fun j _ => (continuous_dxPhiQ Phi j).matrix_elem i j

theorem continuous_fullStar (Phi : ClosedC1Field) : Continuous (fullStar Phi) := by
  have hP := Phi.continuous_Q
  have h2 : Continuous fun q : Q =>
      fullL0 * Phi.toFun (q : Ambient) - Phi.toFun (q : Ambient) * fullL0 :=
    (continuous_const.matrix_mul hP).sub (hP.matrix_mul continuous_const)
  have h3 : Continuous fun q : Q =>
      fullL1 * Phi.toFun (q : Ambient) - Phi.toFun (q : Ambient) * fullL1 :=
    (continuous_const.matrix_mul hP).sub (hP.matrix_mul continuous_const)
  first
    | refine continuous_matrix fun i k => ?_
    | refine continuous_pi fun i => continuous_pi fun k => ?_
  show Continuous fun q : Q =>
    if k.val < 2 then dxPhiQ Phi 0 q i (fullCol k)
    else if k.val < 4 then dxPhiQ Phi 1 q i (fullCol k)
    else if k.val < 6 then
      (fullL0 * Phi.toFun (q : Ambient) - Phi.toFun (q : Ambient) * fullL0) i (fullCol k)
    else
      (fullL1 * Phi.toFun (q : Ambient) - Phi.toFun (q : Ambient) * fullL1) i (fullCol k)
  refine Continuous.if_const _ ?_ (Continuous.if_const _ ?_ (Continuous.if_const _ ?_ ?_))
  · exact (continuous_dxPhiQ Phi 0).matrix_elem i (fullCol k)
  · exact (continuous_dxPhiQ Phi 1).matrix_elem i (fullCol k)
  · exact h2.matrix_elem i (fullCol k)
  · exact h3.matrix_elem i (fullCol k)

theorem continuous_testTriplet_KB (Phi : ClosedC1Field) :
    Continuous (testTriplet KBDstar Phi) :=
  continuous_testTriplet KBDstar Phi (continuous_KBstar Phi)

theorem continuous_testTriplet_full (Phi : ClosedC1Field) :
    Continuous (testTriplet fullDstar Phi) :=
  continuous_testTriplet fullDstar Phi (continuous_fullStar Phi)

theorem dual_bound_each_path_KB (g0 g1 : Spatial → Mat2) (path : MatrixPath 1)
    (Phi : ClosedC1Field) (hHJ : LocalHJ KBDstar Phi)
    (hCE : ContinuityEquation KBDstar g0 g1 path) :
    ENNReal.ofReal (endpointDifference g0 g1 Phi) ≤ matrixAction 1 path.coords :=
  dual_bound_each_path KBDstar g0 g1 path Phi (continuous_KBstar Phi) hHJ hCE

theorem dual_bound_each_path_full (g0 g1 : Spatial → Mat2) (path : MatrixPath 8)
    (Phi : ClosedC1Field) (hHJ : LocalHJ fullDstar Phi)
    (hCE : ContinuityEquation fullDstar g0 g1 path) :
    ENNReal.ofReal (endpointDifference g0 g1 Phi) ≤ matrixAction 8 path.coords :=
  dual_bound_each_path fullDstar g0 g1 path Phi (continuous_fullStar Phi) hHJ hCE

theorem ofReal_endpointDifference_le_wbSquared_KB (g0 g1 : Spatial → Mat2)
    (Phi : ClosedC1Field) (hHJ : LocalHJ KBDstar Phi) :
    ENNReal.ofReal (endpointDifference g0 g1 Phi) ≤ wbSquared KBDstar g0 g1 :=
  ofReal_endpointDifference_le_wbSquared KBDstar g0 g1 Phi (continuous_KBstar Phi) hHJ

theorem ofReal_endpointDifference_le_wbSquared_full (g0 g1 : Spatial → Mat2)
    (Phi : ClosedC1Field) (hHJ : LocalHJ fullDstar Phi) :
    ENNReal.ofReal (endpointDifference g0 g1 Phi) ≤ wbSquared fullDstar g0 g1 :=
  ofReal_endpointDifference_le_wbSquared fullDstar g0 g1 Phi (continuous_fullStar Phi) hHJ

/-! ### Hermitian generators -/

theorem fullL0_isHermitian : fullL0.IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [fullL0]

theorem fullL1_isHermitian : fullL1.IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [fullL1]

/-! ### Column lemmas for `fullStar` -/

@[simp] theorem fullStar_column_zero (Phi : ClosedC1Field) (q : Q) (i : Fin 2) :
    fullStar Phi q i 0 = dxPhiQ Phi 0 q i 0 := by
  have h : fullCol 0 = 0 := by decide
  have c1 : (0 : Fin 8).val < 2 := by decide
  first
    | (simp only [fullStar]; rw [if_pos c1, h]; done)
    | (simp [fullStar, fullCol]; done)

@[simp] theorem fullStar_column_one (Phi : ClosedC1Field) (q : Q) (i : Fin 2) :
    fullStar Phi q i 1 = dxPhiQ Phi 0 q i 1 := by
  have h : fullCol 1 = 1 := by decide
  have c1 : (1 : Fin 8).val < 2 := by decide
  first
    | (simp only [fullStar]; rw [if_pos c1, h]; done)
    | (simp [fullStar, fullCol]; done)

@[simp] theorem fullStar_column_two (Phi : ClosedC1Field) (q : Q) (i : Fin 2) :
    fullStar Phi q i 2 = dxPhiQ Phi 1 q i 0 := by
  have h : fullCol 2 = 0 := by decide
  have c1 : ¬ ((2 : Fin 8).val < 2) := by decide
  have c2 : (2 : Fin 8).val < 4 := by decide
  first
    | (simp only [fullStar]; rw [if_neg c1, if_pos c2, h]; done)
    | (simp [fullStar, fullCol]; done)

@[simp] theorem fullStar_column_three (Phi : ClosedC1Field) (q : Q) (i : Fin 2) :
    fullStar Phi q i 3 = dxPhiQ Phi 1 q i 1 := by
  have h : fullCol 3 = 1 := by decide
  have c1 : ¬ ((3 : Fin 8).val < 2) := by decide
  have c2 : (3 : Fin 8).val < 4 := by decide
  first
    | (simp only [fullStar]; rw [if_neg c1, if_pos c2, h]; done)
    | (simp [fullStar, fullCol]; done)

@[simp] theorem fullStar_column_four (Phi : ClosedC1Field) (q : Q) (i : Fin 2) :
    fullStar Phi q i 4 =
      (fullL0 * Phi.toFun (q : Ambient) - Phi.toFun (q : Ambient) * fullL0) i 0 := by
  have h : fullCol 4 = 0 := by decide
  have c1 : ¬ ((4 : Fin 8).val < 2) := by decide
  have c2 : ¬ ((4 : Fin 8).val < 4) := by decide
  have c3 : (4 : Fin 8).val < 6 := by decide
  first
    | (simp only [fullStar]; rw [if_neg c1, if_neg c2, if_pos c3, h]; done)
    | (simp [fullStar, fullCol]; done)

@[simp] theorem fullStar_column_five (Phi : ClosedC1Field) (q : Q) (i : Fin 2) :
    fullStar Phi q i 5 =
      (fullL0 * Phi.toFun (q : Ambient) - Phi.toFun (q : Ambient) * fullL0) i 1 := by
  have h : fullCol 5 = 1 := by decide
  have c1 : ¬ ((5 : Fin 8).val < 2) := by decide
  have c2 : ¬ ((5 : Fin 8).val < 4) := by decide
  have c3 : (5 : Fin 8).val < 6 := by decide
  first
    | (simp only [fullStar]; rw [if_neg c1, if_neg c2, if_pos c3, h]; done)
    | (simp [fullStar, fullCol]; done)

@[simp] theorem fullStar_column_six (Phi : ClosedC1Field) (q : Q) (i : Fin 2) :
    fullStar Phi q i 6 =
      (fullL1 * Phi.toFun (q : Ambient) - Phi.toFun (q : Ambient) * fullL1) i 0 := by
  have h : fullCol 6 = 0 := by decide
  have c1 : ¬ ((6 : Fin 8).val < 2) := by decide
  have c2 : ¬ ((6 : Fin 8).val < 4) := by decide
  have c3 : ¬ ((6 : Fin 8).val < 6) := by decide
  first
    | (simp only [fullStar]; rw [if_neg c1, if_neg c2, if_neg c3, h]; done)
    | (simp [fullStar, fullCol]; done)

@[simp] theorem fullStar_column_seven (Phi : ClosedC1Field) (q : Q) (i : Fin 2) :
    fullStar Phi q i 7 =
      (fullL1 * Phi.toFun (q : Ambient) - Phi.toFun (q : Ambient) * fullL1) i 1 := by
  have h : fullCol 7 = 1 := by decide
  have c1 : ¬ ((7 : Fin 8).val < 2) := by decide
  have c2 : ¬ ((7 : Fin 8).val < 4) := by decide
  have c3 : ¬ ((7 : Fin 8).val < 6) := by decide
  first
    | (simp only [fullStar]; rw [if_neg c1, if_neg c2, if_neg c3, h]; done)
    | (simp [fullStar, fullCol]; done)

/-! ### Signed-coordinate form of the continuity equation -/

theorem continuityEquation_iff_signedCoordinatePair {r : ℕ} (Dstar : DStar r)
    (g0 g1 : Spatial → Mat2) (path : MatrixPath r)
    (hD : ∀ Phi : ClosedC1Field, Continuous (Dstar Phi)) :
    ContinuityEquation Dstar g0 g1 path ↔
      ∀ Phi : ClosedC1Field,
        signedCoordinatePair r path.coords (testTriplet Dstar Phi) =
          endpointDifference g0 g1 Phi := by
  unfold ContinuityEquation
  refine forall_congr' fun Phi => ?_
  rw [signedCoordinatePair_eq_canonicalPair r path.coords (testTriplet Dstar Phi)
    (testTriplet_measurable Dstar Phi (hD Phi)) (testTriplet_bounded Dstar Phi (hD Phi))]

/-! ### Density representation -/

theorem continuityEquation_iff_integral_of_density {r : ℕ} (Dstar : DStar r)
    (g0 g1 : Spatial → Mat2) (path : MatrixPath r)
    (z : TransportCoord r → Q → ℝ)
    (hzM : ∀ c, Measurable (z c))
    (hzI : ∀ c, Integrable (z c) volumeQ)
    (hcoords : ∀ c, path.coords c = volumeQ.withDensityᵥ (z c))
    (hD : ∀ Phi : ClosedC1Field, Continuous (Dstar Phi)) :
    ContinuityEquation Dstar g0 g1 path ↔
      ∀ Phi : ClosedC1Field,
        (∫ q, weightedPair (fun _ => 1) (testTriplet Dstar Phi q) (fun c => z c q)
            ∂volumeQ) = endpointDifference g0 g1 Phi := by
  have hc : path.coords = fun c => volumeQ.withDensityᵥ (z c) := funext hcoords
  unfold ContinuityEquation
  refine forall_congr' fun Phi => ?_
  rw [hc, canonicalPair_withDensityᵥ r volumeQ z hzM hzI (testTriplet Dstar Phi)
    (testTriplet_measurable Dstar Phi (hD Phi)) (testTriplet_bounded Dstar Phi (hD Phi))]

#print axioms fullL0_isHermitian
#print axioms fullL1_isHermitian
#print axioms continuityEquation_iff_signedCoordinatePair
#print axioms continuityEquation_iff_integral_of_density

#print axioms wbSquared_le_action
#print axioms testTriplet_bounded
#print axioms testTriplet_mem_dualSet
#print axioms dual_bound_each_path
#print axioms continuous_KBstar
#print axioms continuous_fullStar
#print axioms ofReal_endpointDifference_le_wbSquared_KB
#print axioms ofReal_endpointDifference_le_wbSquared_full

end MatrixTransport

end
