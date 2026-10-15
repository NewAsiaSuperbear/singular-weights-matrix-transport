import MatrixTransport.Separation
import MatrixTransport.Comparison
import MatrixTransport.Examples.KBObstruction
import MatrixTransport.ReactionZero.ClosedDomainTests
import MatrixTransport.EntrywiseBures.PathOperations

set_option autoImplicit false

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.NativeSeparation

open MatrixTransport

instance diskCompact : Fact (IsCompact disk) := ⟨disk_isCompact⟩

/-- Restriction of a neighborhood-C¹ field to its actual closed-domain jet. -/
def closedFieldJet (F : ClosedC1Field) : MatrixTransport.ReactionZero.ClosedDomain.ClosedC1Jet disk 2 := by
  refine MatrixTransport.ReactionZero.ClosedDomain.ClosedC1Jet.ofAmbient F.toFun
    ⟨fun p ↦ F.toFun p.val, F.continuous_Q⟩
    ⟨dtPhiQ F, continuous_dtPhiQ F⟩
    (fun j ↦ ⟨dxPhiQ F j, continuous_dxPhiQ F j⟩)
    (fun _ ↦ rfl) (fun p ↦ F.globallyHermitian p.val)
    (dtPhiQ_isHermitian F) (dxPhiQ_isHermitian F) ?_ ?_
  · intro p _
    have hl : HasDerivAt (MatrixTransport.ReactionZero.ClosedDomain.timeLine p.val) (1, 0) 0 := by
      convert ((hasDerivAt_const (0 : ℝ) p.val.1).add (hasDerivAt_id (0 : ℝ))).prodMk
        (hasDerivAt_const (0 : ℝ) p.val.2) using 1 <;> first | rfl | simp [MatrixTransport.ReactionZero.ClosedDomain.timeLine]
    have hd : HasFDerivAt F.toFun (fderiv ℝ F.toFun p.val) (MatrixTransport.ReactionZero.ClosedDomain.timeLine p.val 0) := by
      simpa [MatrixTransport.ReactionZero.ClosedDomain.timeLine] using (F.differentiableAt_QSet p.property).hasFDerivAt
    exact hd.comp_hasDerivAt 0 hl
  · intro p j _
    have hl : HasDerivAt (MatrixTransport.ReactionZero.ClosedDomain.spaceLine p.val j)
        (0, EuclideanSpace.single j (1 : ℝ)) 0 := by
      convert (hasDerivAt_const (0 : ℝ) p.val.1).prodMk
        ((hasDerivAt_const (0 : ℝ) p.val.2).add
          ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j (1 : ℝ))))
        using 1 <;> first | rfl | simp [MatrixTransport.ReactionZero.ClosedDomain.spaceLine]
    have hd : HasFDerivAt F.toFun (fderiv ℝ F.toFun p.val) (MatrixTransport.ReactionZero.ClosedDomain.spaceLine p.val j 0) := by
      simpa [MatrixTransport.ReactionZero.ClosedDomain.spaceLine] using (F.differentiableAt_QSet p.property).hasFDerivAt
    exact hd.comp_hasDerivAt 0 hl

@[simp] theorem closedFieldJet_value (F : ClosedC1Field) (p : Q) :
    (closedFieldJet F).value p = F.toFun p.val := rfl

@[simp] theorem closedFieldJet_dt (F : ClosedC1Field) (p : Q) :
    (closedFieldJet F).dt p = dtPhiQ F p := rfl

@[simp] theorem closedFieldJet_dx (F : ClosedC1Field) (j : Fin 2) (p : Q) :
    (closedFieldJet F).dx j p = dxPhiQ F j p := rfl

/-- Both concrete and general unit-weight costs use precisely the same dual set. -/
theorem dualSet_identity (r : ℕ) : MatrixTransport.ReactionZero.dualSet (1 : Matrix (Fin r) (Fin r) ℝ)
    (1 : Mat2) = MatrixTransport.dualSet r := by
  ext a
  simp only [MatrixTransport.ReactionZero.dualSet, MatrixTransport.dualSet, LocalDualConstraint,
    MatrixTransport.ReactionZero.gram, Matrix.mul_one]
  have hm : MatrixTransport.ReactionZero.mass a = MatrixTransport.mass a := rfl
  have hf : MatrixTransport.ReactionZero.flux a = MatrixTransport.flux a := rfl
  have hr : MatrixTransport.ReactionZero.reaction a = MatrixTransport.reaction a := rfl
  simp only [Set.mem_setOf_eq]
  rw [hm, hf, hr]
  simp only [neg_add, sub_eq_add_neg]

theorem cost_identity (r : ℕ) (a : TransportCoord r → ℝ) :
    MatrixTransport.ReactionZero.cost (1 : Matrix (Fin r) (Fin r) ℝ) (1 : Mat2) a = matrixCost r a := by
  unfold MatrixTransport.ReactionZero.cost matrixCost
  rw [dualSet_identity]

theorem action_identity (r : ℕ) (μ : TransportCoord r → SignedMeasure Q) :
    MatrixTransport.ReactionZero.action (1 : Matrix (Fin r) (Fin r) ℝ) (1 : Mat2) μ = matrixAction r μ := by
  unfold MatrixTransport.ReactionZero.action matrixAction MatrixTransport.ReactionZero.density matrixDensity
  simp only [cost_identity]

/-- The zero-order commutator blocks in the concrete full operator. -/
def fullZeroLinear : Mat2 →ₗ[ℝ] Flux 8 where
  toFun X := Matrix.of fun i k ↦
    if k.val < 4 then 0 else if k.val < 6 then
      (fullL0 * X - X * fullL0) i (fullCol k)
    else (fullL1 * X - X * fullL1) i (fullCol k)
  map_add' X Y := by
    ext i k
    fin_cases k <;> simp [Matrix.of_apply, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, Matrix.sub_apply,
      Matrix.add_apply] <;> ring
  map_smul' r X := by
    ext i k
    fin_cases k <;> simp [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
      Matrix.sub_apply, RingHom.id_apply] <;> ring

/-- The two ordinary-derivative blocks in the concrete full operator. -/
def fullPartialLinear (j : Fin 2) : Mat2 →ₗ[ℝ] Flux 8 where
  toFun X := Matrix.of fun i k ↦
    if k.val < 2 then if j = 0 then X i (fullCol k) else 0
    else if k.val < 4 then if j = 1 then X i (fullCol k) else 0 else 0
  map_add' X Y := by
    ext i k
    fin_cases j <;> fin_cases k <;> simp [Matrix.of_apply, Pi.add_apply, Matrix.add_apply]
  map_smul' r X := by
    ext i k
    fin_cases j <;> fin_cases k <;> simp [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]

@[simp] theorem fullZeroLinear_apply (X : Mat2) (i : Fin 2) (k : Fin 8) :
    fullZeroLinear X i k =
      if k.val < 4 then 0 else if k.val < 6 then
        (fullL0 * X - X * fullL0) i (fullCol k)
      else (fullL1 * X - X * fullL1) i (fullCol k) := rfl

@[simp] theorem fullPartialLinear_apply (j : Fin 2) (X : Mat2) (i : Fin 2) (k : Fin 8) :
    fullPartialLinear j X i k =
      if k.val < 2 then if j = 0 then X i (fullCol k) else 0
      else if k.val < 4 then if j = 1 then X i (fullCol k) else 0 else 0 := rfl

/-- The full matrix-flux operator in the original general operator structure. -/
def fullOperator : MatrixTransport.ReactionZero.ClosedDomain.AdjointOperator 2 2 8 where
  D0 := fullZeroLinear.toContinuousLinearMap
  Dj j := (fullPartialLinear j).toContinuousLinearMap
  D0_one := by
    change fullZeroLinear (1 : Mat2) = 0
    ext i k
    change (if k.val < 4 then 0 else if k.val < 6 then
      (fullL0 * 1 - 1 * fullL0) i (fullCol k)
      else (fullL1 * 1 - 1 * fullL1) i (fullCol k)) = 0
    simp

theorem fullOperator_on_closedField (F : ClosedC1Field) (p : Q) :
    fullOperator.apply (closedFieldJet F) p = fullStar F p := by
  ext i k
  change (fullZeroLinear (F.toFun p.val) +
    ∑ j : Fin 2, fullPartialLinear j (dxPhiQ F j p)) i k = fullStar F p i k
  simp only [Fin.sum_univ_two]
  erw [Matrix.add_apply, Matrix.add_apply]
  rw [fullZeroLinear_apply, fullPartialLinear_apply, fullPartialLinear_apply]
  fin_cases k <;> simp [fullStar]

theorem kbOperator_on_closedField (F : ClosedC1Field) (p : Q) :
    LiZouTransport.Examples.kbOp.apply (closedFieldJet F) p = KBstar F p := by
  ext i k
  erw [LiZouTransport.Examples.kbOp_apply]
  rfl

#print axioms closedFieldJet
#print axioms dualSet_identity
#print axioms cost_identity
#print axioms action_identity
#print axioms fullOperator
#print axioms fullOperator_on_closedField
#print axioms kbOperator_on_closedField

end LiZouTransport.NativeSeparation
