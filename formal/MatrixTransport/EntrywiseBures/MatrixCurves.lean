import MatrixTransport.EntrywiseBures.TimeRescaling
import MatrixTransport.Paper.NativeSeparationTime

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.Reaction
open MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures
variable {n : ℕ}

/-- Matrix product differentiation, proved entrywise from the scalar product rule. -/
theorem matrix_product_deriv {X Y : ℝ → RMat n} {X' Y' : RMat n} {s : ℝ}
    (hX : HasDerivAt X X' s) (hY : HasDerivAt Y Y' s) :
    HasDerivAt (fun t ↦ X t * Y t) (X' * Y s + X s * Y') s := by
  refine hasDerivAt_of_entries fun i j ↦ ?_
  have h := HasDerivAt.fun_sum fun k (_ : k ∈ Finset.univ) ↦
    (hasDerivAt_entry hX i k).mul (hasDerivAt_entry hY k j)
  convert h using 1 <;> try rfl
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

theorem matrix_transpose_deriv {X : ℝ → RMat n} {X' : RMat n} {s : ℝ}
    (hX : HasDerivAt X X' s) : HasDerivAt (fun t ↦ (X t)ᵀ) X'ᵀ s :=
  hasDerivAt_of_entries fun i j ↦ hasDerivAt_entry hX j i

def factorPoint (P Δ : RMat n) (s : ℝ) : RMat n := P + s • Δ

def factorMass (H P Δ : RMat n) (s : ℝ) : RMat n :=
  MatrixTransport.ReactionZero.gram (factorPoint P (H * Δ) s)

def factorRate (H P Δ : RMat n) (s : ℝ) : RMat n :=
  (2 : ℝ) • ((factorPoint P (H * Δ) s) * Δᵀ * H)

def factorMassDeriv (H P Δ : RMat n) (s : ℝ) : RMat n :=
  (H * Δ) * (factorPoint P (H * Δ) s)ᵀ + (factorPoint P (H * Δ) s) * (H * Δ)ᵀ

theorem factorPoint_deriv (P Δ : RMat n) (s : ℝ) :
    HasDerivAt (factorPoint P Δ) Δ s := by
  convert ((hasDerivAt_const s P).add ((hasDerivAt_id s).smul_const Δ)) using 1 <;>
    first | rfl | simp

theorem factorMass_deriv (H P Δ : RMat n) (s : ℝ) :
    HasDerivAt (factorMass H P Δ) (factorMassDeriv H P Δ s) s := by
  have h := factorPoint_deriv P (H * Δ) s
  exact matrix_product_deriv h (matrix_transpose_deriv h)

theorem continuous_factorMass (H P Δ : RMat n) : Continuous (factorMass H P Δ) :=
  continuous_iff_continuousAt.mpr fun s ↦ (factorMass_deriv H P Δ s).continuousAt

theorem continuous_factorRate (H P Δ : RMat n) : Continuous (factorRate H P Δ) := by
  unfold factorRate
  have hc : Continuous (factorPoint P (H * Δ)) :=
    continuous_iff_continuousAt.mpr fun s ↦ (factorPoint_deriv P (H * Δ) s).continuousAt
  exact ((hc.matrix_mul continuous_const).matrix_mul continuous_const).const_smul (2 : ℝ)

theorem continuous_factorMassDeriv (H P Δ : RMat n) :
    Continuous (factorMassDeriv H P Δ) := by
  have hc : Continuous (factorPoint P (H * Δ)) :=
    continuous_iff_continuousAt.mpr fun s ↦ (factorPoint_deriv P (H * Δ) s).continuousAt
  unfold factorMassDeriv
  exact (continuous_const.matrix_mul hc.matrix_transpose).add
    (hc.matrix_mul continuous_const)

theorem frob_transpose_right (A B : RMat n) (hA : Aᵀ = A) :
    MatrixTransport.ReactionZero.frob A Bᵀ = MatrixTransport.ReactionZero.frob A B := by
  unfold MatrixTransport.ReactionZero.frob
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hs : A j i = A i j := congrFun (congrFun hA i) j
  simpa only [Matrix.transpose_apply, hs]

theorem frob_factorMassDeriv (H P Δ A : RMat n) (hH : Hᵀ = H) (hA : Aᵀ = A) (s : ℝ) :
    MatrixTransport.ReactionZero.frob A (factorMassDeriv H P Δ s) =
      MatrixTransport.ReactionZero.frob A (factorRate H P Δ s) := by
  let W := factorPoint P (H * Δ) s
  let B := W * Δᵀ * H
  have he : factorMassDeriv H P Δ s = Bᵀ + B := by
    simp only [B, W, factorMassDeriv, Matrix.transpose_mul, Matrix.transpose_transpose,
      hH, Matrix.mul_assoc]
  rw [he, factorRate]
  change MatrixTransport.ReactionZero.frob A (Bᵀ + B) =
    MatrixTransport.ReactionZero.frob A ((2 : ℝ) • B)
  have hadd : MatrixTransport.ReactionZero.frob A (Bᵀ + B) =
      MatrixTransport.ReactionZero.frob A Bᵀ + MatrixTransport.ReactionZero.frob A B := by
    simp [MatrixTransport.ReactionZero.frob, mul_add, Finset.sum_add_distrib]
  rw [hadd, frob_transpose_right A B hA, MatrixTransport.ReactionZero.frob_smul_right]
  ring

#print axioms matrix_product_deriv
#print axioms factorMass_deriv
#print axioms frob_factorMassDeriv
end LiZouTransport.Reaction
