import MatrixTransport.EntrywiseBures.SqrtProvider
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
set_option autoImplicit false
noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace MatrixTransport.EntrywiseBures
/-- The canonical PSD square root, supplied by continuous functional calculus. -/
def canonicalPSDSqrt (n : ℕ) : PSDSqrt n where
  sqrt := CFC.sqrt
  posSemidef_sqrt A _ := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  sqrt_mul_sqrt A hA := CFC.sqrt_mul_sqrt_self A hA.nonneg
  eq_sqrt_of_mul_self A B hA hB hBB :=
    (CFC.sqrt_eq_iff A B hA.nonneg hB.nonneg).mpr hBB
#print axioms canonicalPSDSqrt
end MatrixTransport.EntrywiseBures
