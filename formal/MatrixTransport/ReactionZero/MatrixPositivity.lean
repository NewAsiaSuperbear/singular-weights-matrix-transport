import MatrixTransport.ReactionZero.PathCoercivity
import MatrixTransport.ReactionZero.MatrixSymmetry

/-!
# Positive semidefinite values of the actual mass measures

Every measurable-set matrix value is restored from its genuine joint RN density.
Integrating the nonnegative quadratic forms of a PSD density proves positivity of the
signed-measure matrix values; no absolute continuity or positivity premise is substituted
for the actual measure family.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.ReactionZero.MatrixPositivity

variable {n k : ℕ} {Q : Type*} [MeasurableSpace Q]

/-- The actual mass matrix value on a measurable set. -/
def massMeasureValue (μ : Coord n k → SignedMeasure Q) (B : Set Q) :
    Matrix (Fin n) (Fin n) ℝ := fun i j ↦ μ (Sum.inl (i, j)) B

/-- Each actual signed-coordinate set value is the set integral of its joint RN derivative. -/
theorem coordinate_apply_eq_setIntegral (μ : Coord n k → SignedMeasure Q)
    (c : Coord n k) (B : Set Q) (hB : MeasurableSet B) :
    μ c B = ∫ x in B, density μ x c ∂jointReference μ := by
  rw [← withDensityᵥ_rnDeriv_jointReference μ c,
    withDensityᵥ_apply (integrable_rnDeriv_jointReference μ c) hB]
  rfl

/-- Finite matrix quadratic forms commute with the genuine coordinate set integrals. -/
theorem quadraticForm_setIntegral {ρ : Measure Q}
    (A : Q → Matrix (Fin n) (Fin n) ℝ)
    (hAI : ∀ i j, Integrable (fun x ↦ A x i j) ρ) (B : Set Q) (v : Fin n → ℝ) :
    star v ⬝ᵥ ((fun i j ↦ ∫ x in B, A x i j ∂ρ) *ᵥ v) =
      ∫ x in B, star v ⬝ᵥ (A x *ᵥ v) ∂ρ := by
  have hi (i j : Fin n) : Integrable (fun x ↦ v i * (A x i j * v j)) (ρ.restrict B) :=
    ((hAI i j).restrict (s := B)).mul_const (v j) |>.const_mul (v i)
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_mul_const]

/-- PSD almost everywhere and genuine coordinate integrability imply PSD matrix set integrals. -/
theorem posSemidef_setIntegral {ρ : Measure Q}
    (A : Q → Matrix (Fin n) (Fin n) ℝ)
    (hAI : ∀ i j, Integrable (fun x ↦ A x i j) ρ)
    (hPSD : ∀ᵐ x ∂ρ, (A x).PosSemidef) (B : Set Q) :
    Matrix.PosSemidef (fun i j ↦ ∫ x in B, A x i j ∂ρ) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    rw [star_trivial]
    apply integral_congr_ae
    exact (ae_restrict_of_ae hPSD).mono fun _ hx ↦
      by simpa only [star_trivial] using hx.isHermitian.apply i j
  · intro v
    rw [quadraticForm_setIntegral A hAI B v]
    exact integral_nonneg_of_ae ((ae_restrict_of_ae hPSD).mono
      fun _ hx ↦ hx.dotProduct_mulVec_nonneg v)

/-- Finite original weighted action makes every measurable-set mass matrix positive
semidefinite. The original signed coordinate measures themselves are used in the conclusion. -/
theorem massMeasureValue_posSemidef (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : MassSymmetric μ) (hfin : action L1 L2 μ ≠ ⊤)
    (B : Set Q) (hB : MeasurableSet B) : (massMeasureValue μ B).PosSemidef := by
  have he : massMeasureValue μ B =
      fun i j ↦ ∫ x in B, mass (density μ x) i j ∂jointReference μ := by
    ext i j
    exact coordinate_apply_eq_setIntegral μ (Sum.inl (i, j)) B hB
  rw [he]
  exact posSemidef_setIntegral (fun x ↦ mass (density μ x))
    (fun i j ↦ integrable_rnDeriv_jointReference μ (Sum.inl (i, j)))
    (PathCoercivity.ae_mass_posSemidef L1 L2 μ hsym hfin) B

/-- Weak-star limits of genuine bounded fixed-action sublevels retain positive mass values.
This is a finite-action closure statement; it does not assume a positivity conclusion. -/
theorem massMeasureValue_posSemidef_of_bounded_weakStar
    [MetricSpace Q] [CompactSpace Q] [BorelSpace Q]
    (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (μ : ℕ → Coord n k → SignedMeasure Q) (ν : Coord n k → SignedMeasure Q)
    (hweak : SignedWeakStarTendsto μ ν) (hsym : ∀ a, MassSymmetric (μ a))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hE : ∀ a, action L1 L2 (μ a) ≤ C)
    (B : Set Q) (hB : MeasurableSet B) : (massMeasureValue ν B).PosSemidef := by
  have hlim : atTop.liminf (fun a ↦ action L1 L2 (μ a)) ≤ C :=
    liminf_le_of_frequently_le' (Filter.Eventually.of_forall hE).frequently
  have hfin : action L1 L2 ν ≠ ⊤ := ne_top_of_le_ne_top hC
    ((WeightedSet.action_le_liminf L1 L2 μ ν hweak).trans hlim)
  exact massMeasureValue_posSemidef L1 L2 ν
    (massSymmetric_of_signedWeakStar μ ν hweak hsym) hfin B hB

#print axioms coordinate_apply_eq_setIntegral
#print axioms quadraticForm_setIntegral
#print axioms posSemidef_setIntegral
#print axioms massMeasureValue_posSemidef
#print axioms massMeasureValue_posSemidef_of_bounded_weakStar

end MatrixTransport.ReactionZero.MatrixPositivity
