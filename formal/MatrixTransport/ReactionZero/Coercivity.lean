import Mathlib

/-!
# Scalar algebra used by the reaction-zero coercivity estimate

These lemmas discharge the scalar quadratic step after a concrete dual test has been
constructed. They do not assume compactness and do not assert the full Radon transport theorem.
The actual matrix dual-test construction and continuity equation must supply their hypotheses.
-/

set_option autoImplicit false

namespace MatrixTransport.ReactionZero

/-- A quadratic Fenchel bound controls the square of its linear coefficient, including zero
quadratic coefficient. -/
theorem quadratic_dual_bound {p v E : ℝ} (hv : 0 ≤ v) (hE : 0 ≤ E)
    (h : ∀ s : ℝ, s * p - (s ^ 2 / 2) * v ≤ E) : p ^ 2 ≤ 2 * E * v := by
  by_cases hv0 : v = 0
  · have hp : p = 0 := by
      by_contra hp0
      have hh := h ((E + 1) / p)
      have hid : ((E + 1) / p) * p = E + 1 := by
        field_simp
      rw [hv0, mul_zero, sub_zero, hid] at hh
      linarith
    simp [hp, hv0]
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    have hh := h (p / v)
    have hid : (p / v) * p - ((p / v) ^ 2 / 2) * v = p ^ 2 / (2 * v) := by
      field_simp
      ring
    rw [hid] at hh
    have hmul := (div_le_iff₀ (by positivity : 0 < 2 * v)).mp hh
    nlinarith

/-- The continuity-equation time test and its reaction dual test give a mass bound whose
constant does not use an inverse eigenvalue of the reaction weight. -/
theorem mass_bound_of_time_dual {T m α E : ℝ} (hm : 0 ≤ m) (hE : 0 ≤ E)
    (h : ∀ s : ℝ, s * (T - m) - (s ^ 2 / 2) * α ^ 2 * T ≤ E) :
    T ≤ 2 * m + 2 * α ^ 2 * E := by
  by_cases ha : α = 0
  · have hp := quadratic_dual_bound (p := T - m) (v := 0) (by positivity) hE
      (fun s ↦ by simpa [ha] using h s)
    have heq : T = m := by nlinarith [sq_nonneg (T - m)]
    simp only [ha, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero]
    linarith
  · have ha2 : 0 < α ^ 2 := sq_pos_of_ne_zero ha
    have hh := h (1 / α ^ 2)
    have hid : (1 / α ^ 2) * (T - m) - ((1 / α ^ 2) ^ 2 / 2) * α ^ 2 * T =
        (T / 2 - m) / α ^ 2 := by
      field_simp
      ring
    rw [hid] at hh
    have hmul := (div_le_iff₀ ha2).mp hh
    nlinarith

/-- Uniform mass and action bounds turn a squared reaction bound into a linear weight bound. -/
theorem reaction_bound_of_square {r α E T C M : ℝ}
    (_hr : 0 ≤ r) (ha : 0 ≤ α) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hEC : E ≤ C) (hTM : T ≤ M) (h : r ^ 2 ≤ 2 * α ^ 2 * E * T) :
    r ≤ α * Real.sqrt (2 * C * M) := by
  have hC : 0 ≤ C := hE.trans hEC
  have hM : 0 ≤ M := hT.trans hTM
  have hET : E * T ≤ C * M := mul_le_mul hEC hTM hT hC
  have hCM : 0 ≤ 2 * C * M := by positivity
  have hs := Real.sq_sqrt hCM
  have hscaled := congrArg (fun x : ℝ ↦ α ^ 2 * x) hs
  have hb : 0 ≤ α * Real.sqrt (2 * C * M) := by positivity
  have hsq : r ^ 2 ≤ (α * Real.sqrt (2 * C * M)) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hET (by positivity : 0 ≤ 2 * α ^ 2)]
  nlinarith

#print axioms quadratic_dual_bound
#print axioms mass_bound_of_time_dual
#print axioms reaction_bound_of_square

end MatrixTransport.ReactionZero
