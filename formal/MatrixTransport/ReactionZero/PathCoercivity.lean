import MatrixTransport.ReactionZero.PointwiseBounds
import MatrixTransport.ReactionZero.WeightedSet
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Coercivity of actual finite signed-measure matrix paths

The path trace, action and coordinate total variations are genuine RN/Jordan measure quantities.
The lemmas derive bounds from symmetry of the original mass coordinate measures and finite
weighted action. The time-test identity is a premise supplied by the concrete continuity
equation; a mass or variation bound is never inserted as an assumption.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Matrix

namespace MatrixTransport.ReactionZero.PathCoercivity

variable {n k : ℕ} {Q : Type*} [MeasurableSpace Q]

/-- Integrated trace of the actual mass RN density against the joint reference. -/
def pathTrace (μ : Coord n k → SignedMeasure Q) : ℝ :=
  ∫ x, (mass (density μ x)).trace ∂jointReference μ

theorem integrable_mass_trace (μ : Coord n k → SignedMeasure Q) :
    Integrable (fun x ↦ (mass (density μ x)).trace) (jointReference μ) :=
  integrable_finsetSum _ fun i _ ↦ integrable_rnDeriv_jointReference μ (Sum.inl (i, i))

theorem integrable_reaction_trace (μ : Coord n k → SignedMeasure Q) :
    Integrable (fun x ↦ (reaction (density μ x)).trace) (jointReference μ) :=
  integrable_finsetSum _ fun i _ ↦
    integrable_rnDeriv_jointReference μ (Sum.inr (Sum.inr (i, i)))

theorem mass_density_isHermitian (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i))) (x : Q) :
    (mass (density μ x)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star ((μ (Sum.inl (j, i))).rnDeriv (jointReference μ) x) =
    (μ (Sum.inl (i, j))).rnDeriv (jointReference μ) x
  rw [star_trivial, hsym j i]

theorem ae_cost_ne_top (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hfin : action L1 L2 μ ≠ ⊤) :
    ∀ᵐ x ∂jointReference μ, cost L1 L2 (density μ x) ≠ ⊤ :=
  (ae_lt_top (measurable_cost_density L1 L2 μ) hfin).mono fun _ h ↦ h.ne

theorem ae_mass_posSemidef (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) :
    ∀ᵐ x ∂jointReference μ, (mass (density μ x)).PosSemidef :=
  (ae_cost_ne_top L1 L2 μ hfin).mono fun x hx ↦
    mass_posSemidef_of_cost_ne_top L1 L2 (density μ x) (mass_density_isHermitian μ hsym x) hx

theorem pathTrace_nonneg (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) : 0 ≤ pathTrace μ :=
  integral_nonneg_of_ae ((ae_mass_posSemidef L1 L2 μ hsym hfin).mono
    fun _ hx ↦ trace_nonneg_of_posSemidef hx)

theorem integrable_cost_toReal (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hfin : action L1 L2 μ ≠ ⊤) :
    Integrable (fun x ↦ (cost L1 L2 (density μ x)).toReal) (jointReference μ) :=
  integrable_toReal_of_lintegral_ne_top (measurable_cost_density L1 L2 μ).aemeasurable hfin

theorem integral_cost_toReal (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hfin : action L1 L2 μ ≠ ⊤) :
    (∫ x, (cost L1 L2 (density μ x)).toReal ∂jointReference μ) = (action L1 L2 μ).toReal :=
  integral_toReal (measurable_cost_density L1 L2 μ).aemeasurable
    (ae_lt_top (measurable_cost_density L1 L2 μ) hfin)

/-- A proved RN variation identity for each actual coordinate measure. -/
theorem coordinateTV_eq_integral_abs (μ : Coord n k → SignedMeasure Q) (c : Coord n k) :
    ((μ c).totalVariation univ).toReal = ∫ x, |density μ x c| ∂jointReference μ := by
  rw [SignedMeasure.totalVariation_eq_variation]
  have h := Measure.variation_withDensityᵥ (integrable_rnDeriv_jointReference μ c)
  rw [withDensityᵥ_rnDeriv_jointReference μ c] at h
  rw [h, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simpa only [Real.norm_eq_abs, density] using
    (integral_norm_eq_lintegral_enorm
      (integrable_rnDeriv_jointReference μ c).aestronglyMeasurable).symm

/-- A pointwise squared estimate supplies every scalar quadratic Fenchel inequality. -/
theorem linear_quadratic_of_square {p V E : ℝ} (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hp : p ^ 2 ≤ 2 * E * V) (s : ℝ) : s * p - (s ^ 2 / 2) * V ≤ E := by
  by_cases hV0 : V = 0
  · have hp0 : p = 0 := by nlinarith [sq_nonneg p]
    simp [hV0, hp0, hE]
  · have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
    have hs := sq_nonneg (s * V - p)
    have hm : (s * p - (s ^ 2 / 2) * V - E) * V ≤ 0 := by nlinarith
    have hc := nonpos_of_mul_nonpos_left hm hVpos
    linarith

/-- Integrating the scalar quadratic inequalities yields a true integral Cauchy bound without
adding any compactness, coercivity or L2 integrability assumption.
-/
theorem integral_abs_square_bound {ρ : Measure Q} {r t e : Q → ℝ} {κ : ℝ}
    (hrI : Integrable r ρ) (htI : Integrable t ρ) (heI : Integrable e ρ)
    (hκ : 0 ≤ κ) (ht : ∀ᵐ x ∂ρ, 0 ≤ t x) (he : ∀ᵐ x ∂ρ, 0 ≤ e x)
    (hb : ∀ᵐ x ∂ρ, r x ^ 2 ≤ 2 * e x * (t x * κ)) :
    (∫ x, |r x| ∂ρ) ^ 2 ≤ 2 * (∫ x, e x ∂ρ) * ((∫ x, t x ∂ρ) * κ) := by
  have hT : 0 ≤ ∫ x, t x ∂ρ := integral_nonneg_of_ae ht
  have hE : 0 ≤ ∫ x, e x ∂ρ := integral_nonneg_of_ae he
  apply quadratic_dual_bound (mul_nonneg hT hκ) hE
  intro s
  have hpoint : ∀ᵐ x ∂ρ, s * |r x| - (s ^ 2 / 2) * (t x * κ) ≤ e x := by
    filter_upwards [ht, he, hb] with x htx hex hbx
    apply linear_quadratic_of_square (mul_nonneg htx hκ) hex
    simpa only [sq_abs] using hbx
  have hi := integral_mono_ae
    ((hrI.abs.const_mul s).sub ((htI.mul_const κ).const_mul (s ^ 2 / 2))) heI hpoint
  change (∫ x, s * |r x| - (s ^ 2 / 2) * (t x * κ) ∂ρ) ≤ ∫ x, e x ∂ρ at hi
  simpa only [integral_sub (hrI.abs.const_mul s)
    ((htI.mul_const κ).const_mul (s ^ 2 / 2)), integral_const_mul, integral_mul_const] using hi

/-- Actual mass coordinate total variation is controlled by the integrated PSD trace. -/
theorem massTV_le_pathTrace (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) (i j : Fin n) :
    ((μ (Sum.inl (i, j))).totalVariation univ).toReal ≤ pathTrace μ := by
  rw [coordinateTV_eq_integral_abs]
  apply integral_mono_ae (integrable_rnDeriv_jointReference μ _).abs
    (integrable_mass_trace μ)
  exact (ae_mass_posSemidef L1 L2 μ hsym hfin).mono fun _ hx ↦
    abs_apply_le_trace_of_posSemidef hx i j

/-- The genuine reaction total variation obeys the weighted action/trace square estimate. -/
theorem reactionTV_sq_le (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) (i j : Fin n) :
    ((μ (Sum.inr (Sum.inr (i, j)))).totalVariation univ).toReal ^ 2 ≤
      2 * (action L1 L2 μ).toReal * (pathTrace μ * frobeniusSq L2) := by
  rw [coordinateTV_eq_integral_abs]
  have h := integral_abs_square_bound (integrable_rnDeriv_jointReference μ _)
    (integrable_mass_trace μ) (integrable_cost_toReal L1 L2 μ hfin)
    (frobeniusSq_nonneg L2)
    ((ae_mass_posSemidef L1 L2 μ hsym hfin).mono fun _ hx ↦
      trace_nonneg_of_posSemidef hx)
    (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
    ((ae_cost_ne_top L1 L2 μ hfin).mono fun x hx ↦
      reaction_entry_sq_le_trace L1 L2 (density μ x)
        (mass_density_isHermitian μ hsym x) hx i j)
  simpa only [integral_cost_toReal L1 L2 μ hfin, pathTrace, density] using h

/-- The flux estimate is valid for arbitrary rectangular flux coordinates and fixed weights. -/
theorem fluxTV_sq_le (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) (i : Fin n) (j : Fin k) :
    ((μ (Sum.inr (Sum.inl (i, j)))).totalVariation univ).toReal ^ 2 ≤
      2 * (action L1 L2 μ).toReal * (pathTrace μ * frobeniusSq L1) := by
  rw [coordinateTV_eq_integral_abs]
  have h := integral_abs_square_bound (integrable_rnDeriv_jointReference μ _)
    (integrable_mass_trace μ) (integrable_cost_toReal L1 L2 μ hfin)
    (frobeniusSq_nonneg L1)
    ((ae_mass_posSemidef L1 L2 μ hsym hfin).mono fun _ hx ↦
      trace_nonneg_of_posSemidef hx)
    (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
    ((ae_cost_ne_top L1 L2 μ hfin).mono fun x hx ↦
      flux_entry_sq_le_trace L1 L2 (density μ x)
        (mass_density_isHermitian μ hsym x) hx i j)
  simpa only [integral_cost_toReal L1 L2 μ hfin, pathTrace, density] using h

theorem integrable_time_reaction_trace (μ : Coord n k → SignedMeasure Q) (w : Q → ℝ)
    (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    Integrable (fun x ↦ w x * (reaction (density μ x)).trace) (jointReference μ) := by
  exact (integrable_reaction_trace μ).bdd_mul hwM.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hw x).1]; exact (hw x).2)

/-- The time CE's diagonal signed pairing is exactly the integrated reaction trace pairing. -/
theorem time_reaction_pair_eq_integral (μ : Coord n k → SignedMeasure Q) (w : Q → ℝ)
    (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    (∑ i, signedPair (μ (Sum.inr (Sum.inr (i, i)))) w) =
      ∫ x, w x * (reaction (density μ x)).trace ∂jointReference μ := by
  have hb : ∃ C : ℝ, ∀ x, |w x| ≤ C :=
    ⟨1, fun x ↦ by rw [abs_of_nonneg (hw x).1]; exact (hw x).2⟩
  have ht (i : Fin n) : Integrable
      (fun x ↦ w x * density μ x (Sum.inr (Sum.inr (i, i)))) (jointReference μ) :=
    (integrable_rnDeriv_jointReference μ _).bdd_mul hwM.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hw x).1]; exact (hw x).2)
  simp_rw [signedPair_rnDeriv (jointReference μ) _
    (absolutelyContinuous_jointReference μ _) hwM hb]
  change (∑ i, ∫ x, w x * density μ x (Sum.inr (Sum.inr (i, i))) ∂jointReference μ) = _
  rw [← integral_finsetSum Finset.univ (fun i _ ↦ ht i)]
  congr 1
  funext x
  rw [Matrix.trace, Finset.mul_sum]
  rfl

/-- Every scalar reaction time-test inequality follows from the original local cost. -/
theorem time_scalar_dual (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) (w : Q → ℝ)
    (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) (s : ℝ) :
    s * (∑ i, signedPair (μ (Sum.inr (Sum.inr (i, i)))) w) -
      (s ^ 2 / 2) * frobeniusSq L2 * pathTrace μ ≤ (action L1 L2 μ).toReal := by
  have hp : ∀ᵐ x ∂jointReference μ,
      s * (w x * (reaction (density μ x)).trace) -
        (s ^ 2 / 2) * (frobeniusSq L2 * (mass (density μ x)).trace) ≤
        (cost L1 L2 (density μ x)).toReal := by
    filter_upwards [ae_cost_ne_top L1 L2 μ hfin,
      ae_mass_posSemidef L1 L2 μ hsym hfin] with x hcx hGx
    have htx := trace_nonneg_of_posSemidef hGx
    have hwx : w x ^ 2 ≤ 1 := by nlinarith [(hw x).1, (hw x).2]
    have hcoef := frob_gram_scalar_mul_le L1 L2 (density μ x) hcx (w x)
    have hcoef' : frob (gram ((w x • (1 : Matrix (Fin n) (Fin n) ℝ)) * L2))
        (mass (density μ x)) ≤ frobeniusSq L2 * (mass (density μ x)).trace := by
      calc _ ≤ w x ^ 2 * frobeniusSq L2 * (mass (density μ x)).trace := hcoef
           _ ≤ 1 * frobeniusSq L2 * (mass (density μ x)).trace :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hwx (frobeniusSq_nonneg L2)) htx
           _ = _ := by ring
    have hf := reaction_fenchel_le_toReal L1 L2 (density μ x) hcx s
      (w x • (1 : Matrix (Fin n) (Fin n) ℝ))
    rw [frob_smul_left, pw_frob_one_left] at hf
    have hh := mul_le_mul_of_nonneg_left hcoef' (show 0 ≤ s ^ 2 / 2 by positivity)
    linarith
  have hi := integral_mono_ae
    (((integrable_time_reaction_trace μ w hwM hw).const_mul s).sub
      ((integrable_mass_trace μ).const_mul (s ^ 2 / 2 * frobeniusSq L2)))
    (integrable_cost_toReal L1 L2 μ hfin) (by
      filter_upwards [hp] with x hx
      change s * (w x * (reaction (density μ x)).trace) -
        (s ^ 2 / 2 * frobeniusSq L2) * (mass (density μ x)).trace ≤ _
      simpa only [mul_assoc] using hx)
  change (∫ x, s * (w x * (reaction (density μ x)).trace) -
      (s ^ 2 / 2 * frobeniusSq L2) * (mass (density μ x)).trace ∂jointReference μ) ≤
      ∫ x, (cost L1 L2 (density μ x)).toReal ∂jointReference μ at hi
  rw [integral_sub ((integrable_time_reaction_trace μ w hwM hw).const_mul s)
      ((integrable_mass_trace μ).const_mul (s ^ 2 / 2 * frobeniusSq L2)),
    integral_const_mul, integral_const_mul, integral_cost_toReal L1 L2 μ hfin,
    ← time_reaction_pair_eq_integral μ w hwM hw] at hi
  exact hi

/-- Complete mass coercivity, with only the actual CE time-test identity as the extra premise. -/
theorem pathTrace_bound_of_time_identity (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) (w : Q → ℝ)
    (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (m0 : ℝ) (hm0 : 0 ≤ m0)
    (hCE : pathTrace μ = m0 + ∑ i, signedPair (μ (Sum.inr (Sum.inr (i, i)))) w) :
    pathTrace μ ≤ 2 * m0 + 2 * frobeniusSq L2 * (action L1 L2 μ).toReal := by
  have hs := mass_bound_of_time_dual (α := Real.sqrt (frobeniusSq L2)) hm0
    (show 0 ≤ (action L1 L2 μ).toReal from ENNReal.toReal_nonneg) (fun s ↦ by
      have h := time_scalar_dual L1 L2 μ hsym hfin w hwM hw s
      rw [Real.sq_sqrt (frobeniusSq_nonneg L2)]
      have hp : pathTrace μ - m0 = ∑ i, signedPair (μ (Sum.inr (Sum.inr (i, i)))) w := by
        linarith [hCE]
      rw [hp]
      simpa only [mul_assoc, div_mul_eq_mul_div] using h)
  simpa only [Real.sq_sqrt (frobeniusSq_nonneg L2)] using hs

/-- A uniform action and trace sublevel supplies an explicit reaction coordinate TV bound. -/
theorem reactionTV_le_sqrt (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) (C M : ℝ)
    (hE : (action L1 L2 μ).toReal ≤ C) (hT : pathTrace μ ≤ M) (i j : Fin n) :
    ((μ (Sum.inr (Sum.inr (i, j)))).totalVariation univ).toReal ≤
      Real.sqrt (frobeniusSq L2) * Real.sqrt (2 * C * M) := by
  apply reaction_bound_of_square ENNReal.toReal_nonneg (Real.sqrt_nonneg _)
    ENNReal.toReal_nonneg (pathTrace_nonneg L1 L2 μ hsym hfin) hE hT
  rw [Real.sq_sqrt (frobeniusSq_nonneg L2)]
  convert reactionTV_sq_le L1 L2 μ hsym hfin i j using 1
  ring

theorem fluxTV_le_sqrt (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) (C M : ℝ)
    (hE : (action L1 L2 μ).toReal ≤ C) (hT : pathTrace μ ≤ M)
    (i : Fin n) (j : Fin k) :
    ((μ (Sum.inr (Sum.inl (i, j)))).totalVariation univ).toReal ≤
      Real.sqrt (frobeniusSq L1) * Real.sqrt (2 * C * M) := by
  apply reaction_bound_of_square ENNReal.toReal_nonneg (Real.sqrt_nonneg _)
    ENNReal.toReal_nonneg (pathTrace_nonneg L1 L2 μ hsym hfin) hE hT
  rw [Real.sq_sqrt (frobeniusSq_nonneg L1)]
  convert fluxTV_sq_le L1 L2 μ hsym hfin i j using 1
  ring

/-- An explicit common TV bound for all three coordinate blocks. -/
def coordinateTVBound (C M K1 K2 : ℝ) : ℝ :=
  max M (max (Real.sqrt K1 * Real.sqrt (2 * C * M))
    (Real.sqrt K2 * Real.sqrt (2 * C * M)))

theorem coordinateTVBound_nonneg (C M K1 K2 : ℝ) : 0 ≤ coordinateTVBound C M K1 K2 :=
  (mul_nonneg (Real.sqrt_nonneg K1) (Real.sqrt_nonneg _)).trans
    ((le_max_left _ _).trans (le_max_right _ _))

theorem coordinateTV_le_bound (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) (C M K1 K2 : ℝ)
    (hE : (action L1 L2 μ).toReal ≤ C) (hT : pathTrace μ ≤ M)
    (hL1 : frobeniusSq L1 ≤ K1) (hL2 : frobeniusSq L2 ≤ K2) (c : Coord n k) :
    ((μ c).totalVariation univ).toReal ≤ coordinateTVBound C M K1 K2 := by
  rcases c with ⟨i, j⟩ | (⟨i, j⟩ | ⟨i, j⟩)
  · exact (massTV_le_pathTrace L1 L2 μ hsym hfin i j).trans
      (hT.trans (le_max_left _ _))
  · have h := fluxTV_le_sqrt L1 L2 μ hsym hfin C M hE hT i j
    exact h.trans ((mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hL1)
      (Real.sqrt_nonneg _)).trans ((le_max_left _ _).trans (le_max_right _ _)))
  · have h := reactionTV_le_sqrt L1 L2 μ hsym hfin C M hE hT i j
    exact h.trans ((mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hL2)
      (Real.sqrt_nonneg _)).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem coordinateTV_le_bound_ennreal (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) (C M K1 K2 : ℝ)
    (hE : (action L1 L2 μ).toReal ≤ C) (hT : pathTrace μ ≤ M)
    (hL1 : frobeniusSq L1 ≤ K1) (hL2 : frobeniusSq L2 ≤ K2) (c : Coord n k) :
    (μ c).totalVariation univ ≤ ENNReal.ofReal (coordinateTVBound C M K1 K2) := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (coordinateTVBound_nonneg C M K1 K2)).2
  exact coordinateTV_le_bound L1 L2 μ hsym hfin C M K1 K2 hE hT hL1 hL2 c

/-- Total joint-reference mass is the true sum of coordinate total variations. -/
theorem jointReference_mass_toReal_eq (μ : Coord n k → SignedMeasure Q) :
    (jointReference μ univ).toReal = ∑ c, ((μ c).totalVariation univ).toReal := by
  rw [jointReference, Measure.finsetSum_apply _ _ univ,
    ENNReal.toReal_sum (fun c _ ↦ measure_ne_top _ _)]

/-- The joint reference is uniformly bounded on the actual weighted action/trace sublevel. -/
theorem jointReference_mass_le_bound (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (hfin : action L1 L2 μ ≠ ⊤) (C M K1 K2 : ℝ)
    (hE : (action L1 L2 μ).toReal ≤ C) (hT : pathTrace μ ≤ M)
    (hL1 : frobeniusSq L1 ≤ K1) (hL2 : frobeniusSq L2 ≤ K2) :
    (jointReference μ univ).toReal ≤
      Fintype.card (Coord n k) * coordinateTVBound C M K1 K2 := by
  rw [jointReference_mass_toReal_eq]
  calc ∑ c, ((μ c).totalVariation univ).toReal
      ≤ ∑ _c : Coord n k, coordinateTVBound C M K1 K2 :=
        Finset.sum_le_sum fun c _ ↦
          coordinateTV_le_bound L1 L2 μ hsym hfin C M K1 K2 hE hT hL1 hL2 c
      _ = _ := by simp

/-- Vanishing reaction weights force each actual reaction coordinate TV to vanish. -/
theorem reactionTV_toReal_tendsto_zero (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : ℕ → Matrix (Fin n) (Fin n) ℝ) (μ : ℕ → Coord n k → SignedMeasure Q)
    (hsym : ∀ a i j, μ a (Sum.inl (i, j)) = μ a (Sum.inl (j, i)))
    (hfin : ∀ a, action L1 (L2 a) (μ a) ≠ ⊤) (C M : ℝ)
    (hE : ∀ a, (action L1 (L2 a) (μ a)).toReal ≤ C)
    (hT : ∀ a, pathTrace (μ a) ≤ M)
    (hL2 : Tendsto (fun a ↦ frobeniusSq (L2 a)) atTop (𝓝 0)) (i j : Fin n) :
    Tendsto (fun a ↦ ((μ a (Sum.inr (Sum.inr (i, j)))).totalVariation univ).toReal)
      atTop (𝓝 0) := by
  have hsq : Tendsto (fun a ↦ Real.sqrt (frobeniusSq (L2 a))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hL2
  have hb : Tendsto (fun a ↦ Real.sqrt (frobeniusSq (L2 a)) * Real.sqrt (2 * C * M))
      atTop (𝓝 0) := by simpa using hsq.mul_const (Real.sqrt (2 * C * M))
  exact squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg)
    (fun a ↦ reactionTV_le_sqrt L1 (L2 a) (μ a) (hsym a) (hfin a) C M
      (hE a) (hT a) i j) hb

theorem reactionTV_tendsto_zero (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : ℕ → Matrix (Fin n) (Fin n) ℝ) (μ : ℕ → Coord n k → SignedMeasure Q)
    (hsym : ∀ a i j, μ a (Sum.inl (i, j)) = μ a (Sum.inl (j, i)))
    (hfin : ∀ a, action L1 (L2 a) (μ a) ≠ ⊤) (C M : ℝ)
    (hE : ∀ a, (action L1 (L2 a) (μ a)).toReal ≤ C)
    (hT : ∀ a, pathTrace (μ a) ≤ M)
    (hL2 : Tendsto (fun a ↦ frobeniusSq (L2 a)) atTop (𝓝 0)) (i j : Fin n) :
    Tendsto (fun a ↦ (μ a (Sum.inr (Sum.inr (i, j)))).totalVariation univ)
      atTop (𝓝 0) :=
  (ENNReal.tendsto_toReal_zero_iff (fun _ ↦ measure_ne_top _ _)).1
    (reactionTV_toReal_tendsto_zero L1 L2 μ hsym hfin C M hE hT hL2 i j)

/-- The trace bound is uniform over a genuine finite action sublevel and bounded weights. -/
theorem pathTrace_bound_on_sublevel (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (C K2 : ℝ) (hC : 0 ≤ C) (hE : action L1 L2 μ ≤ ENNReal.ofReal C)
    (hL2 : frobeniusSq L2 ≤ K2) (w : Q → ℝ)
    (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (m0 : ℝ) (hm0 : 0 ≤ m0)
    (hCE : pathTrace μ = m0 + ∑ i, signedPair (μ (Sum.inr (Sum.inr (i, i)))) w) :
    pathTrace μ ≤ 2 * m0 + 2 * K2 * C := by
  have hfin : action L1 L2 μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE
  have h := pathTrace_bound_of_time_identity L1 L2 μ hsym hfin w hwM hw m0 hm0 hCE
  have hb : frobeniusSq L2 * (action L1 L2 μ).toReal ≤ K2 * C :=
    mul_le_mul hL2 (ENNReal.toReal_le_of_le_ofReal hC hE) ENNReal.toReal_nonneg
      ((frobeniusSq_nonneg L2).trans hL2)
  linarith

/-- No TV bound is assumed: this is derived from the original time identity and action bound. -/
theorem coordinateTV_le_on_sublevel (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (C K2 : ℝ) (hC : 0 ≤ C) (hE : action L1 L2 μ ≤ ENNReal.ofReal C)
    (hL2 : frobeniusSq L2 ≤ K2) (w : Q → ℝ)
    (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (m0 : ℝ) (hm0 : 0 ≤ m0)
    (hCE : pathTrace μ = m0 + ∑ i, signedPair (μ (Sum.inr (Sum.inr (i, i)))) w)
    (c : Coord n k) :
    (μ c).totalVariation univ ≤
      ENNReal.ofReal (coordinateTVBound C (2 * m0 + 2 * K2 * C) (frobeniusSq L1) K2) := by
  exact coordinateTV_le_bound_ennreal L1 L2 μ hsym
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE) C (2 * m0 + 2 * K2 * C)
    (frobeniusSq L1) K2 (ENNReal.toReal_le_of_le_ofReal hC hE)
    (pathTrace_bound_on_sublevel L1 L2 μ hsym C K2 hC hE hL2 w hwM hw m0 hm0 hCE)
    le_rfl hL2 c

/-- The whole joint reference has a finite explicit sublevel bound, derived rather than assumed. -/
theorem jointReference_mass_le_on_sublevel (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : ∀ i j : Fin n, μ (Sum.inl (i, j)) = μ (Sum.inl (j, i)))
    (C K2 : ℝ) (hC : 0 ≤ C) (hE : action L1 L2 μ ≤ ENNReal.ofReal C)
    (hL2 : frobeniusSq L2 ≤ K2) (w : Q → ℝ)
    (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (m0 : ℝ) (hm0 : 0 ≤ m0)
    (hCE : pathTrace μ = m0 + ∑ i, signedPair (μ (Sum.inr (Sum.inr (i, i)))) w) :
    jointReference μ univ ≤ ENNReal.ofReal
      (Fintype.card (Coord n k) *
        coordinateTVBound C (2 * m0 + 2 * K2 * C) (frobeniusSq L1) K2) := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (mul_nonneg (Nat.cast_nonneg _) (coordinateTVBound_nonneg _ _ _ _))).2
  exact jointReference_mass_le_bound L1 L2 μ hsym
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE) C (2 * m0 + 2 * K2 * C)
    (frobeniusSq L1) K2 (ENNReal.toReal_le_of_le_ofReal hC hE)
    (pathTrace_bound_on_sublevel L1 L2 μ hsym C K2 hC hE hL2 w hwM hw m0 hm0 hCE)
    le_rfl hL2

/-- A true time-identity sublevel with vanishing reaction weights has vanishing reaction TV. -/
theorem reactionTV_tendsto_zero_on_sublevel (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : ℕ → Matrix (Fin n) (Fin n) ℝ) (μ : ℕ → Coord n k → SignedMeasure Q)
    (hsym : ∀ a i j, μ a (Sum.inl (i, j)) = μ a (Sum.inl (j, i)))
    (C K2 : ℝ) (hC : 0 ≤ C)
    (hE : ∀ a, action L1 (L2 a) (μ a) ≤ ENNReal.ofReal C)
    (hBound : ∀ a, frobeniusSq (L2 a) ≤ K2)
    (w : Q → ℝ) (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (m0 : ℝ) (hm0 : 0 ≤ m0)
    (hCE : ∀ a, pathTrace (μ a) =
      m0 + ∑ i, signedPair (μ a (Sum.inr (Sum.inr (i, i)))) w)
    (hL2 : Tendsto (fun a ↦ frobeniusSq (L2 a)) atTop (𝓝 0)) (i j : Fin n) :
    Tendsto (fun a ↦ (μ a (Sum.inr (Sum.inr (i, j)))).totalVariation univ)
      atTop (𝓝 0) := by
  exact reactionTV_tendsto_zero L1 L2 μ hsym
    (fun a ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hE a)) C (2 * m0 + 2 * K2 * C)
    (fun a ↦ ENNReal.toReal_le_of_le_ofReal hC (hE a))
    (fun a ↦ pathTrace_bound_on_sublevel L1 (L2 a) (μ a) (hsym a) C K2 hC
      (hE a) (hBound a) w hwM hw m0 hm0 (hCE a)) hL2 i j

/-- Convergence of the actual squared Frobenius weights already implies a global weight bound. -/
theorem exists_frobeniusSq_bound_of_tendsto_zero
    (L2 : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hL2 : Tendsto (fun a ↦ frobeniusSq (L2 a)) atTop (𝓝 0)) :
    ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ a, frobeniusSq (L2 a) ≤ K2 := by
  obtain ⟨K2, hK2⟩ :=
    (Metric.isBounded_range_of_tendsto (fun a ↦ frobeniusSq (L2 a)) hL2).bddAbove
  exact ⟨max K2 0, le_max_right _ _,
    fun a ↦ (hK2 (mem_range_self a)).trans (le_max_left _ _)⟩

/-- Full quantified sublevel coercivity and reaction vanishing, with no TV, trace or
precompactness hypothesis. The actual CE time identity is the only additional path premise. -/
theorem sublevel_coercivity_and_reaction_vanishing (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : ℕ → Matrix (Fin n) (Fin n) ℝ) (μ : ℕ → Coord n k → SignedMeasure Q)
    (hsym : ∀ a i j, μ a (Sum.inl (i, j)) = μ a (Sum.inl (j, i)))
    (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ a, action L1 (L2 a) (μ a) ≤ ENNReal.ofReal C)
    (w : Q → ℝ) (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (m0 : ℝ) (hm0 : 0 ≤ m0)
    (hCE : ∀ a, pathTrace (μ a) =
      m0 + ∑ i, signedPair (μ a (Sum.inr (Sum.inr (i, i)))) w)
    (hL2 : Tendsto (fun a ↦ frobeniusSq (L2 a)) atTop (𝓝 0)) :
    (∃ B : ℝ≥0, ∀ a c, (μ a c).totalVariation univ ≤ (B : ℝ≥0∞)) ∧
      ∀ i j, Tendsto (fun a ↦ (μ a (Sum.inr (Sum.inr (i, j)))).totalVariation univ)
        atTop (𝓝 0) := by
  obtain ⟨K2, _, hBound⟩ := exists_frobeniusSq_bound_of_tendsto_zero L2 hL2
  constructor
  · let b := coordinateTVBound C (2 * m0 + 2 * K2 * C) (frobeniusSq L1) K2
    let B : ℝ≥0 := ⟨b, coordinateTVBound_nonneg _ _ _ _⟩
    refine ⟨B, ?_⟩
    intro a c
    rw [← ENNReal.ofReal_coe_nnreal]
    exact coordinateTV_le_on_sublevel L1 (L2 a) (μ a) (hsym a) C K2 hC
      (hE a) (hBound a) w hwM hw m0 hm0 (hCE a) c
  · exact reactionTV_tendsto_zero_on_sublevel L1 L2 μ hsym C K2 hC hE hBound
      w hwM hw m0 hm0 hCE hL2

/-- Aggregate coordinate total variation of the actual reaction block. -/
def reactionTotalTV (μ : Coord n k → SignedMeasure Q) : ℝ≥0∞ :=
  ∑ p : Fin n × Fin n, (μ (Sum.inr (Sum.inr p))).totalVariation univ

theorem reactionTotalTV_tendsto_zero (μ : ℕ → Coord n k → SignedMeasure Q)
    (h : ∀ i j, Tendsto
      (fun a ↦ (μ a (Sum.inr (Sum.inr (i, j)))).totalVariation univ) atTop (𝓝 0)) :
    Tendsto (fun a ↦ reactionTotalTV (μ a)) atTop (𝓝 0) := by
  simpa only [reactionTotalTV, Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ (fun (p : Fin n × Fin n) _ ↦ h p.1 p.2))

/-- Genuine sublevel precompactness of the actual signed-measure paths; the coordinate TV
bound required for measure compactness is proved from the action and CE, not assumed. -/
theorem sublevel_signedMeasureFamily_subsequence [MetricSpace Q] [CompactSpace Q] [BorelSpace Q]
    (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : ℕ → Matrix (Fin n) (Fin n) ℝ) (μ : ℕ → Coord n k → SignedMeasure Q)
    (hsym : ∀ a i j, μ a (Sum.inl (i, j)) = μ a (Sum.inl (j, i)))
    (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ a, action L1 (L2 a) (μ a) ≤ ENNReal.ofReal C)
    (w : Q → ℝ) (hwM : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (m0 : ℝ) (hm0 : 0 ≤ m0)
    (hCE : ∀ a, pathTrace (μ a) =
      m0 + ∑ i, signedPair (μ a (Sum.inr (Sum.inr (i, i)))) w)
    (hL2 : Tendsto (fun a ↦ frobeniusSq (L2 a)) atTop (𝓝 0)) :
    ∃ (ν : Coord n k → SignedMeasure Q) (φ : ℕ → ℕ),
      StrictMono φ ∧ SignedWeakStarTendsto (fun a ↦ μ (φ a)) ν := by
  obtain ⟨B, hB⟩ := (sublevel_coercivity_and_reaction_vanishing
    L1 L2 μ hsym C hC hE w hwM hw m0 hm0 hCE hL2).1
  exact signedMeasureFamily_subsequence B μ hB

#print axioms coordinateTV_eq_integral_abs
#print axioms ae_mass_posSemidef
#print axioms integral_abs_square_bound
#print axioms reactionTV_sq_le
#print axioms fluxTV_sq_le
#print axioms pathTrace_bound_of_time_identity
#print axioms coordinateTV_le_bound_ennreal
#print axioms jointReference_mass_le_bound
#print axioms reactionTV_tendsto_zero
#print axioms jointReference_mass_le_on_sublevel
#print axioms reactionTV_tendsto_zero_on_sublevel
#print axioms sublevel_coercivity_and_reaction_vanishing
#print axioms reactionTotalTV_tendsto_zero
#print axioms sublevel_signedMeasureFamily_subsequence

end MatrixTransport.ReactionZero.PathCoercivity
