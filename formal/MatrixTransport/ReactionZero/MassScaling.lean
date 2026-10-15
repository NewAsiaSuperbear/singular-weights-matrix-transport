import MatrixTransport.PartialWeights.WeightComparison
import MatrixTransport.ReactionZero.LimitTheorem

/-!
# Exact mass and rate rescaling of the original support action

The dual transformation is `(A,B,C) ↦ (r² A,r B,r C)`. Its pairing with
`(M,Z,R)` is exactly `r` times the original pairing with `(r M,Z,R)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.ReactionZero

variable {n k : ℕ}

def massScaleDual (r : ℝ) (a : Coord n k → ℝ) : Coord n k → ℝ :=
  pack (r ^ 2 • mass a) (r • flux a) (r • reaction a)

theorem massScaleDual_mem (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (a : Coord n k → ℝ)
    (ha : a ∈ dualSet L H) : massScaleDual r a ∈ dualSet L H := by
  refine ⟨?_, ?_⟩
  · exact ha.1.smul (by rfl : IsSelfAdjoint (r ^ 2))
  · change (-mass (massScaleDual r a) - (1 / 2 : ℝ) • gram (flux (massScaleDual r a) * L)
        - (1 / 2 : ℝ) • gram (reaction (massScaleDual r a) * H)).PosSemidef
    simp only [massScaleDual, mass_pack, flux_pack, reaction_pack, Matrix.smul_mul, gram_smul]
    have he : -(r ^ 2 • mass a) - (1 / 2 : ℝ) • (r ^ 2 • gram (flux a * L)) -
        (1 / 2 : ℝ) • (r ^ 2 • gram (reaction a * H)) =
        r ^ 2 • (-mass a - (1 / 2 : ℝ) • gram (flux a * L) -
          (1 / 2 : ℝ) • gram (reaction a * H)) := by module
    rw [he]
    exact ha.2.smul (sq_nonneg r)

theorem massScaleDual_pair (r : ℝ) (a : Coord n k → ℝ)
    (M R : Matrix (Fin n) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin k) ℝ) :
    weightedPair (fun _ ↦ 1) (massScaleDual r a) (pack M Z R) =
      r * weightedPair (fun _ ↦ 1) a (pack (r • M) Z R) := by
  simp only [weightedPair_pack, massScaleDual, mass_pack, flux_pack, reaction_pack,
    frob_smul_left, frob_smul_right]
  ring

theorem cost_pack_smul_mass_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (M R : Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) {r : ℝ} (hr : 0 < r) :
    cost L H (pack (r • M) Z R) ≤ ENNReal.ofReal r⁻¹ * cost L H (pack M Z R) := by
  unfold cost supportFunction
  refine iSup₂_le fun a ha ↦ ?_
  have hs := cost_fenchel L H (pack M Z R) (massScaleDual r a)
    (massScaleDual_mem L H r a ha)
  rw [massScaleDual_pair, ENNReal.ofReal_mul hr.le] at hs
  calc
    ENNReal.ofReal (weightedPair (fun _ ↦ 1) a (pack (r • M) Z R)) =
        ENNReal.ofReal r⁻¹ * (ENNReal.ofReal r *
          ENNReal.ofReal (weightedPair (fun _ ↦ 1) a (pack (r • M) Z R))) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le), inv_mul_cancel₀ hr.ne']
      simp
    _ ≤ ENNReal.ofReal r⁻¹ * cost L H (pack M Z R) := mul_le_mul_right hs _

theorem cost_pack_smul_mass (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (M R : Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) {r : ℝ} (hr : 0 < r) :
    cost L H (pack (r • M) Z R) = ENNReal.ofReal r⁻¹ * cost L H (pack M Z R) := by
  apply le_antisymm (cost_pack_smul_mass_le L H M R Z hr)
  have hs := cost_pack_smul_mass_le L H (r • M) R Z (inv_pos.mpr hr)
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul, inv_inv] at hs
  have h := mul_le_mul_right hs (ENNReal.ofReal r⁻¹)
  simpa only [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),
    inv_mul_cancel₀ hr.ne', ENNReal.ofReal_one, one_mul] using h

theorem cost_pack_div_rates (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (M R : Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) {r : ℝ} (hr : 0 < r) :
    cost L H (pack M (r⁻¹ • Z) (r⁻¹ • R)) =
      ENNReal.ofReal (r⁻¹ ^ 2) * cost L H (pack M Z R) := by
  have he : pack M (r⁻¹ • Z) (r⁻¹ • R) = r⁻¹ • pack (r • M) Z R := by
    funext c
    rcases c with p | p | p
    · change M p.1 p.2 = r⁻¹ * (r * M p.1 p.2)
      rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    · rfl
    · rfl
  rw [he, cost_smul_nonneg _ _ _ (inv_nonneg.mpr hr.le), cost_pack_smul_mass _ _ _ _ _ hr,
    ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le), ← pow_two]

theorem pack_neg_flux_mem (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (a : Coord n k → ℝ)
    (ha : a ∈ dualSet L H) : pack (mass a) (-flux a) (reaction a) ∈ dualSet L H := by
  refine ⟨ha.1, ?_⟩
  simpa only [mass_pack, flux_pack, reaction_pack, Matrix.neg_mul,
    gram, Matrix.transpose_neg, Matrix.mul_neg, neg_neg] using ha.2

theorem cost_pack_neg_flux_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (M R : Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) :
    cost L H (pack M (-Z) R) ≤ cost L H (pack M Z R) := by
  unfold cost supportFunction
  refine iSup₂_le fun a ha ↦ ?_
  have hs := cost_fenchel L H (pack M Z R) (pack (mass a) (-flux a) (reaction a))
    (pack_neg_flux_mem L H a ha)
  have hn : frob (flux a) (-Z) = -frob (flux a) Z := by
    simp [frob, Finset.sum_neg_distrib]
  simpa only [cost, supportFunction, weightedPair_pack, mass_pack, flux_pack, reaction_pack,
    frob_neg_left, hn] using hs

theorem cost_pack_neg_flux (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (M R : Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) :
    cost L H (pack M (-Z) R) = cost L H (pack M Z R) := by
  apply le_antisymm (cost_pack_neg_flux_le L H M R Z)
  simpa only [neg_neg] using cost_pack_neg_flux_le L H M R (-Z)

theorem reaction_zero_of_cost_ne_top (L : Matrix (Fin k) (Fin k) ℝ)
    (v : Coord n k → ℝ) (hfin : cost L 0 v ≠ ⊤) : reaction v = 0 := by
  ext i j
  have h := reaction_entry_sq_le L 0 v hfin i j
  simp only [Matrix.zero_apply, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero,
    mul_zero] at h
  simpa only [Matrix.zero_apply] using (show reaction v i j = 0 by nlinarith [sq_nonneg (reaction v i j)])

theorem cost_eq_top_of_reaction_ne_zero_zeroWeight (L : Matrix (Fin k) (Fin k) ℝ)
    (v : Coord n k → ℝ) (hv : reaction v ≠ 0) : cost L 0 v = ⊤ := by
  by_contra h
  exact hv (reaction_zero_of_cost_ne_top L v h)

section Measures

variable {X : Type*} [MeasurableSpace X]

theorem reaction_measures_zero_of_action_ne_top (L : Matrix (Fin k) (Fin k) ℝ)
    (μ : Coord n k → SignedMeasure X) (hfin : action L 0 μ ≠ ⊤) :
    ∀ i j, μ (Sum.inr (Sum.inr (i, j))) = 0 := by
  intro i j
  have hz : ∀ᵐ x ∂jointReference μ, density μ x (Sum.inr (Sum.inr (i, j))) = 0 :=
    (PathCoercivity.ae_cost_ne_top L 0 μ hfin).mono fun x hx ↦
      congrArg (fun R ↦ R i j) (reaction_zero_of_cost_ne_top L (density μ x) hx)
  ext s hs
  rw [← withDensityᵥ_rnDeriv_jointReference μ (Sum.inr (Sum.inr (i, j))),
    withDensityᵥ_apply (integrable_rnDeriv_jointReference μ _) hs]
  simp only [zero_apply]
  exact integral_eq_zero_of_ae (ae_restrict_of_ae hz)

theorem action_eq_of_gram_eq
    (L L' : Matrix (Fin k) (Fin k) ℝ) (H H' : Matrix (Fin n) (Fin n) ℝ)
    (hL : gram L = gram L') (hH : gram H = gram H')
    (μ : Coord n k → SignedMeasure X) : action L H μ = action L' H' μ := by
  apply le_antisymm
  · have h := MatrixTransport.PartialWeights.action_le_inv_mul_of_relative_grams
      L L' H H' 1 (by norm_num) (by simp [hL]; exact Matrix.PosSemidef.zero)
      (by simp [hH]; exact Matrix.PosSemidef.zero) μ
    simpa using h
  · have h := MatrixTransport.PartialWeights.action_le_inv_mul_of_relative_grams
      L' L H' H 1 (by norm_num) (by simp [hL]; exact Matrix.PosSemidef.zero)
      (by simp [hH]; exact Matrix.PosSemidef.zero) μ
    simpa using h

end Measures

theorem gram_sub_smul_self_posSemidef (L : Matrix (Fin k) (Fin k) ℝ)
    {α : ℝ} (hα : α ≤ 1) : (gram L - α • gram L).PosSemidef := by
  have he : gram L - α • gram L = (1 - α) • gram L := by module
  rw [he]
  exact (posSemidef_gram L).smul (sub_nonneg.mpr hα)

theorem ray_relative_grams (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) {t : ℝ} (ht : 1 ≤ t) :
    (gram L - (t⁻¹ ^ 2) • gram (t • L)).PosSemidef ∧
      (gram H - (t⁻¹ ^ 2) • gram H).PosSemidef := by
  have hp : 0 < t := lt_of_lt_of_le zero_lt_one ht
  constructor
  · rw [gram_smul, smul_smul, ← mul_pow, inv_mul_cancel₀ hp.ne']
    simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin k) (Fin k) ℝ).PosSemidef)
  · exact gram_sub_smul_self_posSemidef H
      (pow_le_one₀ (inv_nonneg.mpr hp.le) ((inv_le_one₀ hp).mpr ht))

namespace Limit

open MatrixTransport.ReactionZero.ClosedDomain
variable {d : ℕ} {Ω : Set (Space d)}

theorem minimumValue_eq_top_iff (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    minimumValue P L H = ⊤ ↔ ∀ μ, Good P μ → action L H μ = ⊤ := by
  simp only [minimumValue, constrainedInfimum, iInf_eq_top]

theorem minimumValue_zero_eq_balancedValue (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) : minimumValue P L 0 = balancedValue P L := by
  apply le_antisymm
  · apply le_iInf₂
    intro μ hμ
    have he := action_eq_of_reaction_measures_zero L 0 1 μ hμ.2
    rw [← he]
    exact iInf_le_of_le μ (iInf_le_of_le hμ.1 le_rfl)
  · apply le_iInf₂
    intro μ hμ
    by_cases hfin : action L 0 μ = ⊤
    · rw [hfin]; exact le_top
    · have hz := reaction_measures_zero_of_action_ne_top L μ hfin
      have he := action_eq_of_reaction_measures_zero L 0 1 μ hz
      rw [he]
      exact iInf_le_of_le μ (iInf_le_of_le (show Balanced P μ from ⟨hμ, hz⟩) le_rfl)

end Limit

#print axioms cost_pack_smul_mass
#print axioms cost_pack_div_rates
#print axioms cost_pack_neg_flux
#print axioms reaction_measures_zero_of_action_ne_top
#print axioms action_eq_of_gram_eq
#print axioms ray_relative_grams
#print axioms Limit.minimumValue_zero_eq_balancedValue

end MatrixTransport.ReactionZero
