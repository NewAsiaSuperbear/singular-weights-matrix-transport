import MatrixTransport.PartialReaction.JointLowerSemicontinuity

/-!
# Joint lower semicontinuity when both matrix weights vary

The transport and reaction dimensions remain independent. Rectangular congruence bounds
produce two vanishing scalar mass-dual shifts, whose sum makes every target dual field
admissible for the current weights. The conclusion concerns the actual signed-measure
RN action, with no assumed lower semicontinuity or dual representation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialWeights

open MatrixTransport.ReactionZero
open MatrixTransport.PartialReaction

variable {n k : ℕ}

/-- Uniform rectangular congruence domination; the two matrix dimensions need not agree. -/
theorem posSemidef_uniform_rectangular_congruence_defect {m p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (C : Matrix (Fin m) (Fin p) ℝ)
    (hS : S.IsHermitian) (M : ℝ) (hM : frobeniusSq C ≤ M) :
    ((entryAbsSum S * M) • (1 : Matrix (Fin m) (Fin m) ℝ) -
      C * S * C.transpose).PosSemidef := by
  have hs := (posSemidef_entryAbsSum_sub S hS).mul_mul_conjTranspose_same C
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hs
  have hg := (posSemidef_frobeniusSq_sub_gram C).smul (entryAbsSum_nonneg S)
  have hplus := hs.add hg
  have he : (C * (entryAbsSum S • (1 : Matrix (Fin p) (Fin p) ℝ) - S) * C.transpose) +
      entryAbsSum S • (frobeniusSq C • (1 : Matrix (Fin m) (Fin m) ℝ) - ReactionZero.gram C) =
      (entryAbsSum S * frobeniusSq C) • (1 : Matrix (Fin m) (Fin m) ℝ) -
        C * S * C.transpose := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, ReactionZero.gram, smul_sub, smul_smul]
    module
  rw [he] at hplus
  have hpad := (Matrix.PosSemidef.one :
    (1 : Matrix (Fin m) (Fin m) ℝ).PosSemidef).smul
      (mul_nonneg (entryAbsSum_nonneg S) (sub_nonneg.mpr hM))
  have := hplus.add hpad
  convert this using 1
  module

/-- An explicit sum of transport and reaction mass shifts makes every target dual test
admissible for both current weights. -/
theorem massShift_mem_dualSet_two_weights
    (L Lstar : Matrix (Fin k) (Fin k) ℝ) (H Hstar : Matrix (Fin n) (Fin n) ℝ)
    (a : Coord n k → ℝ) (ha : a ∈ ReactionZero.dualSet Lstar Hstar)
    (MB MC : ℝ) (hMB : frobeniusSq (ReactionZero.flux a) ≤ MB)
    (hMC : frobeniusSq (ReactionZero.reaction a) ≤ MC) :
    massShift ((entryAbsSum (ReactionZero.gram L - ReactionZero.gram Lstar) * MB +
      entryAbsSum (ReactionZero.gram H - ReactionZero.gram Hstar) * MC) / 2) a ∈
        ReactionZero.dualSet L H := by
  have hSL : (ReactionZero.gram L - ReactionZero.gram Lstar).IsHermitian :=
    (posSemidef_gram L).isHermitian.sub (posSemidef_gram Lstar).isHermitian
  have hSH : (ReactionZero.gram H - ReactionZero.gram Hstar).IsHermitian :=
    (posSemidef_gram H).isHermitian.sub (posSemidef_gram Hstar).isHermitian
  have hdL := (posSemidef_uniform_rectangular_congruence_defect
    (ReactionZero.gram L - ReactionZero.gram Lstar) (ReactionZero.flux a) hSL MB hMB).smul
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hdH := (posSemidef_uniform_rectangular_congruence_defect
    (ReactionZero.gram H - ReactionZero.gram Hstar) (ReactionZero.reaction a) hSH MC hMC).smul
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have heL : ReactionZero.flux a * (ReactionZero.gram L - ReactionZero.gram Lstar) *
      (ReactionZero.flux a).transpose =
      ReactionZero.gram (ReactionZero.flux a * L) -
        ReactionZero.gram (ReactionZero.flux a * Lstar) :=
    (gram_mul_sub (ReactionZero.flux a) L Lstar).symm
  have heH : ReactionZero.reaction a * (ReactionZero.gram H - ReactionZero.gram Hstar) *
      (ReactionZero.reaction a).transpose =
      ReactionZero.gram (ReactionZero.reaction a * H) -
        ReactionZero.gram (ReactionZero.reaction a * Hstar) :=
    (gram_mul_sub (ReactionZero.reaction a) H Hstar).symm
  rw [heL] at hdL
  rw [heH] at hdH
  obtain ⟨hA, hP⟩ := ha
  refine ⟨?_, ?_⟩
  · rw [mass_massShift]
    exact hA.sub ((Matrix.isHermitian_one).smul (by rfl))
  · rw [mass_massShift, flux_massShift, reaction_massShift]
    have hp := (hP.add hdL).add hdH
    convert hp using 1
    module

section ContinuousFields

variable {Q : Type*} [TopologicalSpace Q] [CompactSpace Q]

/-- The squared Frobenius size of every continuous rectangular flux field is bounded. -/
theorem continuousField_flux_bounded (a : C(Q, Coord n k → ℝ)) :
    ∃ M : ℝ, ∀ x, frobeniusSq (ReactionZero.flux (a x)) ≤ M := by
  let f : C(Q, ℝ) := ⟨fun x ↦ frobeniusSq (ReactionZero.flux (a x)),
    continuous_frobeniusSq.comp (WeightedSet.continuous_flux.comp a.continuous)⟩
  refine ⟨‖f‖, fun x ↦ ?_⟩
  exact (le_abs_self (f x)).trans (by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)

end ContinuousFields

/-- Matrix convergence makes the explicit covariance defect gauge tend to zero. -/
theorem entryAbsSum_gram_defect_tendsto_zero {p : ℕ}
    (K : ℕ → Matrix (Fin p) (Fin p) ℝ) (Kstar : Matrix (Fin p) (Fin p) ℝ)
    (hK : Tendsto K atTop (𝓝 Kstar)) :
    Tendsto (fun j ↦ entryAbsSum (ReactionZero.gram (K j) - ReactionZero.gram Kstar))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun j ↦ ReactionZero.gram (K j) - ReactionZero.gram Kstar)
      atTop (𝓝 (0 : Matrix (Fin p) (Fin p) ℝ)) := by
    have hc : Tendsto (fun _ : ℕ ↦ ReactionZero.gram Kstar) atTop
        (𝓝 (ReactionZero.gram Kstar)) := tendsto_const_nhds
    simpa only [Function.comp_def, sub_self] using
      ((WeightedSet.continuous_gram.tendsto Kstar).comp hK).sub hc
  simpa only [Function.comp_def, entryAbsSum_zero] using
    (continuous_entryAbsSum.tendsto 0).comp hg

section JointLimit

variable {Q : Type*} [MeasurableSpace Q] [MetricSpace Q] [CompactSpace Q] [BorelSpace Q]

/-- Actual weighted action is jointly lower semicontinuous under simultaneous matrix-weight
convergence and genuine coordinate signed-measure weak-star convergence. Both weights can
be singular; no Loewner comparison, common eigenbasis, or positive lower eigenvalue is needed.
-/
theorem action_le_varying_weights_liminf
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar))
    (μ : ℕ → Coord n k → SignedMeasure Q) (ν : Coord n k → SignedMeasure Q)
    (hμ : SignedWeakStarTendsto μ ν) :
    ReactionZero.action Lstar Hstar ν ≤
      atTop.liminf (fun j ↦ ReactionZero.action (L j) (H j) (μ j)) := by
  rw [WeightedSet.action_eq_continuousDual]
  unfold Duality.continuousDual
  refine iSup_le fun a ↦ iSup_le fun ha ↦ ?_
  obtain ⟨MB, hMB⟩ := continuousField_flux_bounded a
  obtain ⟨MC, hMC⟩ := continuousField_reaction_bounded a
  let δ : ℕ → ℝ := fun j ↦
    (entryAbsSum (ReactionZero.gram (L j) - ReactionZero.gram Lstar) * MB +
      entryAbsSum (ReactionZero.gram (H j) - ReactionZero.gram Hstar) * MC) / 2
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hLb := entryAbsSum_gram_defect_tendsto_zero L Lstar hL
    have hHb := entryAbsSum_gram_defect_tendsto_zero H Hstar hH
    simpa only [δ, zero_mul, zero_add, zero_div] using
      ((hLb.mul_const MB).add (hHb.mul_const MC)).div_const (2 : ℝ)
  have hpair : Tendsto
      (fun j ↦ Duality.coordinatePair (fun _ ↦ 1) (μ j) (massShiftField (δ j) a)) atTop
      (𝓝 (Duality.coordinatePair (fun _ ↦ 1) ν a)) := by
    have ht := (coordinatePair_tendsto μ ν hμ a).sub
      (hδ.mul (coordinatePair_tendsto μ ν hμ (massIdentityField (Q := Q))))
    simpa only [coordinatePair_massShiftField, zero_mul, sub_zero] using ht
  have ht : Tendsto
      (fun j ↦ ENNReal.ofReal
        (Duality.coordinatePair (fun _ ↦ 1) (μ j) (massShiftField (δ j) a))) atTop
      (𝓝 (ENNReal.ofReal (Duality.coordinatePair (fun _ ↦ 1) ν a))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpair
  have hbound : ∀ j, ENNReal.ofReal
      (Duality.coordinatePair (fun _ ↦ 1) (μ j) (massShiftField (δ j) a)) ≤
        ReactionZero.action (L j) (H j) (μ j) := by
    intro j
    have hadm : ∀ x, massShiftField (δ j) a x ∈ ReactionZero.dualSet (L j) (H j) := by
      intro x
      exact massShift_mem_dualSet_two_weights (L j) Lstar (H j) Hstar (a x)
        (ha x) MB MC (hMB x) (hMC x)
    rw [WeightedSet.action_eq_continuousDual]
    exact le_iSup₂ (f := fun (b : C(Q, Coord n k → ℝ))
      (_ : ∀ x, b x ∈ ReactionZero.dualSet (L j) (H j)) ↦
        ENNReal.ofReal (Duality.coordinatePair (fun _ ↦ 1) (μ j) b))
      (massShiftField (δ j) a) hadm
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Filter.Eventually.of_forall hbound)

end JointLimit

end MatrixTransport.PartialWeights

#print axioms MatrixTransport.PartialWeights.posSemidef_uniform_rectangular_congruence_defect
#print axioms MatrixTransport.PartialWeights.massShift_mem_dualSet_two_weights
#print axioms MatrixTransport.PartialWeights.action_le_varying_weights_liminf
