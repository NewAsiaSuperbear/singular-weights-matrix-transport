import MatrixTransport.PartialReaction.KernelExtinction

/-!
# Genuine flux and reaction extinction for jointly varying weights

The flux is an `n × k` matrix, independently of the `n × n` reaction. Its directional
signed measure and multiplied RN density are actually represented. The final variations
are integrals of actual Frobenius norms; coordinate variation sums are only upper bounds.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.PartialWeights

open MatrixTransport.ReactionZero
open MatrixTransport.ReactionZero.Limit
open MatrixTransport.PartialReaction

variable {n k p : ℕ}

/-- A rectangular dual flux test supported on one mass row. -/
def rowFluxDirection (i : Fin n) (v : Fin k → ℝ) : Matrix (Fin n) (Fin k) ℝ :=
  fun a b ↦ if a = i then v b else 0

theorem rowFluxDirection_mul_apply (i : Fin n) (v : Fin k → ℝ)
    (L : Matrix (Fin k) (Fin k) ℝ) (a : Fin n) (b : Fin k) :
    (rowFluxDirection i v * L) a b = if a = i then (L.transpose *ᵥ v) b else 0 := by
  by_cases h : a = i <;>
    simp [rowFluxDirection, Matrix.mul_apply, Matrix.mulVec, dotProduct, h, mul_comm]

theorem frob_rowFluxDirection (i : Fin n) (v : Fin k → ℝ)
    (q : Matrix (Fin n) (Fin k) ℝ) :
    ReactionZero.frob (rowFluxDirection i v) q = ∑ a, v a * q i a := by
  unfold ReactionZero.frob
  rw [Finset.sum_eq_single i]
  · simp [rowFluxDirection]
  · intro a _ ha
    simp [rowFluxDirection, ha]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem frob_gram_rowFluxDirection (i : Fin n) (v : Fin k → ℝ)
    (L : Matrix (Fin k) (Fin k) ℝ) (G : Matrix (Fin n) (Fin n) ℝ) :
    ReactionZero.frob (ReactionZero.gram (rowFluxDirection i v * L)) G =
      G i i * directionSq L v := by
  have key : ∀ (X : Matrix (Fin n) (Fin k) ℝ) (a c : Fin n),
      ReactionZero.gram X a c = ∑ b, X a b * X c b := by
    intro X a c
    simp [ReactionZero.gram, Matrix.mul_apply]
  have hg : ∀ a c, ReactionZero.gram (rowFluxDirection i v * L) a c =
      if a = i ∧ c = i then directionSq L v else 0 := by
    intro a c
    rw [key]
    simp only [rowFluxDirection_mul_apply]
    by_cases ha : a = i <;> by_cases hc : c = i <;>
      simp [ha, hc, directionSq, pow_two]
  unfold ReactionZero.frob
  simp only [hg]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp only [ite_true, and_self, mul_comm]
    · intro c _ hc
      simp [hc]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · intro a _ ha
    simp [ha]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The genuine rectangular flux pairing has the exact transpose-direction weight. -/
theorem flux_direction_sq_le_trace (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (a : Coord n k → ℝ)
    (hsym : (ReactionZero.mass a).IsHermitian)
    (hfin : ReactionZero.cost L H a ≠ ⊤) (v : Fin k → ℝ) (i : Fin n) :
    (∑ b, v b * ReactionZero.flux a i b) ^ 2 ≤
      2 * (ReactionZero.cost L H a).toReal *
        ((ReactionZero.mass a).trace * directionSq L v) := by
  have h := flux_pairing_sq_le L H a hfin (rowFluxDirection i v)
  rw [frob_rowFluxDirection, frob_gram_rowFluxDirection] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mass_diag_le_trace L H a hsym hfin i)
      (directionSq_nonneg L v)) (by positivity))

section Measures

variable {Q : Type*} [MeasurableSpace Q]

/-- The actual i-th signed coordinate measure of `q v`. -/
def fluxDirection (μ : Coord n k → SignedMeasure Q) (v : Fin k → ℝ)
    (i : Fin n) : SignedMeasure Q :=
  ∑ a, v a • μ (Sum.inr (Sum.inl (i, a)))

def fluxDirectionDensity (μ : Coord n k → SignedMeasure Q) (v : Fin k → ℝ)
    (i : Fin n) (x : Q) : ℝ :=
  ∑ a, v a * ReactionZero.density μ x (Sum.inr (Sum.inl (i, a)))

theorem fluxDirectionDensity_integrable (μ : Coord n k → SignedMeasure Q)
    (v : Fin k → ℝ) (i : Fin n) :
    Integrable (fluxDirectionDensity μ v i) (jointReference μ) := by
  apply integrable_finsetSum
  intro a _
  exact (integrable_rnDeriv_jointReference μ _).const_mul (v a)

/-- The signed linear combination is represented by the actual multiplied RN density. -/
theorem withDensity_fluxDirection (μ : Coord n k → SignedMeasure Q)
    (v : Fin k → ℝ) (i : Fin n) :
    (jointReference μ).withDensityᵥ (fluxDirectionDensity μ v i) =
      fluxDirection μ v i := by
  change (jointReference μ).withDensityᵥ
    (fun x ↦ ∑ a, v a * ReactionZero.density μ x (Sum.inr (Sum.inl (i, a)))) = _
  rw [withDensity_finiteSum]
  · unfold fluxDirection
    apply Finset.sum_congr rfl
    intro a _
    have hs : (jointReference μ).withDensityᵥ
        (fun x ↦ v a * ReactionZero.density μ x (Sum.inr (Sum.inl (i, a)))) =
        v a • (jointReference μ).withDensityᵥ
          (fun x ↦ ReactionZero.density μ x (Sum.inr (Sum.inl (i, a)))) := by
      simpa only [smul_eq_mul] using
        (withDensityᵥ_smul' (μ := jointReference μ)
          (fun x ↦ ReactionZero.density μ x (Sum.inr (Sum.inl (i, a)))) (v a))
    exact hs.trans (congrArg (fun s : SignedMeasure Q ↦ v a • s)
      (withDensityᵥ_rnDeriv_jointReference μ (Sum.inr (Sum.inl (i, a)))))
  · intro a
    exact (integrable_rnDeriv_jointReference μ _).const_mul (v a)

theorem fluxDirectionTV_eq_integral_abs (μ : Coord n k → SignedMeasure Q)
    (v : Fin k → ℝ) (i : Fin n) :
    ((fluxDirection μ v i).totalVariation univ).toReal =
      ∫ x, |fluxDirectionDensity μ v i x| ∂jointReference μ := by
  rw [SignedMeasure.totalVariation_eq_variation]
  have h := Measure.variation_withDensityᵥ (fluxDirectionDensity_integrable μ v i)
  rw [withDensity_fluxDirection] at h
  rw [h, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simpa only [Real.norm_eq_abs] using
    (integral_norm_eq_lintegral_enorm
      (fluxDirectionDensity_integrable μ v i).aestronglyMeasurable).symm

theorem fluxDirectionTV_eq_lintegral_abs (μ : Coord n k → SignedMeasure Q)
    (v : Fin k → ℝ) (i : Fin n) :
    (fluxDirection μ v i).totalVariation univ =
      ∫⁻ x, ENNReal.ofReal |fluxDirectionDensity μ v i x| ∂jointReference μ := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (fluxDirection μ v i).totalVariation univ),
    fluxDirectionTV_eq_integral_abs]
  exact ofReal_integral_eq_lintegral_ofReal
    (fluxDirectionDensity_integrable μ v i).abs (ae_of_all _ fun _ ↦ abs_nonneg _)

/-- The actual directional flux variation obeys the action/trace/weight square bound. -/
theorem fluxDirectionTV_sq_le (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : MassSymmetric μ) (hfin : ReactionZero.action L H μ ≠ ⊤)
    (v : Fin k → ℝ) (i : Fin n) :
    ((fluxDirection μ v i).totalVariation univ).toReal ^ 2 ≤
      2 * (ReactionZero.action L H μ).toReal *
        (PathCoercivity.pathTrace μ * directionSq L v) := by
  rw [fluxDirectionTV_eq_integral_abs]
  have h := PathCoercivity.integral_abs_square_bound
    (fluxDirectionDensity_integrable μ v i)
    (PathCoercivity.integrable_mass_trace μ)
    (PathCoercivity.integrable_cost_toReal L H μ hfin)
    (directionSq_nonneg L v)
    ((PathCoercivity.ae_mass_posSemidef L H μ hsym hfin).mono fun _ hx ↦
      trace_nonneg_of_posSemidef hx)
    (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
    ((PathCoercivity.ae_cost_ne_top L H μ hfin).mono fun x hx ↦
      flux_direction_sq_le_trace L H (ReactionZero.density μ x)
        (PathCoercivity.mass_density_isHermitian μ hsym x) hx v i)
  simpa only [PathCoercivity.integral_cost_toReal L H μ hfin,
    PathCoercivity.pathTrace, fluxDirectionDensity, ReactionZero.flux] using h

theorem fluxDirectionTV_le_sqrt (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure Q)
    (hsym : MassSymmetric μ) (hfin : ReactionZero.action L H μ ≠ ⊤) (C M : ℝ)
    (hE : (ReactionZero.action L H μ).toReal ≤ C)
    (hT : PathCoercivity.pathTrace μ ≤ M) (v : Fin k → ℝ) (i : Fin n) :
    ((fluxDirection μ v i).totalVariation univ).toReal ≤
      Real.sqrt (directionSq L v) * Real.sqrt (2 * C * M) := by
  apply reaction_bound_of_square ENNReal.toReal_nonneg (Real.sqrt_nonneg _)
    ENNReal.toReal_nonneg (PathCoercivity.pathTrace_nonneg L H μ hsym hfin) hE hT
  rw [Real.sq_sqrt (directionSq_nonneg L v)]
  convert fluxDirectionTV_sq_le L H μ hsym hfin v i using 1
  ring

/-- The genuine signed matrix-measure product `q P`. -/
def rightFluxMeasure (μ : Coord n k → SignedMeasure Q)
    (P : Matrix (Fin k) (Fin p) ℝ) (i : Fin n) (j : Fin p) : SignedMeasure Q :=
  fluxDirection μ (fun a ↦ P a j) i

/-- Actual Frobenius RN variation of `q P`, without an entrywise-TV definition. -/
def rightFluxFrobeniusTV (μ : Coord n k → SignedMeasure Q)
    (P : Matrix (Fin k) (Fin p) ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.sqrt
    (frobeniusSq (ReactionZero.flux (ReactionZero.density μ x) * P))) ∂jointReference μ

/-- The already proved genuine reaction norm integral, reused unchanged. -/
abbrev rightReactionFrobeniusTV (μ : Coord n k → SignedMeasure Q)
    (P : Matrix (Fin n) (Fin p) ℝ) : ℝ≥0∞ :=
  PartialReaction.rightReactionFrobeniusTV μ P

theorem fluxDirectionDensity_column (μ : Coord n k → SignedMeasure Q)
    (P : Matrix (Fin k) (Fin p) ℝ) (i : Fin n) (j : Fin p) (x : Q) :
    fluxDirectionDensity μ (fun a ↦ P a j) i x =
      (ReactionZero.flux (ReactionZero.density μ x) * P) i j := by
  simp only [fluxDirectionDensity, Matrix.mul_apply, ReactionZero.flux, mul_comm]

theorem withDensity_rightFluxMeasure (μ : Coord n k → SignedMeasure Q)
    (P : Matrix (Fin k) (Fin p) ℝ) (i : Fin n) (j : Fin p) :
    (jointReference μ).withDensityᵥ
      (fun x ↦ (ReactionZero.flux (ReactionZero.density μ x) * P) i j) =
      rightFluxMeasure μ P i j := by
  simp_rw [← fluxDirectionDensity_column μ P i j]
  exact withDensity_fluxDirection μ (fun a ↦ P a j) i

theorem measurable_fluxDirectionDensity (μ : Coord n k → SignedMeasure Q)
    (v : Fin k → ℝ) (i : Fin n) : Measurable (fluxDirectionDensity μ v i) := by
  unfold fluxDirectionDensity ReactionZero.density
  exact Finset.measurable_fun_sum _ fun a _ ↦
    (measurable_rnDeriv_jointReference μ _).const_mul (v a)

theorem rightFluxFrobeniusTV_le_sum_directionTV
    (μ : Coord n k → SignedMeasure Q) (P : Matrix (Fin k) (Fin p) ℝ) :
    rightFluxFrobeniusTV μ P ≤
      ∑ a : Fin n × Fin p, (rightFluxMeasure μ P a.1 a.2).totalVariation univ := by
  calc rightFluxFrobeniusTV μ P
      ≤ ∫⁻ x, ENNReal.ofReal (∑ a : Fin n × Fin p,
          |(ReactionZero.flux (ReactionZero.density μ x) * P) a.1 a.2|) ∂jointReference μ :=
        lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
          (MatrixVariation.sqrt_frobeniusSq_le_sum_abs
            (ReactionZero.flux (ReactionZero.density μ x) * P))
      _ = ∫⁻ x, ∑ a : Fin n × Fin p,
          ENNReal.ofReal |fluxDirectionDensity μ (fun b ↦ P b a.2) a.1 x|
          ∂jointReference μ := by
        congr 1
        funext x
        simp_rw [fluxDirectionDensity_column]
        exact ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ abs_nonneg _)
      _ = ∑ a : Fin n × Fin p, ∫⁻ x,
          ENNReal.ofReal |fluxDirectionDensity μ (fun b ↦ P b a.2) a.1 x|
          ∂jointReference μ :=
        lintegral_finsetSum Finset.univ fun a _ ↦
          (measurable_fluxDirectionDensity μ (fun b ↦ P b a.2) a.1).abs.ennreal_ofReal
      _ = ∑ a : Fin n × Fin p, (rightFluxMeasure μ P a.1 a.2).totalVariation univ := by
        unfold rightFluxMeasure
        apply Finset.sum_congr rfl
        intro a _
        exact (fluxDirectionTV_eq_lintegral_abs μ (fun b ↦ P b a.2) a.1).symm

theorem rightFluxFrobeniusTV_tendsto_zero
    (μ : ℕ → Coord n k → SignedMeasure Q) (P : Matrix (Fin k) (Fin p) ℝ)
    (h : ∀ i j, Tendsto
      (fun a ↦ (rightFluxMeasure (μ a) P i j).totalVariation univ) atTop (𝓝 0)) :
    Tendsto (fun a ↦ rightFluxFrobeniusTV (μ a) P) atTop (𝓝 0) := by
  have hs : Tendsto (fun j ↦ ∑ a : Fin n × Fin p,
      (rightFluxMeasure (μ j) P a.1 a.2).totalVariation univ) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum Finset.univ (fun (a : Fin n × Fin p) _ ↦ h a.1 a.2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun _ ↦ bot_le) (fun j ↦ rightFluxFrobeniusTV_le_sum_directionTV (μ j) P)

/-- Elementary sequence bookkeeping: actual signed-TV limits follow from a proved
eventual directional bound. Concrete original-model bounds are supplied below. -/
theorem signedTV_tendsto_zero_of_eventual_direction_bound {m : ℕ}
    (K : ℕ → Matrix (Fin m) (Fin m) ℝ) (Kstar : Matrix (Fin m) (Fin m) ℝ)
    (hK : Tendsto K atTop (𝓝 Kstar)) (v : Fin m → ℝ)
    (hv : Kstar.transpose *ᵥ v = 0) (s : ℕ → SignedMeasure Q) (B : ℝ)
    (hb : ∀ᶠ j in atTop, ((s j).totalVariation univ).toReal ≤
      Real.sqrt (directionSq (K j) v) * B) :
    Tendsto (fun j ↦ (s j).totalVariation univ) atTop (𝓝 0) := by
  have hd : Tendsto (fun j ↦ directionSq (K j) v) atTop (𝓝 0) := by
    simpa only [Function.comp_def, directionSq, hv, Pi.zero_apply,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] using
      (continuous_directionSq v).tendsto Kstar |>.comp hK
  have hsq : Tendsto (fun j ↦ Real.sqrt (directionSq (K j) v)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hd
  have hu : Tendsto (fun j ↦ Real.sqrt (directionSq (K j) v) * B) atTop (𝓝 0) := by
    simpa using hsq.mul_const B
  exact (ENNReal.tendsto_toReal_zero_iff (fun _ ↦ measure_ne_top _ _)).1
    (squeeze_zero' (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) hb hu)

end Measures

section PaperProblem

variable {d : ℕ} {Ω : Set (ClosedDomain.Space d)}

/-- The original CE and bounded reaction weights derive a common eventual trace bound,
even when the transport weights change arbitrarily. No trace or TV bound is assumed. -/
theorem eventually_energy_and_trace_bound (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Hstar : Matrix (Fin n) (Fin n) ℝ) (hH : Tendsto H atTop (𝓝 Hstar))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (μ : ℕ → Path Ω n k)
    (hg : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, ReactionZero.action (L j) (H j) (μ j) ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ j in atTop,
      ReactionZero.action (L j) (H j) (μ j) ≠ ⊤ ∧
      (ReactionZero.action (L j) (H j) (μ j)).toReal ≤ C.toReal ∧
      PathCoercivity.pathTrace (μ j) ≤ M := by
  obtain ⟨K, hK, hHK⟩ := exists_frobeniusSq_bound H Hstar hH
  let m0 := ClosedDomain.endpointMass P.initial
  have hm0 : 0 ≤ m0 := ClosedDomain.endpointMass_nonneg _ P.initial_positive
  have hwM : Measurable (ClosedDomain.timeWeight : ClosedDomain.Q Ω → ℝ) :=
    ClosedDomain.timeWeight.continuous.measurable
  have hw : ∀ x : ClosedDomain.Q Ω, 0 ≤ ClosedDomain.timeWeight x ∧
      ClosedDomain.timeWeight x ≤ 1 :=
    fun x ↦ ⟨ClosedDomain.timeWeight_nonneg x, ClosedDomain.timeWeight_le_one x⟩
  refine ⟨2 * m0 + 2 * K * C.toReal, by positivity, ?_⟩
  filter_upwards [hE] with j hj
  have hof : ReactionZero.action (L j) (H j) (μ j) ≤ ENNReal.ofReal C.toReal := by
    simpa only [ENNReal.ofReal_toReal hC] using hj
  refine ⟨ne_top_of_le_ne_top hC hj,
    ENNReal.toReal_le_of_le_ofReal ENNReal.toReal_nonneg hof, ?_⟩
  exact PathCoercivity.pathTrace_bound_on_sublevel (L j) (H j) (μ j) (hg j).1
    C.toReal K ENNReal.toReal_nonneg hof (hHK j) ClosedDomain.timeWeight hwM hw
    m0 hm0 (time_identity P (μ j) (hg j))

/-- Every fixed target transport-kernel direction loses genuine flux variation on the
whole original bounded-energy sequence, with both weights varying. -/
theorem fluxDirectionTV_tendsto_zero_of_eventually_bounded (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, ReactionZero.action (L j) (H j) (μ j) ≤ C)
    (v : Fin k → ℝ) (hv : Lstar.transpose *ᵥ v = 0) (i : Fin n) :
    Tendsto (fun j ↦ (fluxDirection (μ j) v i).totalVariation univ) atTop (𝓝 0) := by
  obtain ⟨M, _, hb⟩ := eventually_energy_and_trace_bound P L H Hstar hH C hC μ hg hE
  apply signedTV_tendsto_zero_of_eventual_direction_bound L Lstar hL v hv
    (fun j ↦ fluxDirection (μ j) v i) (Real.sqrt (2 * C.toReal * M))
  filter_upwards [hb] with j hj
  exact fluxDirectionTV_le_sqrt (L j) (H j) (μ j) (hg j).1 hj.1 C.toReal M
    hj.2.1 hj.2.2 v i

/-- Target reaction-kernel directions lose genuine reaction variation even if transport
weights change without converging. The original CE supplies the required trace bound. -/
theorem reactionDirectionTV_tendsto_zero_of_eventually_bounded (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, ReactionZero.action (L j) (H j) (μ j) ≤ C)
    (v : Fin n → ℝ) (hv : Hstar.transpose *ᵥ v = 0) (i : Fin n) :
    Tendsto (fun j ↦ (reactionDirection (μ j) v i).totalVariation univ) atTop (𝓝 0) := by
  obtain ⟨M, _, hb⟩ := eventually_energy_and_trace_bound P L H Hstar hH C hC μ hg hE
  apply signedTV_tendsto_zero_of_eventual_direction_bound H Hstar hH v hv
    (fun j ↦ reactionDirection (μ j) v i) (Real.sqrt (2 * C.toReal * M))
  filter_upwards [hb] with j hj
  exact reactionDirectionTV_le_sqrt (L j) (H j) (μ j) (hg j).1 hj.1 C.toReal M
    hj.2.1 hj.2.2 v i

/-- Actual Frobenius variation of `q A` vanishes along the whole sequence for arbitrary
fixed rectangular `A` whose columns lie in the target transport transpose-kernel. -/
theorem rightFluxFrobeniusTV_tendsto_zero_of_eventually_bounded (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ) (Lstar : Matrix (Fin k) (Fin k) ℝ)
    (hL : Tendsto L atTop (𝓝 Lstar))
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, ReactionZero.action (L j) (H j) (μ j) ≤ C)
    (A : Matrix (Fin k) (Fin p) ℝ) (hA : Lstar.transpose * A = 0) :
    Tendsto (fun j ↦ rightFluxFrobeniusTV (μ j) A) atTop (𝓝 0) := by
  apply rightFluxFrobeniusTV_tendsto_zero
  intro i j
  have hv : Lstar.transpose *ᵥ (fun a ↦ A a j) = 0 := by
    funext b
    have hab := congrFun (congrFun hA b) j
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.zero_apply,
      Matrix.zero_apply] using hab
  exact fluxDirectionTV_tendsto_zero_of_eventually_bounded P L Lstar hL H Hstar hH C hC
    μ hg hE (fun a ↦ A a j) hv i

/-- Actual Frobenius variation of `R A` vanishes along the whole sequence for every fixed
matrix whose columns lie in the target reaction transpose-kernel. -/
theorem rightReactionFrobeniusTV_tendsto_zero_of_eventually_bounded (P : Problem Ω n k)
    (L : ℕ → Matrix (Fin k) (Fin k) ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (Hstar : Matrix (Fin n) (Fin n) ℝ)
    (hH : Tendsto H atTop (𝓝 Hstar)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (μ : ℕ → Path Ω n k) (hg : ∀ j, Good P (μ j))
    (hE : ∀ᶠ j in atTop, ReactionZero.action (L j) (H j) (μ j) ≤ C)
    (A : Matrix (Fin n) (Fin p) ℝ) (hA : Hstar.transpose * A = 0) :
    Tendsto (fun j ↦ rightReactionFrobeniusTV (μ j) A) atTop (𝓝 0) := by
  apply PartialReaction.rightReactionFrobeniusTV_tendsto_zero
  intro i j
  have hv : Hstar.transpose *ᵥ (fun a ↦ A a j) = 0 := by
    funext b
    have hab := congrFun (congrFun hA b) j
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.zero_apply,
      Matrix.zero_apply] using hab
  exact reactionDirectionTV_tendsto_zero_of_eventually_bounded P L H Hstar hH C hC
    μ hg hE (fun a ↦ A a j) hv i

end PaperProblem

end MatrixTransport.PartialWeights

#print axioms MatrixTransport.PartialWeights.fluxDirectionTV_sq_le
#print axioms MatrixTransport.PartialWeights.withDensity_rightFluxMeasure
#print axioms MatrixTransport.PartialWeights.rightFluxFrobeniusTV_le_sum_directionTV
#print axioms MatrixTransport.PartialWeights.eventually_energy_and_trace_bound
#print axioms MatrixTransport.PartialWeights.rightFluxFrobeniusTV_tendsto_zero_of_eventually_bounded
#print axioms MatrixTransport.PartialWeights.rightReactionFrobeniusTV_tendsto_zero_of_eventually_bounded
