import MatrixTransport.ReactionZero.DualRepresentation

/-!
# Continuous-dual representation of finite-coordinate integrated support actions

This module proves the reverse representation inequality and the resulting equality
between the canonical joint-RN integrated action and the actual continuous signed-measure dual
supremum. It covers arbitrary finite coordinate signed measures on a compact metric space,
including singular measures and infinite action, and arbitrary closed convex support sets
containing zero. It then proves weak-star sequential lower semicontinuity of the integrated
action. None of these conclusions is an assumption.

The proof constructs dense countable dual vectors and finite measurable maximizing selectors.
A finite density-weighted measure translates Euclidean L1 approximation into a pairing error.
The genuine nonexpansive closed-convex projection proved in `DualRepresentation` preserves dual
admissibility everywhere. Monotone convergence and an explicit vanishing-error argument close
the representation. This general bridge does not by itself prove the Li--Zou reaction-zero
limit: the concrete matrix support set, continuity equation, coercivity and variational limit
still need their own verified instantiations.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace MatrixTransport.ReactionZero.SelectorApproximation

variable {ι : Type*} [Fintype ι]

/-- Every finite-coordinate target containing zero admits a dense sequence starting at zero. -/
theorem exists_denseSequence_starting_zero (S : Set (ι → ℝ)) (h0 : (0 : ι → ℝ) ∈ S) :
    ∃ a : ℕ → ι → ℝ, a 0 = 0 ∧ (∀ n, a n ∈ S) ∧ S ⊆ closure (range a) := by
  let : Nonempty S := ⟨⟨0, h0⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq S
  let a : ℕ → ι → ℝ := fun n ↦ match n with
    | 0 => 0
    | n + 1 => (u n).val
  refine ⟨a, rfl, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact h0
    | succ n => exact (u n).property
  · intro b hb
    let T : Set S := {s | s.val ∈ closure (range a)}
    have hT : IsClosed T := isClosed_closure.preimage continuous_subtype_val
    have hsub : range u ⊆ T := by
      rintro s ⟨n, rfl⟩
      exact subset_closure ⟨n + 1, rfl⟩
    exact closure_minimal hsub hT (hu ⟨b, hb⟩)

theorem continuous_weightedPair_left (coeff : ι → ℝ) (v : ι → ℝ) :
    Continuous (fun a : ι → ℝ ↦ weightedPair coeff a v) := by
  unfold weightedPair
  exact continuous_finsetSum _ fun i _ ↦
    (continuous_const.mul (continuous_apply i)).mul continuous_const

/-- Passing to a dense countable subset preserves the support function, including infinite values.
The hypothesis says the sequence lies in `S` and its range is dense in `S`.
-/
theorem supportFunction_eq_countable (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (a : ℕ → ι → ℝ) (ha : ∀ n, a n ∈ S) (hd : S ⊆ closure (range a)) (v : ι → ℝ) :
    supportFunction coeff S v = ⨆ n, ENNReal.ofReal (weightedPair coeff (a n) v) := by
  apply le_antisymm
  · refine iSup_le fun b ↦ iSup_le fun hb ↦ ?_
    let T : Set (ι → ℝ) :=
      {b | ENNReal.ofReal (weightedPair coeff b v) ≤
        ⨆ n, ENNReal.ofReal (weightedPair coeff (a n) v)}
    have hT : IsClosed T := isClosed_Iic.preimage
      (ENNReal.continuous_ofReal.comp (continuous_weightedPair_left coeff v))
    have hsub : range a ⊆ T := by
      rintro b ⟨n, rfl⟩
      exact le_iSup (fun n ↦ ENNReal.ofReal (weightedPair coeff (a n) v)) n
    exact closure_minimal hsub hT (hd hb)
  · exact iSup_le fun n ↦ supportFunction_fenchel coeff S v (a n) (ha n)

/-- A selector among the first `n+1` dual vectors, breaking ties in favor of the old selector. -/
def finiteSelector (coeff : ι → ℝ) (a : ℕ → ι → ℝ) (v : ι → ℝ) : ℕ → ι → ℝ
  | 0 => a 0
  | n + 1 => if weightedPair coeff (a (n + 1)) v ≤
      weightedPair coeff (finiteSelector coeff a v n) v
    then finiteSelector coeff a v n else a (n + 1)

theorem finiteSelector_index (coeff : ι → ℝ) (a : ℕ → ι → ℝ) (v : ι → ℝ) (n : ℕ) :
    ∃ m ≤ n, finiteSelector coeff a v n = a m := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    simp only [finiteSelector]
    split_ifs
    · obtain ⟨m, hm, he⟩ := ih
      exact ⟨m, hm.trans (Nat.le_succ _), he⟩
    · exact ⟨n + 1, le_rfl, rfl⟩

theorem finiteSelector_mem (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (a : ℕ → ι → ℝ) (ha : ∀ n, a n ∈ S) (v : ι → ℝ) (n : ℕ) :
    finiteSelector coeff a v n ∈ S := by
  obtain ⟨m, _, he⟩ := finiteSelector_index coeff a v n
  rw [he]
  exact ha m

theorem finiteSelector_pair_le_succ (coeff : ι → ℝ) (a : ℕ → ι → ℝ)
    (v : ι → ℝ) (n : ℕ) :
    weightedPair coeff (finiteSelector coeff a v n) v ≤
      weightedPair coeff (finiteSelector coeff a v (n + 1)) v := by
  simp only [finiteSelector]
  split_ifs with h
  · rfl
  · exact (not_le.mp h).le

theorem finiteSelector_pair_monotone (coeff : ι → ℝ) (a : ℕ → ι → ℝ) (v : ι → ℝ) :
    Monotone (fun n ↦ weightedPair coeff (finiteSelector coeff a v n) v) :=
  monotone_nat_of_le_succ (finiteSelector_pair_le_succ coeff a v)

theorem own_pair_le_finiteSelector_pair (coeff : ι → ℝ) (a : ℕ → ι → ℝ)
    (v : ι → ℝ) (n : ℕ) :
    weightedPair coeff (a n) v ≤ weightedPair coeff (finiteSelector coeff a v n) v := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [finiteSelector]
    split_ifs with h
    · exact h
    · rfl

theorem pair_le_finiteSelector_pair (coeff : ι → ℝ) (a : ℕ → ι → ℝ)
    (v : ι → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    weightedPair coeff (a m) v ≤ weightedPair coeff (finiteSelector coeff a v n) v :=
  (own_pair_le_finiteSelector_pair coeff a v m).trans
    (finiteSelector_pair_monotone coeff a v hmn)

theorem finiteSelector_pair_nonneg (coeff : ι → ℝ) (a : ℕ → ι → ℝ)
    (ha0 : a 0 = 0) (v : ι → ℝ) (n : ℕ) :
    0 ≤ weightedPair coeff (finiteSelector coeff a v n) v := by
  have h := pair_le_finiteSelector_pair coeff a v (Nat.zero_le n)
  simpa [ha0, weightedPair] using h

theorem supportFunction_eq_iSup_finiteSelector (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (a : ℕ → ι → ℝ) (ha : ∀ n, a n ∈ S) (hd : S ⊆ closure (range a)) (v : ι → ℝ) :
    supportFunction coeff S v =
      ⨆ n, ENNReal.ofReal (weightedPair coeff (finiteSelector coeff a v n) v) := by
  apply le_antisymm
  · rw [supportFunction_eq_countable coeff S a ha hd v]
    refine iSup_le fun n ↦ ?_
    exact (ENNReal.ofReal_le_ofReal (own_pair_le_finiteSelector_pair coeff a v n)).trans
      (le_iSup (fun n ↦ ENNReal.ofReal (weightedPair coeff (finiteSelector coeff a v n) v)) n)
  · exact iSup_le fun n ↦ supportFunction_fenchel coeff S v _
      (finiteSelector_mem coeff S a ha v n)

section MeasurableSelectors

variable {X : Type*} [MeasurableSpace X]

theorem measurable_weightedPair_fields (coeff : ι → ℝ) {u v : X → ι → ℝ}
    (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun x ↦ weightedPair coeff (u x) (v x)) := by
  unfold weightedPair
  exact Finset.measurable_fun_sum _ fun i _ ↦
    (measurable_const.mul ((measurable_pi_apply i).comp hu)).mul
      ((measurable_pi_apply i).comp hv)

theorem measurable_finiteSelector (coeff : ι → ℝ) (a : ℕ → ι → ℝ)
    {v : X → ι → ℝ} (hv : Measurable v) (n : ℕ) :
    Measurable (fun x ↦ finiteSelector coeff a (v x) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.piecewise (measurableSet_le
      (measurable_weightedPair_fields coeff measurable_const hv)
      (measurable_weightedPair_fields coeff ih hv)) measurable_const

/-- Monotone convergence reduces the genuine integrated support to integrals of finite selectors.
This holds with arbitrary extended values, so no finite-action assumption occurs.
-/
theorem lintegral_support_eq_iSup_selector_integrals (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (a : ℕ → ι → ℝ) (ha : ∀ n, a n ∈ S) (hd : S ⊆ closure (range a))
    {v : X → ι → ℝ} (hv : Measurable v) (ν : Measure X) :
    (∫⁻ x, supportFunction coeff S (v x) ∂ν) =
      ⨆ n, ∫⁻ x, ENNReal.ofReal (weightedPair coeff (finiteSelector coeff a (v x) n) (v x)) ∂ν := by
  simp_rw [supportFunction_eq_iSup_finiteSelector coeff S a ha hd]
  apply lintegral_iSup
  · intro n
    exact ENNReal.measurable_ofReal.comp
      (measurable_weightedPair_fields coeff (measurable_finiteSelector coeff a hv n) hv)
  · intro m n hmn x
    exact ENNReal.ofReal_le_ofReal (finiteSelector_pair_monotone coeff a (v x) hmn)

end MeasurableSelectors

theorem finiteSelector_euclidean_bounded (coeff : ι → ℝ) (a : ℕ → ι → ℝ)
    (v : ι → ℝ) (n : ℕ) :
    ‖WithLp.toLp 2 (finiteSelector coeff a v n)‖ ≤
      ∑ m ∈ Finset.range (n + 1), ‖WithLp.toLp 2 (a m)‖ := by
  obtain ⟨m, hm, he⟩ := finiteSelector_index coeff a v n
  rw [he]
  exact Finset.single_le_sum (f := fun m : ℕ ↦ ‖WithLp.toLp 2 (a m)‖)
    (fun m _ ↦ norm_nonneg (WithLp.toLp 2 (a m)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))

/-- Scalar weight controlling the full coordinate pairing error by a Euclidean error. -/
def pairingWeight (coeff : ι → ℝ) (v : ι → ℝ) : ℝ := ∑ i, |coeff i * v i|

theorem pairingWeight_nonneg (coeff : ι → ℝ) (v : ι → ℝ) : 0 ≤ pairingWeight coeff v :=
  Finset.sum_nonneg fun i _ ↦ abs_nonneg (coeff i * v i)

theorem weightedPair_error_le (coeff : ι → ℝ) (u g v : ι → ℝ) :
    |weightedPair coeff u v - weightedPair coeff g v| ≤
      pairingWeight coeff v * ‖WithLp.toLp 2 u - WithLp.toLp 2 g‖ := by
  have he : weightedPair coeff u v - weightedPair coeff g v =
      ∑ i, (u i - g i) * (coeff i * v i) := by
    unfold weightedPair
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  calc
    |∑ i, (u i - g i) * (coeff i * v i)| ≤
        ∑ i, |(u i - g i) * (coeff i * v i)| := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le Finset.univ (fun i ↦ (u i - g i) * (coeff i * v i))
    _ ≤ ∑ i, ‖WithLp.toLp 2 u - WithLp.toLp 2 g‖ * |coeff i * v i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hi := PiLp.norm_apply_le (WithLp.toLp 2 u - WithLp.toLp 2 g) i
      change |u i - g i| ≤ ‖WithLp.toLp 2 u - WithLp.toLp 2 g‖ at hi
      exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)
    _ = pairingWeight coeff v * ‖WithLp.toLp 2 u - WithLp.toLp 2 g‖ := by
      rw [← Finset.mul_sum]
      exact mul_comm _ _

/-- Transport a closed convex coordinate target to its finite-dimensional Hilbert norm. -/
def hilbertTarget (S : Set (ι → ℝ)) (h0 : (0 : ι → ℝ) ∈ S)
    (hc : IsClosed S) (hconv : Convex ℝ S) :
    ConvexProjection.Target (EuclideanSpace ℝ ι) where
  carrier := WithLp.ofLp ⁻¹' S
  nonempty := ⟨0, by simpa using h0⟩
  closed := hc.preimage (PiLp.continuous_ofLp 2 (fun _ : ι ↦ ℝ))
  convex := hconv.linear_preimage (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap

section PairingWeightMeasure

variable {X : Type*} [MeasurableSpace X]

theorem measurable_pairingWeight (coeff : ι → ℝ) {v : X → ι → ℝ} (hv : Measurable v) :
    Measurable (fun x ↦ pairingWeight coeff (v x)) :=
  Finset.measurable_fun_sum _ fun i _ ↦
    (measurable_const.mul ((measurable_pi_apply i).comp hv)).abs

theorem integrable_pairingWeight (coeff : ι → ℝ) {v : X → ι → ℝ} {ρ : Measure X}
    (hv : ∀ i, Integrable (fun x ↦ v x i) ρ) :
    Integrable (fun x ↦ pairingWeight coeff (v x)) ρ :=
  integrable_finsetSum _ fun i _ ↦ ((hv i).const_mul (coeff i)).abs

theorem isFiniteMeasure_pairingWeight (coeff : ι → ℝ) {v : X → ι → ℝ} {ρ : Measure X}
    (hv : ∀ i, Integrable (fun x ↦ v x i) ρ) :
    IsFiniteMeasure (ρ.withDensity fun x ↦ ENNReal.ofReal (pairingWeight coeff (v x))) :=
  isFiniteMeasure_withDensity
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt
      (integrable_pairingWeight coeff hv).hasFiniteIntegral).ne

end PairingWeightMeasure

section WeightedContinuousApproximation

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [CompactSpace X] [BorelSpace X]

omit [MeasurableSpace X] [MetricSpace X] [CompactSpace X] [BorelSpace X] in
theorem finiteSelector_coordinate_bounded (coeff : ι → ℝ) (a : ℕ → ι → ℝ)
    (v : X → ι → ℝ) (n : ℕ) (i : ι) :
    ∃ C : ℝ, ∀ x, |finiteSelector coeff a (v x) n i| ≤ C := by
  refine ⟨∑ m ∈ Finset.range (n + 1), |a m i|, ?_⟩
  intro x
  obtain ⟨m, hm, he⟩ := finiteSelector_index coeff a (v x) n
  rw [he]
  exact Finset.single_le_sum (f := fun m : ℕ ↦ |a m i|)
    (fun m _ ↦ abs_nonneg (a m i)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))

/-- Approximate an actual finite maximizing field by an admissible continuous field, with the
error measured by the original density pairing. All target constraints hold everywhere.
-/
theorem exists_continuous_selector_pairing_approximation (coeff : ι → ℝ)
    (S : Set (ι → ℝ)) (h0 : (0 : ι → ℝ) ∈ S) (hc : IsClosed S) (hconv : Convex ℝ S)
    (a : ℕ → ι → ℝ) (ha : ∀ n, a n ∈ S) {v : X → ι → ℝ}
    (hvM : Measurable v) (ρ : Measure X) (hvI : ∀ i, Integrable (fun x ↦ v x i) ρ)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(X, ι → ℝ), (∀ x, g x ∈ S) ∧
      (∫ x, |weightedPair coeff (finiteSelector coeff a (v x) n) (v x) -
        weightedPair coeff (g x) (v x)| ∂ρ) ≤ ε := by
  let ν := ρ.withDensity (fun x ↦ ENNReal.ofReal (pairingWeight coeff (v x)))
  have : IsFiniteMeasure ν := isFiniteMeasure_pairingWeight coeff hvI
  let U : X → EuclideanSpace ℝ ι := fun x ↦
    WithLp.toLp 2 (finiteSelector coeff a (v x) n)
  let B : ℝ := ∑ m ∈ Finset.range (n + 1), ‖WithLp.toLp 2 (a m)‖
  have hUM : Measurable U :=
    (PiLp.continuous_toLp 2 (fun _ : ι ↦ ℝ)).measurable.comp
      (measurable_finiteSelector coeff a hvM n)
  have hUI : Integrable U ν := (integrable_const B).mono' hUM.aestronglyMeasurable
    (ae_of_all _ fun x ↦ finiteSelector_euclidean_bounded coeff a (v x) n)
  let K := hilbertTarget S h0 hc hconv
  obtain ⟨G, hGS, herr⟩ := ConvexProjection.exists_continuous_target_approximation K hUI
    (fun x ↦ finiteSelector_mem coeff S a ha (v x) n) hε
  let g : C(X, ι → ℝ) :=
    ⟨fun x ↦ WithLp.ofLp (G x), (PiLp.continuous_ofLp 2 (fun _ : ι ↦ ℝ)).comp G.continuous⟩
  have hGI : Integrable G ν := (integrable_const ‖G‖).mono' G.continuous.aestronglyMeasurable
    (ae_of_all _ fun x ↦ G.norm_coe_le_norm x)
  have hwM : Measurable (fun x ↦ ENNReal.ofReal (pairingWeight coeff (v x))) :=
    ENNReal.measurable_ofReal.comp (measurable_pairingWeight coeff hvM)
  have hwlt : ∀ᵐ x ∂ρ, ENNReal.ofReal (pairingWeight coeff (v x)) < ∞ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hWI : Integrable (fun x ↦ pairingWeight coeff (v x) * ‖U x - G x‖) ρ := by
    have h := (integrable_withDensity_iff_integrable_smul' hwM hwlt).mp (hUI.sub hGI).norm
    simpa only [ENNReal.toReal_ofReal (pairingWeight_nonneg coeff _), smul_eq_mul,
      Pi.sub_apply] using h
  have hWint : (∫ x, pairingWeight coeff (v x) * ‖U x - G x‖ ∂ρ) =
      ∫ x, ‖U x - G x‖ ∂ν := by
    symm
    rw [integral_withDensity_eq_integral_toReal_smul hwM hwlt]
    simp only [ENNReal.toReal_ofReal (pairingWeight_nonneg coeff _), smul_eq_mul]
  refine ⟨g, hGS, ?_⟩
  calc
    (∫ x, |weightedPair coeff (finiteSelector coeff a (v x) n) (v x) -
        weightedPair coeff (g x) (v x)| ∂ρ) ≤
        ∫ x, pairingWeight coeff (v x) * ‖U x - G x‖ ∂ρ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) hWI
      apply ae_of_all
      intro x
      simpa only [g, U, ContinuousMap.coe_mk, WithLp.toLp_ofLp] using
        weightedPair_error_le coeff (finiteSelector coeff a (v x) n) (g x) (v x)
    _ = ∫ x, ‖U x - G x‖ ∂ν := hWint
    _ ≤ ε := herr

/-- The reverse representation inequality for all finite-coordinate signed measures.
The support set is any closed convex set containing zero. No finiteness of the action is assumed.
-/
theorem integratedSupport_le_continuousDual (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (h0 : (0 : ι → ℝ) ∈ S) (hc : IsClosed S) (hconv : Convex ℝ S)
    (μ : ι → SignedMeasure X) :
    Duality.integratedSupport coeff S μ ≤ Duality.continuousDual coeff S μ := by
  obtain ⟨a, ha0, ha, hd⟩ := exists_denseSequence_starting_zero S h0
  let v := Duality.density μ
  let ρ := jointReference μ
  have hvM : Measurable v := Duality.measurable_density μ
  have hvI : ∀ i, Integrable (fun x ↦ v x i) ρ := integrable_rnDeriv_jointReference μ
  change (∫⁻ x, supportFunction coeff S (v x) ∂ρ) ≤ _
  rw [lintegral_support_eq_iSup_selector_integrals coeff S a ha hd hvM ρ]
  refine iSup_le fun n ↦ ?_
  let u : X → ι → ℝ := fun x ↦ finiteSelector coeff a (v x) n
  have huM : ∀ i, Measurable (fun x ↦ u x i) :=
    fun i ↦ (measurable_pi_apply i).comp (measurable_finiteSelector coeff a hvM n)
  have huB : ∀ i, ∃ C : ℝ, ∀ x, |u x i| ≤ C :=
    finiteSelector_coordinate_bounded coeff a v n
  have hpuI : Integrable (fun x ↦ weightedPair coeff (u x) (v x)) ρ :=
    Duality.integrable_weightedPair coeff μ u huM huB
  have hpu0 : ∀ᵐ x ∂ρ, 0 ≤ weightedPair coeff (u x) (v x) :=
    ae_of_all _ fun x ↦ finiteSelector_pair_nonneg coeff a ha0 (v x) n
  change (∫⁻ x, ENNReal.ofReal (weightedPair coeff (u x) (v x)) ∂ρ) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hpuI hpu0]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨g, hg, herr⟩ := exists_continuous_selector_pairing_approximation coeff S h0 hc hconv
    a ha hvM ρ hvI n (show (0 : ℝ) < ε from hε)
  have hgM : ∀ i, Measurable (fun x ↦ g x i) :=
    fun i ↦ (Duality.coordinateTest g i).continuous.measurable
  have hgB : ∀ i, ∃ C : ℝ, ∀ x, |g x i| ≤ C :=
    Duality.continuousField_coordinate_bounded g
  have hpgI : Integrable (fun x ↦ weightedPair coeff (g x) (v x)) ρ :=
    Duality.integrable_weightedPair coeff μ g hgM hgB
  have hnorm := norm_integral_le_integral_norm (μ := ρ)
    (fun x ↦ weightedPair coeff (u x) (v x) - weightedPair coeff (g x) (v x))
  rw [integral_sub hpuI hpgI] at hnorm
  simp only [Real.norm_eq_abs] at hnorm
  have herror : (∫ x, weightedPair coeff (u x) (v x) ∂ρ) ≤
      (∫ x, weightedPair coeff (g x) (v x) ∂ρ) + ε := by
    have hle := le_abs_self ((∫ x, weightedPair coeff (u x) (v x) ∂ρ) -
      ∫ x, weightedPair coeff (g x) (v x) ∂ρ)
    have hsmall := hle.trans (hnorm.trans herr)
    linarith
  have hdual : ENNReal.ofReal (∫ x, weightedPair coeff (g x) (v x) ∂ρ) ≤
      Duality.continuousDual coeff S μ := by
    rw [← Duality.coordinatePair_eq_integral coeff μ g hgM hgB]
    unfold Duality.continuousDual
    exact le_iSup₂ (f := fun (g : C(X, ι → ℝ)) (_ : ∀ x, g x ∈ S) ↦
      ENNReal.ofReal (Duality.coordinatePair coeff μ g)) g hg
  calc
    ENNReal.ofReal (∫ x, weightedPair coeff (u x) (v x) ∂ρ) ≤
        ENNReal.ofReal ((∫ x, weightedPair coeff (g x) (v x) ∂ρ) + ε) :=
      ENNReal.ofReal_le_ofReal herror
    _ ≤ ENNReal.ofReal (∫ x, weightedPair coeff (g x) (v x) ∂ρ) + ε := by
      simpa using (ENNReal.ofReal_add_le
        (p := ∫ x, weightedPair coeff (g x) (v x) ∂ρ) (q := ε))
    _ ≤ Duality.continuousDual coeff S μ + ε := add_le_add hdual le_rfl

/-- Complete continuous-dual representation of the genuine integrated support action. -/
theorem integratedSupport_eq_continuousDual (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (h0 : (0 : ι → ℝ) ∈ S) (hc : IsClosed S) (hconv : Convex ℝ S)
    (μ : ι → SignedMeasure X) :
    Duality.integratedSupport coeff S μ = Duality.continuousDual coeff S μ :=
  le_antisymm (integratedSupport_le_continuousDual coeff S h0 hc hconv μ)
    (Duality.continuousDual_le_integratedSupport coeff S μ)

/-- Weak-star sequential lower semicontinuity of the genuine integrated action follows from the
proved representation, rather than from an equality assumed in the theorem's hypotheses.
-/
theorem integratedSupport_le_liminf (coeff : ι → ℝ) (S : Set (ι → ℝ))
    (h0 : (0 : ι → ℝ) ∈ S) (hc : IsClosed S) (hconv : Convex ℝ S)
    (μ : ℕ → ι → SignedMeasure X) (ν : ι → SignedMeasure X)
    (hμ : ∀ i (f : C(X, ℝ)),
      Tendsto (fun n ↦ signedPair (μ n i) f) atTop (𝓝 (signedPair (ν i) f))) :
    Duality.integratedSupport coeff S ν ≤
      atTop.liminf (fun n ↦ Duality.integratedSupport coeff S (μ n)) := by
  simp_rw [integratedSupport_eq_continuousDual coeff S h0 hc hconv]
  exact Duality.continuousDual_le_liminf coeff S μ ν hμ

end WeightedContinuousApproximation

#print axioms supportFunction_eq_countable
#print axioms exists_denseSequence_starting_zero
#print axioms measurable_finiteSelector
#print axioms lintegral_support_eq_iSup_selector_integrals
#print axioms weightedPair_error_le
#print axioms isFiniteMeasure_pairingWeight
#print axioms exists_continuous_selector_pairing_approximation
#print axioms integratedSupport_eq_continuousDual
#print axioms integratedSupport_le_liminf

end MatrixTransport.ReactionZero.SelectorApproximation
