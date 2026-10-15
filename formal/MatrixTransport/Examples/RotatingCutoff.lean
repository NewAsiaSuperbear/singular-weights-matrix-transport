import MatrixTransport.Examples.AffineTests

/-!
# Globally C¹ sine cutoff for rotating transport weights

The function `h(z)` is zero below `-π/2`, `(1+sin z)/2` between the breakpoints,
and one above `π/2`. It is expressed using clamping to that interval. Its
derivative vanishes at both breakpoints, and `h'² = h(1-h)` everywhere.

The spatial profile is `h((S x₀-c x₁)/ε)`, with certified coordinate-line
derivatives. The time profiles `aδ(s) = -2/(1+δ-s)` and `bδ(s) = 2/(s+δ)`
satisfy the Riccati identities on the unit interval for `δ > 0`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Asymptotics
open scoped ENNReal Matrix BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace LiZouTransport.Examples

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain

/-! ### The sine cutoff -/

/-- Clamp to `[-π/2, π/2]`. -/
def clampHalfPi (z : ℝ) : ℝ := max (-(Real.pi / 2)) (min z (Real.pi / 2))

/-- The cutoff `h`: `0` below `-π/2`, `(1 + sin z)/2` in between, `1` above `π/2`. -/
def sineCutoff (z : ℝ) : ℝ := (1 + Real.sin (clampHalfPi z)) / 2

/-- The derivative `cos (clamp z) / 2` (zero outside `(-π/2, π/2)`). -/
def sineCutoffD (z : ℝ) : ℝ := Real.cos (clampHalfPi z) / 2

theorem clampHalfPi_of_mem {z : ℝ} (h1 : -(Real.pi / 2) ≤ z) (h2 : z ≤ Real.pi / 2) :
    clampHalfPi z = z := by
  unfold clampHalfPi
  rw [min_eq_left h2, max_eq_right h1]

theorem clampHalfPi_of_ge {z : ℝ} (h : Real.pi / 2 ≤ z) : clampHalfPi z = Real.pi / 2 := by
  unfold clampHalfPi
  rw [min_eq_right h]
  exact max_eq_right (by linarith [Real.pi_pos])

theorem clampHalfPi_of_le {z : ℝ} (h : z ≤ -(Real.pi / 2)) : clampHalfPi z = -(Real.pi / 2) := by
  unfold clampHalfPi
  have hm : min z (Real.pi / 2) = z := min_eq_left (by linarith [Real.pi_pos])
  rw [hm]
  exact max_eq_left h

theorem sineCutoff_of_ge {z : ℝ} (h : Real.pi / 2 ≤ z) : sineCutoff z = 1 := by
  unfold sineCutoff
  rw [clampHalfPi_of_ge h, Real.sin_pi_div_two]
  norm_num

theorem sineCutoff_of_le {z : ℝ} (h : z ≤ -(Real.pi / 2)) : sineCutoff z = 0 := by
  unfold sineCutoff
  rw [clampHalfPi_of_le h, Real.sin_neg, Real.sin_pi_div_two]
  norm_num

theorem sineCutoffD_of_ge {z : ℝ} (h : Real.pi / 2 ≤ z) : sineCutoffD z = 0 := by
  unfold sineCutoffD
  rw [clampHalfPi_of_ge h, Real.cos_pi_div_two]
  norm_num

theorem sineCutoffD_of_le {z : ℝ} (h : z ≤ -(Real.pi / 2)) : sineCutoffD z = 0 := by
  unfold sineCutoffD
  rw [clampHalfPi_of_le h, Real.cos_neg, Real.cos_pi_div_two]
  norm_num

theorem sineCutoff_nonneg (z : ℝ) : 0 ≤ sineCutoff z := by
  unfold sineCutoff
  have := Real.neg_one_le_sin (clampHalfPi z)
  linarith

theorem sineCutoff_le_one (z : ℝ) : sineCutoff z ≤ 1 := by
  unfold sineCutoff
  have := Real.sin_le_one (clampHalfPi z)
  linarith

/-- **The identity `h'² = h(1-h)`** (the scalar form of (9.1)). -/
theorem sineCutoffD_sq (z : ℝ) : sineCutoffD z ^ 2 = sineCutoff z * (1 - sineCutoff z) := by
  unfold sineCutoffD sineCutoff
  have h := Real.sin_sq_add_cos_sq (clampHalfPi z)
  linear_combination (1 / 4 : ℝ) * h

theorem continuous_sineCutoffD : Continuous sineCutoffD := by
  unfold sineCutoffD clampHalfPi
  exact (Real.continuous_cos.comp
    (continuous_const.max (continuous_id.min continuous_const))).div_const 2

/-- **`h` is globally `C¹`**: `h' = cos (clamp z)/2` exists everywhere, including at the two
breaks `z = ±π/2`, where both one-sided derivatives are `0`. -/
theorem hasDerivAt_sineCutoff (z : ℝ) : HasDerivAt sineCutoff (sineCutoffD z) z := by
  have hp : 0 < Real.pi / 2 := by positivity
  -- interior points
  have hmid : ∀ w : ℝ, -(Real.pi / 2) < w → w < Real.pi / 2 →
      HasDerivAt sineCutoff (sineCutoffD w) w := by
    intro w h1 h2
    have h : sineCutoff =ᶠ[𝓝 w] fun v => (1 + Real.sin v) / 2 := by
      filter_upwards [Ioo_mem_nhds h1 h2] with v hv
      unfold sineCutoff
      rw [clampHalfPi_of_mem hv.1.le hv.2.le]
    have hd : HasDerivAt (fun v => (1 + Real.sin v) / 2) (Real.cos w / 2) w :=
      ((Real.hasDerivAt_sin w).const_add 1).div_const 2
    have h3 := hd.congr_of_eventuallyEq h
    unfold sineCutoffD
    rw [clampHalfPi_of_mem h1.le h2.le]
    exact h3
  -- the junction at `π/2`
  have hupper : HasDerivAt sineCutoff 0 (Real.pi / 2) := by
    have hL : HasDerivWithinAt sineCutoff 0 (Iic (Real.pi / 2)) (Real.pi / 2) := by
      have hd : HasDerivAt (fun v => (1 + Real.sin v) / 2) 0 (Real.pi / 2) := by
        have h := ((Real.hasDerivAt_sin (Real.pi / 2)).const_add 1).div_const 2
        rw [Real.cos_pi_div_two] at h
        simpa using h
      refine hd.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · refine eventually_nhdsWithin_iff.mpr ?_
        filter_upwards [Ioi_mem_nhds (show -(Real.pi / 2) < Real.pi / 2 by linarith)]
          with w hw hwI
        unfold sineCutoff
        rw [clampHalfPi_of_mem (le_of_lt hw) hwI]
      · unfold sineCutoff
        rw [clampHalfPi_of_mem (by linarith) le_rfl]
    have hR : HasDerivWithinAt sineCutoff 0 (Ici (Real.pi / 2)) (Real.pi / 2) :=
      (hasDerivAt_const (Real.pi / 2) (1 : ℝ)).hasDerivWithinAt.congr
        (fun w hw => sineCutoff_of_ge hw) (sineCutoff_of_ge le_rfl)
    have h := hL.union hR
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h
  -- the junction at `-π/2`
  have hlower : HasDerivAt sineCutoff 0 (-(Real.pi / 2)) := by
    have hL : HasDerivWithinAt sineCutoff 0 (Iic (-(Real.pi / 2))) (-(Real.pi / 2)) :=
      (hasDerivAt_const (-(Real.pi / 2)) (0 : ℝ)).hasDerivWithinAt.congr
        (fun w hw => sineCutoff_of_le hw) (sineCutoff_of_le le_rfl)
    have hR : HasDerivWithinAt sineCutoff 0 (Ici (-(Real.pi / 2))) (-(Real.pi / 2)) := by
      have hd : HasDerivAt (fun v => (1 + Real.sin v) / 2) 0 (-(Real.pi / 2)) := by
        have h := ((Real.hasDerivAt_sin (-(Real.pi / 2))).const_add 1).div_const 2
        rw [Real.cos_neg, Real.cos_pi_div_two] at h
        simpa using h
      refine hd.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · refine eventually_nhdsWithin_iff.mpr ?_
        filter_upwards [Iio_mem_nhds (show -(Real.pi / 2) < Real.pi / 2 by linarith)]
          with w hw hwI
        unfold sineCutoff
        rw [clampHalfPi_of_mem hwI (le_of_lt hw)]
      · unfold sineCutoff
        rw [clampHalfPi_of_mem le_rfl (by linarith)]
    have h := hL.union hR
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h
  rcases lt_trichotomy z (-(Real.pi / 2)) with h | h | h
  · have hev : sineCutoff =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with w hw
      exact sineCutoff_of_le (le_of_lt hw)
    rw [sineCutoffD_of_le h.le]
    exact (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq hev
  · subst h
    rw [sineCutoffD_of_le le_rfl]
    exact hlower
  · rcases lt_trichotomy z (Real.pi / 2) with h2 | h2 | h2
    · exact hmid z h h2
    · subst h2
      rw [sineCutoffD_of_ge le_rfl]
      exact hupper
    · have hev : sineCutoff =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds h2] with w hw
        exact sineCutoff_of_ge (le_of_lt hw)
      rw [sineCutoffD_of_ge h2.le]
      exact (hasDerivAt_const z (1 : ℝ)).congr_of_eventuallyEq hev

theorem continuous_sineCutoff : Continuous sineCutoff :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_sineCutoff z).continuousAt

/-! ### The spatial profile `f(x) = h(u · x / ε)` with `u = (S, -c)` -/

/-- `u · x` for `u = (S, -c)`. -/
def uSig (S c : ℝ) (x : Space 2) : ℝ := S * x 0 - c * x 1

/-- `u · eⱼ`. -/
def uDir (S c : ℝ) (j : Fin 2) : ℝ :=
  S * (EuclideanSpace.single j (1 : ℝ) : Space 2) 0 -
    c * (EuclideanSpace.single j (1 : ℝ) : Space 2) 1

@[simp] theorem uDir_zero (S c : ℝ) : uDir S c 0 = S := by
  simp [uDir, EuclideanSpace.single_apply]

@[simp] theorem uDir_one (S c : ℝ) : uDir S c 1 = -c := by
  simp [uDir, EuclideanSpace.single_apply]

theorem uSig_add_smul (S c : ℝ) (x : Space 2) (j : Fin 2) (s : ℝ) :
    uSig S c (x + s • EuclideanSpace.single j (1 : ℝ)) = uSig S c x + s * uDir S c j := by
  fin_cases j <;> simp [uSig, uDir] <;> ring

theorem continuous_uSig (S c : ℝ) : Continuous (uSig S c) := by
  unfold uSig
  exact (continuous_const.mul (continuous_coord 0)).sub (continuous_const.mul (continuous_coord 1))

/-- The globally `C¹` spatial cutoff `f_j(x) = h(u_j · x / ε_j)`. -/
def cutF (S c ε : ℝ) (x : Space 2) : ℝ := sineCutoff (uSig S c x / ε)

theorem continuous_cutF (S c ε : ℝ) : Continuous (cutF S c ε) :=
  continuous_sineCutoff.comp ((continuous_uSig S c).div_const ε)

theorem cutF_nonneg (S c ε : ℝ) (x : Space 2) : 0 ≤ cutF S c ε x := sineCutoff_nonneg _

theorem cutF_le_one (S c ε : ℝ) (x : Space 2) : cutF S c ε x ≤ 1 := sineCutoff_le_one _

/-- Derivative of `f` along the coordinate line through `x` in direction `eⱼ`. -/
theorem hasDerivAt_cutF_line (S c ε : ℝ) (x : Space 2) (j : Fin 2) :
    HasDerivAt (fun s : ℝ => cutF S c ε (x + s • EuclideanSpace.single j (1 : ℝ)))
      (sineCutoffD (uSig S c x / ε) * (uDir S c j / ε)) 0 := by
  have hz : HasDerivAt (fun s : ℝ => (uSig S c x + s * uDir S c j) / ε) (uDir S c j / ε) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).mul_const (uDir S c j)).const_add (uSig S c x)).div_const ε
    simpa using h
  have hc := (hasDerivAt_sineCutoff (uSig S c x / ε)).comp_of_eq (0 : ℝ) hz (by simp)
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show sineCutoff (uSig S c (x + s • EuclideanSpace.single j (1 : ℝ)) / ε) =
    sineCutoff ((uSig S c x + s * uDir S c j) / ε)
  rw [uSig_add_smul]

/-! ### The exact reaction profiles -/

/-- `a_δ(s) = -2/(1+δ-s)`. -/
def aTime (δ s : ℝ) : ℝ := -2 * (1 + δ - s)⁻¹

/-- `a_δ'(s) = -2/(1+δ-s)²`. -/
def aD (δ s : ℝ) : ℝ := -2 * ((1 + δ - s) ^ 2)⁻¹

/-- `b_δ(s) = 2/(s+δ)`. -/
def bTime (δ s : ℝ) : ℝ := 2 * (s + δ)⁻¹

/-- `b_δ'(s) = -2/(s+δ)²`. -/
def bD (δ s : ℝ) : ℝ := -2 * ((s + δ) ^ 2)⁻¹

theorem aD_eq (δ s : ℝ) : aD δ s = -(1 / 2 : ℝ) * aTime δ s ^ 2 := by
  unfold aD aTime
  rw [mul_pow, inv_pow]
  ring

theorem bD_eq (δ s : ℝ) : bD δ s = -(1 / 2 : ℝ) * bTime δ s ^ 2 := by
  unfold bD bTime
  rw [mul_pow, inv_pow]
  ring

theorem hasDerivAt_aTime (δ s : ℝ) (h : 1 + δ - s ≠ 0) : HasDerivAt (aTime δ) (aD δ s) s := by
  have h1 := (((hasDerivAt_id' s).const_sub (1 + δ)).inv h).const_mul (-2)
  exact h1.congr_deriv (by unfold aD; ring)

theorem hasDerivAt_bTime (δ s : ℝ) (h : s + δ ≠ 0) : HasDerivAt (bTime δ) (bD δ s) s := by
  have h1 := (((hasDerivAt_id' s).add_const δ).inv h).const_mul 2
  exact h1.congr_deriv (by unfold bD; ring)

theorem continuousOn_aTime {δ : ℝ} (hδ : 0 < δ) : ContinuousOn (aTime δ) (Icc (0 : ℝ) 1) := by
  unfold aTime
  refine continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) ?_)
  intro s hs
  have h2 : s ≤ 1 := hs.2
  intro h
  have h3 : 1 + δ - s = 0 := h
  linarith

theorem continuousOn_aD {δ : ℝ} (hδ : 0 < δ) : ContinuousOn (aD δ) (Icc (0 : ℝ) 1) := by
  unfold aD
  refine continuousOn_const.mul
    (ContinuousOn.inv₀ ((continuousOn_const.sub continuousOn_id).pow 2) ?_)
  intro s hs
  have h2 : s ≤ 1 := hs.2
  have h3 : 1 + δ - s ≠ 0 := by
    intro h
    linarith
  exact pow_ne_zero 2 h3

theorem continuousOn_bTime {δ : ℝ} (hδ : 0 < δ) : ContinuousOn (bTime δ) (Icc (0 : ℝ) 1) := by
  unfold bTime
  refine continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_id.add continuousOn_const) ?_)
  intro s hs
  have h2 : 0 ≤ s := hs.1
  intro h
  have h3 : s + δ = 0 := h
  linarith

theorem continuousOn_bD {δ : ℝ} (hδ : 0 < δ) : ContinuousOn (bD δ) (Icc (0 : ℝ) 1) := by
  unfold bD
  refine continuousOn_const.mul
    (ContinuousOn.inv₀ ((continuousOn_id.add continuousOn_const).pow 2) ?_)
  intro s hs
  have h2 : 0 ≤ s := hs.1
  have h3 : s + δ ≠ 0 := by
    intro h
    linarith
  exact pow_ne_zero 2 h3

/-- Derivative at `0` of a shifted function. -/
theorem hasDerivAt_shift {f : ℝ → ℝ} {f' a : ℝ} (h : HasDerivAt f f' a) :
    HasDerivAt (fun s => f (a + s)) f' 0 := by
  have h2 := h.comp_of_eq (0 : ℝ) ((hasDerivAt_id' (0 : ℝ)).const_add a) (by simp)
  exact h2.congr_deriv (by simp)

/-- A function of the time coordinate alone is continuous on the closed domain. -/
theorem continuousOn_fst_comp {d : ℕ} {Ω : Set (Space d)} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    ContinuousOn (fun p : Ambient d => g p.1) (domain Ω) :=
  hg.comp continuous_fst.continuousOn (fun p hp => hp.1)

theorem fst_mem_Ioo_of_interior {d : ℕ} {Ω : Set (Space d)} {p : Ambient d}
    (hp : p ∈ interior (domain Ω)) : p.1 ∈ Ioo (0 : ℝ) 1 := by
  unfold domain at hp
  rw [interior_prod_eq, interior_Icc] at hp
  exact hp.1

#print axioms hasDerivAt_sineCutoff
#print axioms sineCutoffD_sq

end LiZouTransport.Examples

end
