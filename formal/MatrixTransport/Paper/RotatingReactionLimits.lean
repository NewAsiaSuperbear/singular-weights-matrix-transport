import MatrixTransport.EntrywiseBures.BuresAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Scalar formula and limits of the rotating-reaction example

The scalar parameter is `p = sin θ ^ 2`.  The value formula here is connected to the
original transport minimum by the separate rotating-reaction value theorem.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
namespace MatrixTransport.Paper.RotatingReaction

def radicand (ε p : ℝ) : ℝ := 1 + p + 2 * Real.sqrt 2 * ε ^ 2 + (2 - p) * ε ^ 4

def rawValue (ε p : ℝ) : ℝ :=
  2 * (3 - p + (2 + p) / ε ^ 2) - 4 * Real.sqrt (radicand ε p) / ε ^ 2

def baseTerm (ε p : ℝ) : ℝ :=
  2 * (3 - p) -
    4 * (2 * Real.sqrt 2 + (2 - p) * ε ^ 2) /
      (Real.sqrt (radicand ε p) + Real.sqrt (1 + p))

def excessTerm (ε p : ℝ) : ℝ :=
  2 * (p / ε) ^ 2 / (Real.sqrt (1 + p) + 1) ^ 2

def rationalizedValue (ε p : ℝ) : ℝ := baseTerm ε p + excessTerm ε p

def targetValue : ℝ := 2 * (Real.sqrt 2 - 1) ^ 2

theorem targetValue_eq : targetValue = 6 - 4 * Real.sqrt 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  unfold targetValue
  nlinarith

theorem radicand_pos {ε p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 < radicand ε p := by
  have h1 := mul_nonneg (Real.sqrt_nonneg 2) (sq_nonneg ε)
  have h2 := mul_nonneg (show 0 ≤ 2 - p by linarith) (pow_nonneg (sq_nonneg ε) 2)
  unfold radicand
  nlinarith

/-- Cancellation-free evaluation of the same exact scalar expression. -/
theorem rawValue_eq_rationalized {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    rawValue ε p = rationalizedValue ε p := by
  have he := ne_of_gt hε
  have hs := Real.sq_sqrt (show 0 ≤ 1 + p by linarith)
  have hz := Real.sq_sqrt (radicand_pos (ε := ε) hp hp1).le
  have hd1 : Real.sqrt (1 + p) + 1 ≠ 0 := by positivity
  have hd2 : Real.sqrt (radicand ε p) + Real.sqrt (1 + p) ≠ 0 := by
    have h := Real.sqrt_pos.mpr (show 0 < 1 + p by linarith)
    positivity
  have hfirst : (Real.sqrt (1 + p) - 1) * (Real.sqrt (1 + p) + 1) = p := by nlinarith
  have hsecond : (Real.sqrt (radicand ε p) - Real.sqrt (1 + p)) *
      (Real.sqrt (radicand ε p) + Real.sqrt (1 + p)) =
      ε ^ 2 * (2 * Real.sqrt 2 + (2 - p) * ε ^ 2) := by
    unfold radicand at hz ⊢
    nlinarith
  have hfirstsq := congrArg (fun x : ℝ ↦ x ^ 2) hfirst
  unfold rawValue rationalizedValue baseTerm excessTerm
  field_simp
  linear_combination
    -4 * (Real.sqrt (1 + p) + 1) ^ 2 * hsecond +
    2 * (Real.sqrt (radicand ε p) + Real.sqrt (1 + p)) * hfirstsq -
    2 * (Real.sqrt (radicand ε p) + Real.sqrt (1 + p)) *
      (Real.sqrt (1 + p) + 1) ^ 2 * hs

theorem tendsto_baseTerm {ε p : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hp : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun j ↦ baseTerm (ε j) (p j)) atTop (𝓝 targetValue) := by
  have hrad : Tendsto (fun j ↦ radicand (ε j) (p j)) atTop (𝓝 1) := by
    unfold radicand
    convert (((tendsto_const_nhds.add hp).add
      (tendsto_const_nhds.mul (hε.pow 2))).add
      ((tendsto_const_nhds.sub hp).mul (hε.pow 4))) using 1 <;> (first | rfl | (congr 1 <;> ring))
  have hs : Tendsto (fun j ↦ Real.sqrt (1 + p j)) atTop (𝓝 1) := by
    convert (tendsto_const_nhds.add hp).sqrt using 1 <;> (first | rfl | (congr 1 <;> ring))
  have hz : Tendsto (fun j ↦ Real.sqrt (radicand (ε j) (p j))) atTop (𝓝 1) := by
    convert hrad.sqrt using 1 <;> (first | rfl | (congr 1 <;> ring))
  have hnum : Tendsto (fun j ↦ 4 * (2 * Real.sqrt 2 + (2 - p j) * ε j ^ 2))
      atTop (𝓝 (8 * Real.sqrt 2)) := by
    convert (tendsto_const_nhds (x := 4)).mul
      ((tendsto_const_nhds (x := 2 * Real.sqrt 2)).add
        (((tendsto_const_nhds (x := 2)).sub hp).mul (hε.pow 2))) using 1 <;> (first | rfl | (congr 1 <;> ring))
  have hquot := hnum.div (hz.add hs) (by norm_num : (1 : ℝ) + 1 ≠ 0)
  have hfirst : Tendsto (fun j ↦ 2 * (3 - p j)) atTop (𝓝 6) := by
    convert (tendsto_const_nhds (x := 2)).mul
      ((tendsto_const_nhds (x := 3)).sub hp) using 1 <;> (first | rfl | (congr 1 <;> ring))
  unfold baseTerm
  rw [targetValue_eq]
  convert hfirst.sub hquot using 1 <;> (first | rfl | (congr 1 <;> ring))

/-- Finite limits are governed by the endpoint-specific scale `p/ε`. -/
theorem tendsto_value_finite {ε p : ℕ → ℝ} {ℓ : ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hp : Tendsto p atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ p j / ε j) atTop (𝓝 ℓ)) :
    Tendsto (fun j ↦ rationalizedValue (ε j) (p j)) atTop
      (𝓝 (targetValue + ℓ ^ 2 / 2)) := by
  have hs : Tendsto (fun j ↦ Real.sqrt (1 + p j)) atTop (𝓝 1) := by
    convert (tendsto_const_nhds.add hp).sqrt using 1 <;> (first | rfl | (congr 1 <;> ring))
  have hex : Tendsto (fun j ↦ excessTerm (ε j) (p j)) atTop (𝓝 (ℓ ^ 2 / 2)) := by
    unfold excessTerm
    convert (((tendsto_const_nhds (x := 2)).mul (hratio.pow 2)).div
      ((hs.add_const 1).pow 2) (by norm_num : ((1 : ℝ) + 1) ^ 2 ≠ 0)) using 1 <;> (first | rfl | (congr 1 <;> ring))
  exact (tendsto_baseTerm hε hp).add hex

theorem tendsto_excess_coefficient {p : ℕ → ℝ} (hp : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun j ↦ 2 / (Real.sqrt (1 + p j) + 1) ^ 2) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hs : Tendsto (fun j ↦ Real.sqrt (1 + p j)) atTop (𝓝 1) := by
    convert ((tendsto_const_nhds (x := 1)).add hp).sqrt using 1 <;> (first | rfl | norm_num)
  convert (tendsto_const_nhds (x := (2 : ℝ))).div ((hs.add_const 1).pow 2)
    (by norm_num : ((1 : ℝ) + 1) ^ 2 ≠ 0) using 1 <;> (first | rfl | norm_num)

/-- In the divergent regime the value is asymptotic to `(p/ε)^2/2`. -/
theorem tendsto_value_div_ratio_sq {ε p : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hp : Tendsto p atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ p j / ε j) atTop atTop) :
    Tendsto (fun j ↦ rationalizedValue (ε j) (p j) / ((p j / ε j) ^ 2 / 2))
      atTop (𝓝 1) := by
  have hsquare : Tendsto (fun j ↦ (p j / ε j) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hratio
  have hbase := (tendsto_baseTerm hε hp).div_atTop
    (hsquare.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have hcoeff := (tendsto_excess_coefficient hp).mul_const 2
  have hsum : Tendsto
      (fun j ↦ baseTerm (ε j) (p j) / ((p j / ε j) ^ 2 / 2) +
        (2 / (Real.sqrt (1 + p j) + 1) ^ 2) * 2) atTop (𝓝 1) := by
    convert hbase.add hcoeff using 1 <;> (first | rfl | norm_num)
  apply hsum.congr'
  filter_upwards [hratio.eventually_gt_atTop 0] with j hj
  have hn : p j / ε j ≠ 0 := ne_of_gt hj
  have hpne := (div_ne_zero_iff.mp hn).1
  have hene := (div_ne_zero_iff.mp hn).2
  unfold rationalizedValue excessTerm
  field_simp
  <;> ring

/-- The exact value diverges in the supercritical regime. -/
theorem tendsto_value_atTop {ε p : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hp : Tendsto p atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ p j / ε j) atTop atTop) :
    Tendsto (fun j ↦ rationalizedValue (ε j) (p j)) atTop atTop := by
  have hsquare : Tendsto (fun j ↦ (p j / ε j) ^ 2 / 2) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hratio).atTop_div_const
      (by norm_num : (0 : ℝ) < 2)
  have h := (tendsto_value_div_ratio_sq hε hp hratio).pos_mul_atTop
    (by norm_num : (0 : ℝ) < 1) hsquare
  apply h.congr'
  filter_upwards [hratio.eventually_gt_atTop 0] with j hj
  have hn : (p j / ε j) ^ 2 / 2 ≠ 0 := by positivity
  exact div_mul_cancel₀ _ hn

/-- The original critical angle scale implies `sin(θ)^2/ε → a^2`, including `a=0`. -/
theorem tendsto_sin_sq_div_eps {ε θ : ℕ → ℝ} {a : ℝ}
    (hεpos : ∀ j, 0 < ε j) (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ θ j / Real.sqrt (ε j)) atTop (𝓝 a)) :
    Tendsto (fun j ↦ Real.sin (θ j) ^ 2 / ε j) atTop (𝓝 (a ^ 2)) := by
  have hsinc : Tendsto (fun j ↦ Real.sinc (θ j)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using
      (Real.continuous_sinc.tendsto 0).comp hθ
  have h := (hsinc.mul hratio).pow 2
  convert h using 1
  · funext j
    have he := ne_of_gt (hεpos j)
    have hroot : Real.sqrt (ε j) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hεpos j))
    have hsquare := Real.sq_sqrt (hεpos j).le
    by_cases ht : θ j = 0
    · simp [ht]
    · rw [Real.sinc_of_ne_zero ht]
      field_simp
      nlinarith
  · norm_num

/-- Subcritical and critical limits in the manuscript's angle normalization. -/
theorem tendsto_value_angle_finite {ε θ : ℕ → ℝ} {a : ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ θ j / Real.sqrt (ε j)) atTop (𝓝 a)) :
    Tendsto (fun j ↦ rationalizedValue (ε j) (Real.sin (θ j) ^ 2)) atTop
      (𝓝 (targetValue + a ^ 4 / 2)) := by
  have hp : Tendsto (fun j ↦ Real.sin (θ j) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sin_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((Real.continuous_sin.tendsto 0).comp hθ).pow 2
  have h := tendsto_value_finite hε hp (tendsto_sin_sq_div_eps hεpos hθ hratio)
  convert h using 1
  congr 1
  ring

theorem tendsto_sin_sq_div_eps_atTop {ε θ : ℕ → ℝ}
    (hεpos : ∀ j, 0 < ε j) (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ |θ j| / Real.sqrt (ε j)) atTop atTop) :
    Tendsto (fun j ↦ Real.sin (θ j) ^ 2 / ε j) atTop atTop := by
  have hsinc : Tendsto (fun j ↦ Real.sinc (θ j) ^ 2) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sinc_zero, one_pow] using
      ((Real.continuous_sinc.tendsto 0).comp hθ).pow 2
  have hsquare : Tendsto (fun j ↦ (|θ j| / Real.sqrt (ε j)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hratio
  have h := hsinc.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hsquare
  apply h.congr
  intro j
  have he := ne_of_gt (hεpos j)
  have hsqrte := ne_of_gt (Real.sqrt_pos.mpr (hεpos j))
  have heq := Real.sq_sqrt (hεpos j).le
  by_cases ht : θ j = 0
  · simp [ht]
  · rw [Real.sinc_of_ne_zero ht]
    simp only [div_pow, sq_abs]
    field_simp
    nlinarith

/-- Supercritical angle growth gives the stated `θ^4/(2ε^2)` asymptotic. -/
theorem tendsto_value_div_angle_scale {ε θ : ℕ → ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ |θ j| / Real.sqrt (ε j)) atTop atTop) :
    Tendsto (fun j ↦ rationalizedValue (ε j) (Real.sin (θ j) ^ 2) /
      (θ j ^ 4 / (2 * ε j ^ 2))) atTop (𝓝 1) := by
  have hp : Tendsto (fun j ↦ Real.sin (θ j) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sin_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using ((Real.continuous_sin.tendsto 0).comp hθ).pow 2
  have hpscale := tendsto_sin_sq_div_eps_atTop hεpos hθ hratio
  have hval := tendsto_value_div_ratio_sq hε hp hpscale
  have hsinc : Tendsto (fun j ↦ Real.sinc (θ j) ^ 4) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sinc_zero, one_pow] using
      ((Real.continuous_sinc.tendsto 0).comp hθ).pow 4
  have h := hval.mul hsinc
  have hlim : Tendsto
      (fun j ↦ rationalizedValue (ε j) (Real.sin (θ j) ^ 2) /
        ((Real.sin (θ j) ^ 2 / ε j) ^ 2 / 2) * Real.sinc (θ j) ^ 4)
      atTop (𝓝 1) := by simpa only [one_mul] using h
  apply hlim.congr'
  filter_upwards [hpscale.eventually_gt_atTop 0, hratio.eventually_gt_atTop 0] with j hj hjθ
  have he := ne_of_gt (hεpos j)
  have ht : θ j ≠ 0 := by
    intro ht
    simp [ht] at hjθ
  have hpne : Real.sin (θ j) ≠ 0 := by
    intro hpzero
    simp [hpzero] at hj
  rw [Real.sinc_of_ne_zero ht]
  field_simp
  <;> ring

theorem tendsto_value_angle_atTop {ε θ : ℕ → ℝ}
    (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    (hθ : Tendsto θ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ |θ j| / Real.sqrt (ε j)) atTop atTop) :
    Tendsto (fun j ↦ rationalizedValue (ε j) (Real.sin (θ j) ^ 2)) atTop atTop := by
  have hp : Tendsto (fun j ↦ Real.sin (θ j) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sin_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using ((Real.continuous_sin.tendsto 0).comp hθ).pow 2
  exact tendsto_value_atTop hε hp (tendsto_sin_sq_div_eps_atTop hεpos hθ hratio)

#print axioms rawValue_eq_rationalized
#print axioms tendsto_value_finite
#print axioms tendsto_value_angle_finite
#print axioms tendsto_value_angle_atTop
#print axioms tendsto_value_div_angle_scale
end MatrixTransport.Paper.RotatingReaction
