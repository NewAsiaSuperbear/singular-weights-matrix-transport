import MatrixTransport.Paper.NativeSeparationSqrt
import MatrixTransport.GeneratorAdmissibility

/-! # Explicit scalar estimates and commutator displays for the separation proof

These identities retain the constants and the literal square-root curve printed in the paper.
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace LiZouTransport.ExpandedSeparation

/-- The displayed numerical bound for the variable-amplitude KB certificate. -/
theorem amplitude_square_bound (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 8) :
    (1 + a) ^ 2 / 2 ≤ (81 / 128 : ℝ) ∧ (81 / 128 : ℝ) < 1 := by
  constructor
  · nlinarith [sq_nonneg (a - 1 / 8)]
  · norm_num

/-- The inverse square root appearing in the exact reaction-cost bound. -/
theorem inv_sqrt_two_eq : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  field_simp
  nlinarith

/-- The literal equality between the two forms of the sharp scalar upper bound. -/
theorem sqrt_endpoint_cost_eq :
    2 * (1 - 1 / Real.sqrt 2) ^ 2 = 3 - 2 * Real.sqrt 2 := by
  rw [inv_sqrt_two_eq]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The exact scalar upper bound in the expanded square-root competitor calculation. -/
theorem sqrt_increment_cost_sharp (u : ℝ) (hu : |u| ≤ (1 / 2 : ℝ)) :
    2 * (Real.sqrt (1 + u) - 1) ^ 2 ≤ 3 - 2 * Real.sqrt 2 := by
  have h := abs_le.mp hu
  have hs0 := Real.sqrt_nonneg (1 + u)
  have hr0 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 + u by linarith)
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr15 : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by nlinarith
  have hlo : Real.sqrt 2 / 2 ≤ Real.sqrt (1 + u) := by
    have hb := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ≤ 1 + u by linarith)
    have hh : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, inv_sqrt_two_eq]
    rwa [hh] at hb
  have hhi : Real.sqrt (1 + u) ≤ 2 - Real.sqrt 2 / 2 := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hm := mul_pos (show 0 < Real.sqrt (1 + u) + (2 - Real.sqrt 2 / 2) by
      linarith) (sub_pos.mpr hlt)
    nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith

/-- The strict comparison printed before integrating over the disk. -/
theorem sqrt_endpoint_cost_lt_quarter :
    3 - 2 * Real.sqrt 2 < (1 / 4 : ℝ) := by
  have h0 := Real.sqrt_nonneg (2 : ℝ)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

/-- The scalar factor stays between its positive endpoint factors. -/
theorem sqrt_factor_interval (u s : ℝ) (hu : |u| ≤ (1 / 2 : ℝ))
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    min 1 (Real.sqrt (1 + u)) ≤ 1 + s * (Real.sqrt (1 + u) - 1) ∧
    1 + s * (Real.sqrt (1 + u) - 1) ≤ max 1 (Real.sqrt (1 + u)) ∧
    1 / Real.sqrt 2 ≤ 1 + s * (Real.sqrt (1 + u) - 1) := by
  have hb := abs_le.mp hu
  have hroot := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ≤ 1 + u by linarith)
  have hhalf : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  rw [hhalf] at hroot
  have hbase : 1 / Real.sqrt 2 ≤ (1 : ℝ) := by
    rw [inv_sqrt_two_eq]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sqrt_nonneg (2 : ℝ)]
  constructor
  · by_cases h : 1 ≤ Real.sqrt (1 + u)
    · rw [min_eq_left h]
      nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr h)]
    · have h' := le_of_not_ge h
      rw [min_eq_right h']
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h')]
  constructor
  · by_cases h : 1 ≤ Real.sqrt (1 + u)
    · rw [max_eq_right h]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h)]
    · have h' := le_of_not_ge h
      rw [max_eq_left h']
      nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr h')]
  · have hm := mul_nonneg hs.1 (sub_nonneg.mpr hroot)
    have hn := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hbase)
    nlinarith

/-- The first literal two-by-two commutator expansion; no symmetry is needed. -/
theorem generator_zero_commutator (a b c d : ℝ) :
    MatrixTransport.fullL0 * !![a, b; c, d] -
      !![a, b; c, d] * MatrixTransport.fullL0 = !![0, 2 * b; -2 * c, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatrixTransport.fullL0] <;> ring

/-- The second literal commutator expansion after the first matrix is diagonal. -/
theorem generator_one_diagonal_commutator (a d : ℝ) :
    MatrixTransport.fullL1 * !![a, 0; 0, d] -
      !![a, 0; 0, d] * MatrixTransport.fullL1 = !![0, d - a; a - d, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatrixTransport.fullL1]

/-- The real-valued half-period identity used in the expanded oscillatory-limit argument. -/
theorem cosine_half_period_identity (a : MatrixTransport.Spatial → ℝ)
    (ha : Continuous a) (haS : HasCompactSupport a) (k : ℝ) (hk : 0 < k) :
    (∫ x : MatrixTransport.Spatial, a x * Real.cos (k * x 0)) =
      (1 / 2 : ℝ) * ∫ x : MatrixTransport.Spatial,
        (a x - a (x + (Real.pi / k) • MatrixTransport.e1)) * Real.cos (k * x 0) := by
  let v : MatrixTransport.Spatial := (Real.pi / k) • MatrixTransport.e1
  have hp (x : MatrixTransport.Spatial) :
      Real.cos (k * (x + v) 0) = -Real.cos (k * x 0) := by
    have he : k * (x + v) 0 = k * x 0 + Real.pi := by
      simp [v, MatrixTransport.e1]
      field_simp
    rw [he, Real.cos_add_pi]
  have hcos : Continuous (fun x : MatrixTransport.Spatial ↦ Real.cos (k * x 0)) :=
    Real.continuous_cos.comp (continuous_const.mul (MatrixTransport.continuous_coord))
  have hi : MeasureTheory.Integrable (fun x : MatrixTransport.Spatial ↦
      a x * Real.cos (k * x 0)) :=
    (ha.mul hcos).integrable_of_hasCompactSupport
      (MatrixTransport.hasCompactSupport_mul_left' _ _ haS)
  have hshift : MeasureTheory.Integrable (fun x : MatrixTransport.Spatial ↦
      a (x + v) * Real.cos (k * x 0)) := by
    convert (hi.comp_add_right v).neg using 1
    funext x
    change a (x + v) * Real.cos (k * x 0) =
      -(a (x + v) * Real.cos (k * (x + v) 0))
    erw [hp x]
    ring
  have he : (∫ x : MatrixTransport.Spatial, a (x + v) * Real.cos (k * x 0)) =
      -(∫ x : MatrixTransport.Spatial, a x * Real.cos (k * x 0)) := by
    calc
      _ = ∫ x : MatrixTransport.Spatial,
          -(a (x + v) * Real.cos (k * (x + v) 0)) := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          change a (x + v) * Real.cos (k * x 0) =
            -(a (x + v) * Real.cos (k * (x + v) 0))
          erw [hp x]
          ring
      _ = -(∫ x : MatrixTransport.Spatial,
          a (x + v) * Real.cos (k * (x + v) 0)) := MeasureTheory.integral_neg _
      _ = _ := by rw [MeasureTheory.integral_add_right_eq_self
        (fun x : MatrixTransport.Spatial ↦ a x * Real.cos (k * x 0)) v]
  change _ = (1 / 2 : ℝ) * ∫ x : MatrixTransport.Spatial,
    (a x - a (x + v)) * Real.cos (k * x 0)
  simp_rw [sub_mul]
  rw [MeasureTheory.integral_sub hi hshift, he]
  ring

/-- The actual continuous compact-support Fourier decay underlying the real cosine argument. -/
theorem continuous_compact_fourier_decay (f : MatrixTransport.Spatial → ℂ)
    (hf : Continuous f) (hfS : HasCompactSupport f) :
    Filter.Tendsto (fun w : MatrixTransport.Spatial ↦
      ∫ x : MatrixTransport.Spatial, Real.fourierChar (-(inner ℝ x w)) • f x)
      (Filter.cocompact MatrixTransport.Spatial) (nhds 0) :=
  tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support hf hfS

#print axioms amplitude_square_bound
#print axioms sqrt_endpoint_cost_eq
#print axioms sqrt_increment_cost_sharp
#print axioms sqrt_endpoint_cost_lt_quarter
#print axioms sqrt_factor_interval
#print axioms generator_zero_commutator
#print axioms generator_one_diagonal_commutator
#print axioms cosine_half_period_identity
#print axioms continuous_compact_fourier_decay

end LiZouTransport.ExpandedSeparation
