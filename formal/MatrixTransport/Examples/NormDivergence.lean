import MatrixTransport.Examples.AffineTests

/-!
# Frobenius-norm divergence does not ensure convergence of minima

On the closed unit disk, the scalar gradient operator has reaction weight one
and Dirac endpoints at `(0,-1)` and `(0,1)`, of equal total mass.

For every original signed Radon competitor, the affine certificate
`Φ(s,x,y) = y/4 - s/8` gives `V(diag(t,1)) ≥ 3/8`. A balanced unit atom moving
vertically has action at most `2/t²` for `diag(1,t)`. Consequently an alternating
sequence of these weights has diverging Frobenius norm while its minimum values
do not converge. Both estimates use the complete native continuity equation.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace LiZouTransport.Examples

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain

/-- `diag(t, 1)`. -/
def Lhoriz (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![t, 0; 0, 1]

/-- `diag(1, t)`. -/
def Lvert (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, t]

/-- The atom `(0,-1)` of the closed unit disk. -/
def diskA : ↥disk2 := ⟨pt2 0 (-1), (mem_disk2_iff _).2 (by norm_num [pt2_zero, pt2_one])⟩

/-- The atom `(0,1)` of the closed unit disk. -/
def diskB : ↥disk2 := ⟨pt2 0 1, (mem_disk2_iff _).2 (by norm_num [pt2_zero, pt2_one])⟩

/-- The scalar original problem `δ_{(0,-1)} → δ_{(0,1)}` on the closed unit disk. -/
def normDivProblem : Limit.Problem disk2 1 2 := diracGradProblem diskA diskB

theorem normDiv_equal_total_mass :
    endpointMass normDivProblem.initial = endpointMass normDivProblem.terminal := by
  show endpointMass (fun _ : Fin 1 × Fin 1 => diracAt diskA 1) =
    endpointMass (fun _ : Fin 1 × Fin 1 => diracAt diskB 1)
  rw [endpointMass_diracAt, endpointMass_diracAt]

/-! ### Lower bound for every competitor -/

theorem real_hj_scalar (s y : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy0 : -1 ≤ y) (hy1 : y ≤ 1) :
    (-1 / 8 : ℝ) + (1 / 2) * (1 / 4 : ℝ) ^ 2 + (1 / 2) * (-(1 / 8) * s + (1 / 4) * y) ^ 2 ≤ 0 := by
  have h1 : 0 ≤ 3 / 8 - (-(1 / 8) * s + (1 / 4) * y) := by linarith
  have h2 : 0 ≤ (-(1 / 8) * s + (1 / 4) * y) + 3 / 8 := by linarith
  nlinarith [mul_nonneg h1 h2]

/-- The pointwise Hamilton–Jacobi inequality for `Φ = y/4 - s/8`, uniformly in `t`. -/
theorem hj_norm_div (t : ℝ) (q : Q disk2) :
    (-1 / 8 : ℝ) + (1 / 2 : ℝ) * ∑ l, (∑ l', affFx 0 (1 / 4) l' * Lhoriz t l' l) ^ 2 +
      (1 / 2 : ℝ) * (affF 0 (-1 / 8) 0 (1 / 4) q.val) ^ 2 ≤ 0 := by
  have hs := q.property.1
  have hy := (mem_disk2_iff _).1 q.property.2
  have hs0 : 0 ≤ q.val.1 := hs.1
  have hs1 : q.val.1 ≤ 1 := hs.2
  have hy1 : q.val.2 1 ≤ 1 := by nlinarith [sq_nonneg (q.val.2 0)]
  have hy0 : -1 ≤ q.val.2 1 := by nlinarith [sq_nonneg (q.val.2 0)]
  have hreal := real_hj_scalar q.val.1 (q.val.2 1) hs0 hs1 hy0 hy1
  simp [Fin.sum_univ_two, affF, Lhoriz]
  nlinarith [hreal]

/-- **Lower certificate against all Radon competitors:** `V(diag(t,1)) ≥ 3/8` for every `t`. -/
theorem normDiv_lower (t : ℝ) :
    ENNReal.ofReal (3 / 8) ≤ Limit.minimumValue normDivProblem (Lhoriz t) 1 := by
  have h := affine_lower_bound disk2 diskA diskB (Lhoriz t) 0 (-1 / 8) 0 (1 / 4) (hj_norm_div t)
  have hval : affF 0 (-1 / 8) 0 (1 / 4) (1, diskB.val) -
      affF 0 (-1 / 8) 0 (1 / 4) (0, diskA.val) = 3 / 8 := by
    norm_num [affF, diskA, diskB, pt2_zero, pt2_one]
  rw [hval] at h
  exact h

/-! ### The vertical moving-atom path -/

/-- The vertical segment `s ↦ (0, -1 + 2 s)`. -/
def vertCurve : AxisCurve disk2 where
  y₀ := pt2 0 (-1)
  j := 1
  c := 2
  mem := by
    intro s hs
    refine ⟨hs, (mem_disk2_iff _).2 ?_⟩
    rw [axisPt_snd_zero, axisPt_snd_one]
    norm_num
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  interior_mem := by
    intro s hs
    refine mem_interior_domain hs
      (mem_interior_disk2 (v := (axisPt (pt2 0 (-1)) 1 s (2 * s)).2) ?_)
    rw [axisPt_snd_zero, axisPt_snd_one]
    norm_num
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2]

/-- A static interior point, carrying a zero-weight dummy atom. -/
def staticCurve : AxisCurve disk2 where
  y₀ := pt2 (1 / 2) 0
  j := 0
  c := 0
  mem := by
    intro s hs
    refine ⟨hs, (mem_disk2_iff _).2 ?_⟩
    rw [axisPt_snd_zero, axisPt_snd_one]
    norm_num
  interior_mem := by
    intro s hs
    refine mem_interior_domain hs
      (mem_interior_disk2 (v := (axisPt (pt2 (1 / 2) 0) 0 s (0 * s)).2) ?_)
    rw [axisPt_snd_zero, axisPt_snd_one]
    norm_num

/-- Unit mass travelling along the vertical segment (reaction `0`). -/
def vertAtom : TAtom disk2 where
  cur := vertCurve
  g := fun _ => 1
  g' := fun _ => 0
  hg := fun s => hasDerivAt_const s (1 : ℝ)
  hgc := continuous_const
  hg'c := continuous_const

/-- The zero-weight dummy atom (shares the two-atom machinery). -/
def zeroAtom : TAtom disk2 where
  cur := staticCurve
  g := fun _ => 0
  g' := fun _ => 0
  hg := fun s => hasDerivAt_const s (0 : ℝ)
  hgc := continuous_const
  hg'c := continuous_const

/-- The vertical path as a (one-atom) `TwoAtom`; `ψ = 1 - 2 x₀` separates the curves. -/
def vertTwoAtom : TwoAtom disk2 where
  A := vertAtom
  B := zeroAtom
  ψ := fun x => 1 - 2 * x 0
  ψ_cont := continuous_const.sub (continuous_const.mul (continuous_coord 0))
  ψ_A := by
    intro s hs
    show (1 : ℝ) - 2 * (axisPt (pt2 0 (-1)) 1 s (2 * s)).2 0 = 1
    rw [axisPt_snd_zero]
    norm_num
  ψ_B := by
    intro s hs
    show (1 : ℝ) - 2 * (axisPt (pt2 (1 / 2) 0) 0 s (0 * s)).2 0 = 0
    rw [axisPt_snd_zero]
    norm_num

/-- **The vertical path satisfies the original CE for every closed-`C¹` jet.** -/
theorem vertical_good : Limit.Good normDivProblem vertTwoAtom.path := by
  refine vertTwoAtom.good_dirac diskA diskB ?_ ?_
  · intro φ
    have hp : axisPt (pt2 0 (-1)) 1 0 (2 * 0) =
        (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ diskA).val := by
      refine Prod.ext rfl ?_
      show pt2 0 (-1) + ((2 : ℝ) * 0) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) = pt2 0 (-1)
      simp
    show (1 : ℝ) * zeroExtend φ.value (axisPt (pt2 0 (-1)) 1 0 (2 * 0)) 0 0 +
      0 * zeroExtend φ.value (axisPt (pt2 (1 / 2) 0) 0 0 (0 * 0)) 0 0 = _
    rw [hp, zeroExtend_apply_mem]
    ring
  · intro φ
    have hp : axisPt (pt2 0 (-1)) 1 1 (2 * 1) =
        (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ diskB).val := by
      refine Prod.ext rfl ?_
      show pt2 0 (-1) + ((2 : ℝ) * 1) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) = pt2 0 1
      rw [pt2_add_single_one]
      norm_num
    show (1 : ℝ) * zeroExtend φ.value (axisPt (pt2 0 (-1)) 1 1 (2 * 1)) 0 0 +
      0 * zeroExtend φ.value (axisPt (pt2 (1 / 2) 0) 0 1 (0 * 1)) 0 0 = _
    rw [hp, zeroExtend_apply_mem]
    ring

theorem vert_pointwise (t : ℝ) (ht : t ≠ 0) (m r f0 f1 : ℝ)
    (h : m + (1 / 2 : ℝ) * (f0 ^ 2 + (f1 * t) ^ 2) + (1 / 2 : ℝ) * r ^ 2 ≤ 0) :
    m + f1 * 2 ≤ 2 / t ^ 2 := by
  have hpos : 0 < t ^ 2 := lt_of_le_of_ne (sq_nonneg t) (Ne.symm (pow_ne_zero 2 ht))
  have h2 : 2 * f1 - (1 / 2 : ℝ) * t ^ 2 * f1 ^ 2 ≤ 2 / t ^ 2 := by
    first
      | rw [le_div_iff₀ hpos]
      | rw [le_div_iff hpos]
    nlinarith [sq_nonneg (t ^ 2 * f1 - 2)]
  nlinarith [sq_nonneg f0, sq_nonneg r, h, h2]

theorem vertA_bound (t : ℝ) (ht : t ≠ 0) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin 2 → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * Lvert t l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * vertTwoAtom.A.g s +
          (∑ l, f l * (if l = vertTwoAtom.A.cur.j then
            vertTwoAtom.A.g s * vertTwoAtom.A.cur.c else 0)) + r * vertTwoAtom.A.g' s ≤
          (fun _ : ℝ => 2 / t ^ 2) s := by
  intro s hs m r f h
  have e2 : ∑ l, (∑ l', f l' * Lvert t l' l) ^ 2 = f 0 ^ 2 + (f 1 * t) ^ 2 := by
    simp [Fin.sum_univ_two, Lvert]
  rw [e2] at h
  have key := vert_pointwise t ht m r (f 0) (f 1) h
  have e3 : (∑ l : Fin 2, f l * (if l = 1 then (1 : ℝ) * 2 else 0)) = f 1 * 2 := by
    simp [Fin.sum_univ_two]
  show m * 1 + (∑ l : Fin 2, f l * (if l = 1 then (1 : ℝ) * 2 else 0)) + r * 0 ≤ 2 / t ^ 2
  rw [e3]
  linarith

theorem zeroB_bound (L : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin 2 → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * L l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * vertTwoAtom.B.g s +
          (∑ l, f l * (if l = vertTwoAtom.B.cur.j then
            vertTwoAtom.B.g s * vertTwoAtom.B.cur.c else 0)) + r * vertTwoAtom.B.g' s ≤
          (fun _ : ℝ => (0 : ℝ)) s := by
  intro s hs m r f h
  show m * 0 + (∑ l, f l * (if l = 0 then (0 : ℝ) * 0 else 0)) + r * 0 ≤ 0
  simp

/-- **Upper bound of the integrated action** of the vertical path for `L = diag(1,t)`. -/
theorem vert_action_le (t : ℝ) (ht : t ≠ 0) :
    action (Lvert t) (1 : Matrix (Fin 1) (Fin 1) ℝ) vertTwoAtom.path ≤
      ENNReal.ofReal (2 / t ^ 2) := by
  have h := vertTwoAtom.action_le (Lvert t) (fun _ => 2 / t ^ 2) (fun _ => 0)
    continuous_const continuous_const (vertA_bound t ht) (zeroB_bound (Lvert t))
  simpa using h

/-- **Actual upper path:** `V(diag(1,t)) ≤ 2/t²`. -/
theorem normDiv_upper (t : ℝ) (ht : t ≠ 0) :
    Limit.minimumValue normDivProblem (Lvert t) 1 ≤ ENNReal.ofReal (2 / t ^ 2) :=
  (minimumValue_le_of_good normDivProblem (Lvert t) 1 vertTwoAtom.path vertical_good).trans
    (vert_action_le t ht)

/-! ### Non-convergence despite `‖L_j‖_F → ∞` -/

/-- Alternating weights `diag(t_j, 1)` (even `j`) and `diag(1, t_j)` (odd `j`). -/
def altL (t : ℕ → ℝ) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if Even j then Lhoriz (t j) else Lvert (t j)

theorem frobeniusSq_altL (t : ℕ → ℝ) (j : ℕ) : frobeniusSq (altL t j) = t j ^ 2 + 1 := by
  unfold altL
  split_ifs
  · simp [frobeniusSq, Fin.sum_univ_two, Lhoriz] <;> ring
  · simp [frobeniusSq, Fin.sum_univ_two, Lvert] <;> ring

/-- **Frobenius-norm divergence is insufficient.**  For any `t_j → ∞`, the alternating weights
have `‖L_j‖_F² = t_j² + 1 → ∞`, yet the minimum values `V_j` (over all original competitors)
do not converge: even `j` give `V_j ≥ 3/8`, odd `j` give `V_j ≤ 2/t_j² → 0`.  Both endpoint
total masses are `1`, so the total-matrix (Bures) target would be `0`. -/
theorem norm_divergence_nonconvergence (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    Tendsto (fun j => frobeniusSq (altL t j)) atTop atTop ∧
    (∀ j, Even j → ENNReal.ofReal (3 / 8) ≤ Limit.minimumValue normDivProblem (altL t j) 1) ∧
    (∀ j, ¬ Even j → t j ≠ 0 →
      Limit.minimumValue normDivProblem (altL t j) 1 ≤ ENNReal.ofReal (2 / t j ^ 2)) ∧
    ¬ ∃ c : ℝ≥0∞,
      Tendsto (fun j => Limit.minimumValue normDivProblem (altL t j) 1) atTop (𝓝 c) := by
  have hev : ∀ j, Even j → ENNReal.ofReal (3 / 8) ≤
      Limit.minimumValue normDivProblem (altL t j) 1 := by
    intro j hj
    have e : altL t j = Lhoriz (t j) := by simp [altL, hj]
    rw [e]
    exact normDiv_lower (t j)
  have hod : ∀ j, ¬ Even j → t j ≠ 0 →
      Limit.minimumValue normDivProblem (altL t j) 1 ≤ ENNReal.ofReal (2 / t j ^ 2) := by
    intro j hj htj
    have e : altL t j = Lvert (t j) := by simp [altL, hj]
    rw [e]
    exact normDiv_upper (t j) htj
  refine ⟨?_, hev, hod, ?_⟩
  · have hfun : (fun j => frobeniusSq (altL t j)) = fun j => t j ^ 2 + 1 :=
      funext (frobeniusSq_altL t)
    rw [hfun]
    exact Filter.tendsto_atTop_add_const_right _ 1 ((tendsto_pow_atTop two_ne_zero).comp ht)
  · rintro ⟨c, hc⟩
    have hmono2 : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
      Filter.tendsto_atTop_mono (fun m => show m ≤ 2 * m by omega) tendsto_id
    have hmono3 : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
      Filter.tendsto_atTop_mono (fun m => show m ≤ 2 * m + 1 by omega) tendsto_id
    have hevT := hc.comp hmono2
    have hodT := hc.comp hmono3
    have hlow : ENNReal.ofReal (3 / 8) ≤ c :=
      ge_of_tendsto hevT (Filter.Eventually.of_forall fun m => hev (2 * m) (even_two_mul m))
    have h1 : Tendsto (fun m : ℕ => t (2 * m + 1)) atTop atTop := ht.comp hmono3
    have h2 : Tendsto (fun m : ℕ => t (2 * m + 1) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp h1
    have h3 : Tendsto (fun m : ℕ => 2 / t (2 * m + 1) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h2
    have h4 := ENNReal.tendsto_ofReal h3
    have hupT : Tendsto (fun m : ℕ => ENNReal.ofReal (2 / t (2 * m + 1) ^ 2)) atTop (𝓝 0) := by
      simpa using h4
    have hpos : ∀ᶠ m : ℕ in atTop, 0 < t (2 * m + 1) := h1.eventually_gt_atTop 0
    have hevent : ∀ᶠ m : ℕ in atTop,
        Limit.minimumValue normDivProblem (altL t (2 * m + 1)) 1 ≤
          ENNReal.ofReal (2 / t (2 * m + 1) ^ 2) := by
      filter_upwards [hpos] with m hm
      exact hod (2 * m + 1) (by first | exact Nat.not_even_two_mul_add_one m | simp [Nat.even_add_one])
        hm.ne'
    have hupper : c ≤ 0 := le_of_tendsto_of_tendsto hodT hupT hevent
    exact absurd (hlow.trans hupper) (not_le.mpr (ENNReal.ofReal_pos.mpr (by norm_num)))

#print axioms normDiv_lower
#print axioms normDiv_upper
#print axioms frobeniusSq_altL
#print axioms norm_divergence_nonconvergence

end LiZouTransport.Examples

end
