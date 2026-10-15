import MatrixTransport.Examples.RotatingCutoff

/-!
# Exact minimum jump for rotating scalar transport weights

The scalar gradient problem on the closed unit disk has reaction weight one
and Dirac endpoints at `(-1/2,0)` and `(1/2,0)`. Minima are taken over the
original signed Radon coordinates with symmetric mass and the complete native
closed-domain C¹ continuity equation.

The sine-cutoff Hamilton–Jacobi test gives `V(Lθ,ε) ≥ 4` when `ε > 0` and
`π ε ≤ sin θ`. A genuine annihilation/creation path gives the matching upper
bound for every transport weight. At the singular target `diag(1,0)`, a balanced
horizontal path has action at most `1/2`.

For `θ = √ε` and `0 < ε ≤ 1/25`, the current minimum is exactly four although
the weights converge to that singular target. The final theorem also gives the
sequence version for every positive sequence `εⱼ → 0`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Asymptotics
open scoped ENNReal Matrix BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace LiZouTransport.Examples

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain

/-! ### The rotated weight and the singular target weight -/

/-- `L = U_θ diag(1,ε) U_θᵀ`, entrywise, in terms of `S = sin θ`, `c = cos θ`. -/
def rotW (S c ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c ^ 2 + ε * S ^ 2, (1 - ε) * c * S; (1 - ε) * c * S, S ^ 2 + ε * c ^ 2]

def rotWeight (θ ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := rotW (Real.sin θ) (Real.cos θ) ε

/-- The singular target weight `L_* = diag(1,0)`. -/
def rotLstar : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

def rotMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The weight `L_ε = U_θ diag(1,ε) U_θᵀ`. -/
theorem rotWeight_eq (θ ε : ℝ) :
    rotWeight θ ε = rotMat θ * !![1, 0; 0, ε] * (rotMat θ).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotWeight, rotW, rotMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `L u = ε u` for `u = (S, -c)`: the flux Gram of a gradient along `u` is `ε² μ²`. -/
theorem rotW_flux (S c ε μ : ℝ) (h : S ^ 2 + c ^ 2 = 1) :
    ∑ l : Fin 2, (∑ l' : Fin 2, (μ * uDir S c l') * rotW S c ε l' l) ^ 2 = (ε * μ) ^ 2 := by
  have e : ∑ l : Fin 2, (∑ l' : Fin 2, (μ * uDir S c l') * rotW S c ε l' l) ^ 2 =
      (ε * μ) ^ 2 * (S ^ 2 + c ^ 2) ^ 3 := by
    simp [Fin.sum_univ_two, rotW]
    ring
  rw [e, h]
  ring

/-! ### The exact Hamilton–Jacobi identity -/

/-- The convex-combination identity: the HJ expression of `(1-f) a + f b` vanishes. -/
theorem rot_hj_real (A B A' B' f hh E : ℝ) (hA : A' = -(1 / 2 : ℝ) * A ^ 2)
    (hB : B' = -(1 / 2 : ℝ) * B ^ 2) (hhh : hh ^ 2 = f * (1 - f)) (hE : E = ((B - A) * hh) ^ 2) :
    (A' + f * (B' - A')) + (1 / 2 : ℝ) * E + (1 / 2 : ℝ) * (A + f * (B - A)) ^ 2 = 0 := by
  subst hA
  subst hB
  subst hE
  have e : ((B - A) * hh) ^ 2 = (B - A) ^ 2 * (f * (1 - f)) := by
    rw [mul_pow, hhh]
  rw [e]
  ring

/-- `Φ = a(s) + f(x) (b(s) - a(s)) = (1-f) a + f b`. -/
def rotF (S c ε δ : ℝ) (p : Ambient 2) : ℝ :=
  aTime δ p.1 + cutF S c ε p.2 * (bTime δ p.1 - aTime δ p.1)

/-- `∂ₛ Φ`. -/
def rotFt (S c ε δ : ℝ) (p : Ambient 2) : ℝ :=
  aD δ p.1 + cutF S c ε p.2 * (bD δ p.1 - aD δ p.1)

/-- `∂ⱼ Φ = (b - a) h'(u·x/ε) (uⱼ/ε)`. -/
def rotFx (S c ε δ : ℝ) (j : Fin 2) (p : Ambient 2) : ℝ :=
  (bTime δ p.1 - aTime δ p.1) * (sineCutoffD (uSig S c p.2 / ε) * (uDir S c j / ε))

/-- **The Hamilton–Jacobi inequality, as an exact identity `= 0`**, at every point and for every
`ε ≠ 0`: it follows from `h'² = h(1-h)`, `L u = ε u`, `a' = -a²/2`, `b' = -b²/2`. -/
theorem rot_hj (θ ε δ : ℝ) (hε : ε ≠ 0) (q : Ambient 2) :
    rotFt (Real.sin θ) (Real.cos θ) ε δ q +
      (1 / 2 : ℝ) * ∑ l, (∑ l', rotFx (Real.sin θ) (Real.cos θ) ε δ l' q *
        rotWeight θ ε l' l) ^ 2 +
      (1 / 2 : ℝ) * (rotF (Real.sin θ) (Real.cos θ) ε δ q) ^ 2 ≤ 0 := by
  have hSc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hflux : ∀ l' : Fin 2, rotFx (Real.sin θ) (Real.cos θ) ε δ l' q =
      ((bTime δ q.1 - aTime δ q.1) *
        (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε)) *
        uDir (Real.sin θ) (Real.cos θ) l' := by
    intro l'
    unfold rotFx
    ring
  have hsum : ∑ l : Fin 2, (∑ l' : Fin 2, rotFx (Real.sin θ) (Real.cos θ) ε δ l' q *
      rotWeight θ ε l' l) ^ 2 =
      (ε * ((bTime δ q.1 - aTime δ q.1) *
        (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε))) ^ 2 := by
    simp only [hflux]
    exact rotW_flux (Real.sin θ) (Real.cos θ) ε _ hSc
  have hcancel : ε * (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε) =
      sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) := by
    field_simp
  have hε2 : ε * ((bTime δ q.1 - aTime δ q.1) *
      (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε)) =
      (bTime δ q.1 - aTime δ q.1) * sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) := by
    calc ε * ((bTime δ q.1 - aTime δ q.1) *
          (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε))
        = (bTime δ q.1 - aTime δ q.1) *
          (ε * (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε) / ε)) := by ring
      _ = _ := by rw [hcancel]
  rw [hsum, hε2]
  have key := rot_hj_real (aTime δ q.1) (bTime δ q.1) (aD δ q.1) (bD δ q.1)
    (cutF (Real.sin θ) (Real.cos θ) ε q.2)
    (sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε))
    (((bTime δ q.1 - aTime δ q.1) *
      sineCutoffD (uSig (Real.sin θ) (Real.cos θ) q.2 / ε)) ^ 2)
    (aD_eq δ q.1) (bD_eq δ q.1) (sineCutoffD_sq _) rfl
  unfold rotFt rotF
  linarith [key]

/-! ### Derivative and continuity certificates (original closed-domain test class) -/

theorem hasDerivAt_rotF_time (S c ε δ : ℝ) (p : Ambient 2) (hp : p.1 ∈ Ioo (0 : ℝ) 1)
    (hδ : 0 < δ) :
    HasDerivAt (fun s => rotF S c ε δ (timeLine p s)) (rotFt S c ε δ p) 0 := by
  have h1 : 1 + δ - p.1 ≠ 0 := by
    have h := hp.2
    intro h'
    linarith
  have h2 : p.1 + δ ≠ 0 := by
    have h := hp.1
    intro h'
    linarith
  have ha := hasDerivAt_shift (hasDerivAt_aTime δ p.1 h1)
  have hb := hasDerivAt_shift (hasDerivAt_bTime δ p.1 h2)
  have h3 := ha.add ((hb.sub ha).const_mul (cutF S c ε p.2))
  exact h3.congr_deriv (by unfold rotFt; ring)

theorem hasDerivAt_rotF_space (S c ε δ : ℝ) (p : Ambient 2) (j : Fin 2) :
    HasDerivAt (fun s => rotF S c ε δ (spaceLine p j s)) (rotFx S c ε δ j p) 0 := by
  have hc := hasDerivAt_cutF_line S c ε p.2 j
  have h3 := (hc.mul_const (bTime δ p.1 - aTime δ p.1)).const_add (aTime δ p.1)
  exact h3.congr_deriv (by unfold rotFx; ring)

theorem continuousOn_rotF (S c ε δ : ℝ) (hδ : 0 < δ) :
    ContinuousOn (rotF S c ε δ) (domain disk2) := by
  unfold rotF
  have ha : ContinuousOn (fun p : Ambient 2 => aTime δ p.1) (domain disk2) :=
    continuousOn_fst_comp (continuousOn_aTime hδ)
  have hb : ContinuousOn (fun p : Ambient 2 => bTime δ p.1) (domain disk2) :=
    continuousOn_fst_comp (continuousOn_bTime hδ)
  have hf : ContinuousOn (fun p : Ambient 2 => cutF S c ε p.2) (domain disk2) :=
    ((continuous_cutF S c ε).comp continuous_snd).continuousOn
  exact ha.add (hf.mul (hb.sub ha))

theorem continuousOn_rotFt (S c ε δ : ℝ) (hδ : 0 < δ) :
    ContinuousOn (rotFt S c ε δ) (domain disk2) := by
  unfold rotFt
  have ha : ContinuousOn (fun p : Ambient 2 => aD δ p.1) (domain disk2) :=
    continuousOn_fst_comp (continuousOn_aD hδ)
  have hb : ContinuousOn (fun p : Ambient 2 => bD δ p.1) (domain disk2) :=
    continuousOn_fst_comp (continuousOn_bD hδ)
  have hf : ContinuousOn (fun p : Ambient 2 => cutF S c ε p.2) (domain disk2) :=
    ((continuous_cutF S c ε).comp continuous_snd).continuousOn
  exact ha.add (hf.mul (hb.sub ha))

theorem continuousOn_rotFx (S c ε δ : ℝ) (hδ : 0 < δ) (j : Fin 2) :
    ContinuousOn (rotFx S c ε δ j) (domain disk2) := by
  unfold rotFx
  have ha : ContinuousOn (fun p : Ambient 2 => aTime δ p.1) (domain disk2) :=
    continuousOn_fst_comp (continuousOn_aTime hδ)
  have hb : ContinuousOn (fun p : Ambient 2 => bTime δ p.1) (domain disk2) :=
    continuousOn_fst_comp (continuousOn_bTime hδ)
  have hh : ContinuousOn
      (fun p : Ambient 2 => sineCutoffD (uSig S c p.2 / ε) * (uDir S c j / ε)) (domain disk2) :=
    ((continuous_sineCutoffD.comp (((continuous_uSig S c).comp continuous_snd).div_const ε)).mul
      continuous_const).continuousOn
  exact (hb.sub ha).mul hh

/-! ### The problem -/

/-- The atom `(-1/2, 0)`. -/
def rotA : ↥disk2 := ⟨pt2 (-1 / 2) 0, (mem_disk2_iff _).2 (by norm_num [pt2_zero, pt2_one])⟩

/-- The atom `(1/2, 0)`. -/
def rotB : ↥disk2 := ⟨pt2 (1 / 2) 0, (mem_disk2_iff _).2 (by norm_num [pt2_zero, pt2_one])⟩

/-- The scalar original problem `δ_{(-1/2,0)} → δ_{(1/2,0)}` on the closed unit disk. -/
def rotProblem : Limit.Problem disk2 1 2 := diracGradProblem rotA rotB

/-! ### Lower bound `V ≥ 4` -/

theorem rotF_endpoints (θ ε δ : ℝ) (hε : 0 < ε) (hS : Real.pi * ε ≤ Real.sin θ) :
    rotF (Real.sin θ) (Real.cos θ) ε δ (1, rotB.val) -
      rotF (Real.sin θ) (Real.cos θ) ε δ (0, rotA.val) = 4 * (1 + δ)⁻¹ := by
  have hb : cutF (Real.sin θ) (Real.cos θ) ε rotB.val = 1 := by
    unfold cutF
    apply sineCutoff_of_ge
    have hu : uSig (Real.sin θ) (Real.cos θ) rotB.val = Real.sin θ * (1 / 2) := by
      simp [uSig, rotB] <;> ring
    rw [hu]
    first
      | rw [le_div_iff₀ hε]
      | rw [le_div_iff hε]
    nlinarith [hS]
  have ha : cutF (Real.sin θ) (Real.cos θ) ε rotA.val = 0 := by
    unfold cutF
    apply sineCutoff_of_le
    have hu : uSig (Real.sin θ) (Real.cos θ) rotA.val = -(Real.sin θ * (1 / 2)) := by
      simp [uSig, rotA] <;> ring
    rw [hu]
    first
      | rw [div_le_iff₀ hε]
      | rw [div_le_iff hε]
    nlinarith [hS]
  have e : rotF (Real.sin θ) (Real.cos θ) ε δ (1, rotB.val) -
      rotF (Real.sin θ) (Real.cos θ) ε δ (0, rotA.val) =
      (aTime δ 1 + 1 * (bTime δ 1 - aTime δ 1)) - (aTime δ 0 + 0 * (bTime δ 0 - aTime δ 0)) := by
    show (aTime δ 1 + cutF (Real.sin θ) (Real.cos θ) ε rotB.val * (bTime δ 1 - aTime δ 1)) -
      (aTime δ 0 + cutF (Real.sin θ) (Real.cos θ) ε rotA.val * (bTime δ 0 - aTime δ 0)) = _
    rw [ha, hb]
  rw [e]
  simp only [aTime, bTime, sub_zero]
  ring

theorem rot_lower_delta (θ ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hS : Real.pi * ε ≤ Real.sin θ) :
    ENNReal.ofReal (4 * (1 + δ)⁻¹) ≤ Limit.minimumValue rotProblem (rotWeight θ ε) 1 := by
  have h := diracGradProblem_lower_bound rotA rotB (rotWeight θ ε)
    (rotF (Real.sin θ) (Real.cos θ) ε δ) (rotFt (Real.sin θ) (Real.cos θ) ε δ)
    (fun j => rotFx (Real.sin θ) (Real.cos θ) ε δ j)
    (continuousOn_rotF _ _ _ δ hδ) (continuousOn_rotFt _ _ _ δ hδ)
    (fun j => continuousOn_rotFx _ _ _ δ hδ j)
    (fun p hp => hasDerivAt_rotF_time _ _ _ δ p.val (fst_mem_Ioo_of_interior hp) hδ)
    (fun p j _ => hasDerivAt_rotF_space _ _ _ δ p.val j)
    (fun q => rot_hj θ ε δ hε.ne' q.val)
  rw [rotF_endpoints θ ε δ hε hS] at h
  exact h

/-- **Lower certificate against all Radon competitors:** `V ≥ 4` as soon as `π ε ≤ sin θ`. -/
theorem rot_lower_exact (θ ε : ℝ) (hε : 0 < ε) (hS : Real.pi * ε ≤ Real.sin θ) :
    ENNReal.ofReal 4 ≤ Limit.minimumValue rotProblem (rotWeight θ ε) 1 := by
  refine ofReal_le_of_forall_pos_sub 4 _ (fun e he => ?_)
  have hδ : 0 < e / 4 := by positivity
  have h := rot_lower_delta θ ε (e / 4) hε hδ hS
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
  have hpos : 0 < 1 + e / 4 := by linarith
  have hinv : (1 + e / 4) * (1 + e / 4)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hy : 0 < (1 + e / 4)⁻¹ := inv_pos.2 hpos
  nlinarith [hinv, sq_nonneg e, hy, hpos]

/-! ### Upper bound `V ≤ 4`: annihilation / creation -/

/-- A static atom at an interior point `(x, y)` of the disk. -/
def staticCurveAt (x y : ℝ) (hxy : x ^ 2 + y ^ 2 < 1) : AxisCurve disk2 where
  y₀ := pt2 x y
  j := 0
  c := 0
  mem := by
    intro s hs
    refine ⟨hs, (mem_disk2_iff _).2 ?_⟩
    have h0 : (axisPt (pt2 x y) 0 s (0 * s)).2 0 = x := by
      rw [axisPt_snd_zero]
      simp
    have h1 : (axisPt (pt2 x y) 0 s (0 * s)).2 1 = y := by
      rw [axisPt_snd_one]
      simp
    rw [h0, h1]
    exact hxy.le
  interior_mem := by
    intro s hs
    refine mem_interior_domain hs
      (mem_interior_disk2 (v := (axisPt (pt2 x y) 0 s (0 * s)).2) ?_)
    have h0 : (axisPt (pt2 x y) 0 s (0 * s)).2 0 = x := by
      rw [axisPt_snd_zero]
      simp
    have h1 : (axisPt (pt2 x y) 0 s (0 * s)).2 1 = y := by
      rw [axisPt_snd_one]
      simp
    rw [h0, h1]
    exact hxy

theorem hasDerivAt_oneSub_mul_self (s : ℝ) :
    HasDerivAt (fun x : ℝ => (1 - x) * (1 - x)) (-2 * (1 - s)) s :=
  (((hasDerivAt_id' s).const_sub 1).mul ((hasDerivAt_id' s).const_sub 1)).congr_deriv
    (by ring)

theorem hasDerivAt_mul_self' (s : ℝ) : HasDerivAt (fun x : ℝ => x * x) (2 * s) s :=
  ((hasDerivAt_id' s).mul (hasDerivAt_id' s)).congr_deriv (by ring)

/-- Mass `(1-s)²` annihilated at `(-1/2, 0)`, reaction `-2(1-s)`. -/
def annihAtom : TAtom disk2 where
  cur := staticCurveAt (-1 / 2) 0 (by norm_num)
  g := fun s => (1 - s) * (1 - s)
  g' := fun s => -2 * (1 - s)
  hg := hasDerivAt_oneSub_mul_self
  hgc := (continuous_const.sub continuous_id).mul (continuous_const.sub continuous_id)
  hg'c := continuous_const.mul (continuous_const.sub continuous_id)

/-- Mass `s²` created at `(1/2, 0)`, reaction `2s`. -/
def createAtom : TAtom disk2 where
  cur := staticCurveAt (1 / 2) 0 (by norm_num)
  g := fun s => s * s
  g' := fun s => 2 * s
  hg := hasDerivAt_mul_self'
  hgc := continuous_id.mul continuous_id
  hg'c := continuous_const.mul continuous_id

/-- The annihilation/creation path `G_s = (1-s)² δ_{x₀} + s² δ_{x₁}`, `q = 0`. -/
def rotStaticTwo : TwoAtom disk2 where
  A := annihAtom
  B := createAtom
  ψ := fun x => 1 / 2 - x 0
  ψ_cont := continuous_const.sub (continuous_coord 0)
  ψ_A := by
    intro s hs
    show (1 / 2 : ℝ) - (axisPt (pt2 (-1 / 2) 0) 0 s (0 * s)).2 0 = 1
    rw [axisPt_snd_zero]
    norm_num
  ψ_B := by
    intro s hs
    show (1 / 2 : ℝ) - (axisPt (pt2 (1 / 2) 0) 0 s (0 * s)).2 0 = 0
    rw [axisPt_snd_zero]
    norm_num

/-- **The annihilation/creation path satisfies the original CE for every closed-`C¹` jet.** -/
theorem rotStatic_good : Limit.Good rotProblem rotStaticTwo.path := by
  refine rotStaticTwo.good_dirac rotA rotB ?_ ?_
  · intro φ
    have hp : axisPt (pt2 (-1 / 2) 0) 0 0 (0 * 0) =
        (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ rotA).val := by
      refine Prod.ext rfl ?_
      show pt2 (-1 / 2) 0 + ((0 : ℝ) * 0) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) =
        pt2 (-1 / 2) 0
      simp
    show ((1 - 0) * (1 - 0) : ℝ) *
        zeroExtend φ.value (axisPt (pt2 (-1 / 2) 0) 0 0 (0 * 0)) 0 0 +
      ((0 : ℝ) * 0) * zeroExtend φ.value (axisPt (pt2 (1 / 2) 0) 0 0 (0 * 0)) 0 0 = _
    rw [hp, zeroExtend_apply_mem]
    ring
  · intro φ
    have hp : axisPt (pt2 (1 / 2) 0) 0 1 (0 * 1) =
        (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ rotB).val := by
      refine Prod.ext rfl ?_
      show pt2 (1 / 2) 0 + ((0 : ℝ) * 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) =
        pt2 (1 / 2) 0
      simp
    show ((1 - 1) * (1 - 1) : ℝ) *
        zeroExtend φ.value (axisPt (pt2 (-1 / 2) 0) 0 1 (0 * 1)) 0 0 +
      ((1 : ℝ) * 1) * zeroExtend φ.value (axisPt (pt2 (1 / 2) 0) 0 1 (0 * 1)) 0 0 = _
    rw [hp, zeroExtend_apply_mem]
    ring

theorem staticA_bound (L : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin 2 → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * L l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * rotStaticTwo.A.g s +
          (∑ l, f l * (if l = rotStaticTwo.A.cur.j then
            rotStaticTwo.A.g s * rotStaticTwo.A.cur.c else 0)) +
          r * rotStaticTwo.A.g' s ≤ (fun _ : ℝ => (2 : ℝ)) s := by
  intro s hs m r f h
  have h_sumSq : 0 ≤ ∑ l, (∑ l', f l' * L l' l) ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hm : m ≤ -(1 / 2 : ℝ) * r ^ 2 := by nlinarith
  have hsum : (∑ l : Fin 2, f l * (if l = 0 then (1 - s) * (1 - s) * 0 else 0)) = 0 := by
    simp
  show m * ((1 - s) * (1 - s)) +
    (∑ l : Fin 2, f l * (if l = 0 then (1 - s) * (1 - s) * 0 else 0)) +
    r * (-2 * (1 - s)) ≤ 2
  rw [hsum]
  have hg : 0 ≤ (1 - s) * (1 - s) := mul_self_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hm hg
  nlinarith [sq_nonneg (r * (1 - s) + 2)]

theorem staticB_bound (L : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin 2 → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * L l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * rotStaticTwo.B.g s +
          (∑ l, f l * (if l = rotStaticTwo.B.cur.j then
            rotStaticTwo.B.g s * rotStaticTwo.B.cur.c else 0)) +
          r * rotStaticTwo.B.g' s ≤ (fun _ : ℝ => (2 : ℝ)) s := by
  intro s hs m r f h
  have h_sumSq : 0 ≤ ∑ l, (∑ l', f l' * L l' l) ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hm : m ≤ -(1 / 2 : ℝ) * r ^ 2 := by nlinarith
  have hsum : (∑ l : Fin 2, f l * (if l = 0 then s * s * 0 else 0)) = 0 := by
    simp
  show m * (s * s) + (∑ l : Fin 2, f l * (if l = 0 then s * s * 0 else 0)) +
    r * (2 * s) ≤ 2
  rw [hsum]
  have hg : 0 ≤ s * s := mul_self_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hm hg
  nlinarith [sq_nonneg (r * s - 2)]

theorem rotStatic_action_le (L : Matrix (Fin 2) (Fin 2) ℝ) :
    action L (1 : Matrix (Fin 1) (Fin 1) ℝ) rotStaticTwo.path ≤ ENNReal.ofReal 4 := by
  have h := rotStaticTwo.action_le L (fun _ => 2) (fun _ => 2)
    continuous_const continuous_const (staticA_bound L) (staticB_bound L)
  have e : ((2 : ℝ) + 2) = 4 := by norm_num
  simpa [e] using h

/-- **Actual upper path:** `V ≤ 4` for **every** transport weight `L`. -/
theorem rot_upper (L : Matrix (Fin 2) (Fin 2) ℝ) :
    Limit.minimumValue rotProblem L 1 ≤ ENNReal.ofReal 4 :=
  (minimumValue_le_of_good rotProblem L 1 rotStaticTwo.path rotStatic_good).trans
    (rotStatic_action_le L)

theorem rot_value_eq (θ ε : ℝ) (hε : 0 < ε) (hS : Real.pi * ε ≤ Real.sin θ) :
    Limit.minimumValue rotProblem (rotWeight θ ε) 1 = ENNReal.ofReal 4 :=
  le_antisymm (rot_upper _) (rot_lower_exact θ ε hε hS)

/-! ### The singular target: horizontal straight-line path, action `1/2` -/

/-- The horizontal segment `s ↦ (-1/2 + s, 0)`. -/
def horizCurve : AxisCurve disk2 where
  y₀ := pt2 (-1 / 2) 0
  j := 0
  c := 1
  mem := by
    intro s hs
    refine ⟨hs, (mem_disk2_iff _).2 ?_⟩
    have h0 : (axisPt (pt2 (-1 / 2) 0) 0 s (1 * s)).2 0 = -1 / 2 + s := by
      rw [axisPt_snd_zero]
      simp
    have h1 : (axisPt (pt2 (-1 / 2) 0) 0 s (1 * s)).2 1 = 0 := by
      rw [axisPt_snd_one]
      simp
    rw [h0, h1]
    nlinarith [mul_nonneg hs.1 (sub_nonneg.2 hs.2)]
  interior_mem := by
    intro s hs
    refine mem_interior_domain hs
      (mem_interior_disk2 (v := (axisPt (pt2 (-1 / 2) 0) 0 s (1 * s)).2) ?_)
    have h0 : (axisPt (pt2 (-1 / 2) 0) 0 s (1 * s)).2 0 = -1 / 2 + s := by
      rw [axisPt_snd_zero]
      simp
    have h1 : (axisPt (pt2 (-1 / 2) 0) 0 s (1 * s)).2 1 = 0 := by
      rw [axisPt_snd_one]
      simp
    rw [h0, h1]
    nlinarith [mul_pos hs.1 (sub_pos.2 hs.2)]

/-- Unit mass travelling along the horizontal segment (reaction `0`). -/
def horizAtom : TAtom disk2 where
  cur := horizCurve
  g := fun _ => 1
  g' := fun _ => 0
  hg := fun s => hasDerivAt_const s (1 : ℝ)
  hgc := continuous_const
  hg'c := continuous_const

/-- Zero-weight dummy atom at `(0, 1/2)` (shares the two-atom machinery). -/
def dummyAtom : TAtom disk2 where
  cur := staticCurveAt 0 (1 / 2) (by norm_num)
  g := fun _ => 0
  g' := fun _ => 0
  hg := fun s => hasDerivAt_const s (0 : ℝ)
  hgc := continuous_const
  hg'c := continuous_const

/-- The horizontal path as a (one-atom) `TwoAtom`; `ψ = 1 - 2 x₁` separates the curves. -/
def horizTwo : TwoAtom disk2 where
  A := horizAtom
  B := dummyAtom
  ψ := fun x => 1 - 2 * x 1
  ψ_cont := continuous_const.sub (continuous_const.mul (continuous_coord 1))
  ψ_A := by
    intro s hs
    show (1 : ℝ) - 2 * (axisPt (pt2 (-1 / 2) 0) 0 s (1 * s)).2 1 = 1
    rw [axisPt_snd_one]
    norm_num
  ψ_B := by
    intro s hs
    show (1 : ℝ) - 2 * (axisPt (pt2 0 (1 / 2)) 0 s (0 * s)).2 1 = 0
    rw [axisPt_snd_one]
    norm_num

/-- **The horizontal straight-line path satisfies the original CE for every jet.** -/
theorem horiz_good : Limit.Good rotProblem horizTwo.path := by
  refine horizTwo.good_dirac rotA rotB ?_ ?_
  · intro φ
    have hp : axisPt (pt2 (-1 / 2) 0) 0 0 (1 * 0) =
        (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ rotA).val := by
      refine Prod.ext rfl ?_
      show pt2 (-1 / 2) 0 + ((1 : ℝ) * 0) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) =
        pt2 (-1 / 2) 0
      simp
    show (1 : ℝ) * zeroExtend φ.value (axisPt (pt2 (-1 / 2) 0) 0 0 (1 * 0)) 0 0 +
      0 * zeroExtend φ.value (axisPt (pt2 0 (1 / 2)) 0 0 (0 * 0)) 0 0 = _
    rw [hp, zeroExtend_apply_mem]
    ring
  · intro φ
    have hp : axisPt (pt2 (-1 / 2) 0) 0 1 (1 * 1) =
        (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ rotB).val := by
      refine Prod.ext rfl ?_
      show pt2 (-1 / 2) 0 + ((1 : ℝ) * 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) =
        pt2 (1 / 2) 0
      rw [pt2_add_single_zero]
      norm_num
    show (1 : ℝ) * zeroExtend φ.value (axisPt (pt2 (-1 / 2) 0) 0 1 (1 * 1)) 0 0 +
      0 * zeroExtend φ.value (axisPt (pt2 0 (1 / 2)) 0 1 (0 * 1)) 0 0 = _
    rw [hp, zeroExtend_apply_mem]
    ring

theorem horizA_bound :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin 2 → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * rotLstar l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * horizTwo.A.g s +
          (∑ l, f l * (if l = horizTwo.A.cur.j then horizTwo.A.g s * horizTwo.A.cur.c else 0)) +
          r * horizTwo.A.g' s ≤ (fun _ : ℝ => (1 / 2 : ℝ)) s := by
  intro s hs m r f h
  have e2 : ∑ l, (∑ l', f l' * rotLstar l' l) ^ 2 = f 0 ^ 2 := by
    simp [Fin.sum_univ_two, rotLstar]
  rw [e2] at h
  have e3 : (∑ l : Fin 2, f l * (if l = 0 then (1 : ℝ) * 1 else 0)) = f 0 := by
    simp [Fin.sum_univ_two]
  show m * 1 + (∑ l : Fin 2, f l * (if l = 0 then (1 : ℝ) * 1 else 0)) + r * 0 ≤ 1 / 2
  rw [e3]
  nlinarith [sq_nonneg (f 0 - 1), sq_nonneg r]

theorem dummyB_bound (L : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin 2 → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * L l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * horizTwo.B.g s +
          (∑ l, f l * (if l = horizTwo.B.cur.j then horizTwo.B.g s * horizTwo.B.cur.c else 0)) +
          r * horizTwo.B.g' s ≤ (fun _ : ℝ => (0 : ℝ)) s := by
  intro s hs m r f h
  show m * 0 + (∑ l, f l * (if l = 0 then (0 : ℝ) * 0 else 0)) + r * 0 ≤ 0
  simp

theorem horiz_action_le :
    action rotLstar (1 : Matrix (Fin 1) (Fin 1) ℝ) horizTwo.path ≤ ENNReal.ofReal (1 / 2) := by
  have h := horizTwo.action_le rotLstar (fun _ => 1 / 2) (fun _ => 0)
    continuous_const continuous_const horizA_bound (dummyB_bound rotLstar)
  simpa using h

/-- **The singular target value is at most `1/2`.** -/
theorem rot_target_le : Limit.minimumValue rotProblem rotLstar 1 ≤ ENNReal.ofReal (1 / 2) :=
  (minimumValue_le_of_good rotProblem rotLstar 1 horizTwo.path horiz_good).trans horiz_action_le

/-! ### Convergence of the weights and the threshold -/

theorem rotWeight_sqrt_tendsto :
    Tendsto (fun ε : ℝ => rotWeight (Real.sqrt ε) ε) (𝓝[>] 0) (𝓝 rotLstar) := by
  have hc : Continuous (fun ε : ℝ => rotWeight (Real.sqrt ε) ε) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [rotWeight, rotW] <;> first | fun_prop | continuity
  have h0 : rotWeight 0 0 = rotLstar := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotWeight, rotW, rotLstar]
  have h := hc.tendsto 0
  have h' : Tendsto (fun ε : ℝ => rotWeight (Real.sqrt ε) ε) (𝓝 0) (𝓝 rotLstar) := by
    simpa [h0] using h
  exact h'.mono_left nhdsWithin_le_nhds

/-- The small-parameter threshold: `sin θ ≥ π ε` for `θ = √ε` small. -/
theorem pi_mul_le_sin_sqrt (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 25) :
    Real.pi * ε ≤ Real.sin (Real.sqrt ε) := by
  have hx0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 h0
  have hxx : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt h0.le
  have hx1 : Real.sqrt ε ≤ 1 / 5 := by nlinarith [hxx, hx0]
  have hs : Real.sqrt ε - Real.sqrt ε ^ 3 / 4 ≤ Real.sin (Real.sqrt ε) := by
    have h := Real.sin_gt_sub_cube hx0
    nlinarith [pow_nonneg hx0.le 3]
  have hpi := Real.pi_le_four
  have hq : 0 ≤ 1 - Real.sqrt ε ^ 2 / 4 - 4 * Real.sqrt ε := by
    nlinarith [hx0, hx1, hxx]
  have key : 4 * Real.sqrt ε ^ 2 ≤ Real.sqrt ε - Real.sqrt ε ^ 3 / 4 := by
    have h : 0 ≤ Real.sqrt ε * (1 - Real.sqrt ε ^ 2 / 4 - 4 * Real.sqrt ε) :=
      mul_nonneg hx0.le hq
    nlinarith [h]
  calc Real.pi * ε ≤ 4 * ε := mul_le_mul_of_nonneg_right hpi h0.le
    _ = 4 * Real.sqrt ε ^ 2 := by rw [hxx]
    _ ≤ Real.sqrt ε - Real.sqrt ε ^ 3 / 4 := key
    _ ≤ Real.sin (Real.sqrt ε) := hs

/-! ### The jump -/

/-- **Exact rotating-transport minimum jump (original model).**  For `0 < ε ≤ 1/25` and
`θ = √ε`, the minimum value is exactly `4`, although `L_ε → diag(1,0)` and the singular target
value is `≤ 1/2`.  Hence matrix convergence of the weights alone does not give continuity of
the minimum. -/
theorem rotating_transport_jump :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 25 →
      Limit.minimumValue rotProblem (rotWeight (Real.sqrt ε) ε) 1 = ENNReal.ofReal 4) ∧
    Limit.minimumValue rotProblem rotLstar 1 ≤ ENNReal.ofReal (1 / 2) ∧
    Tendsto (fun ε : ℝ => rotWeight (Real.sqrt ε) ε) (𝓝[>] 0) (𝓝 rotLstar) ∧
    ¬ Tendsto (fun ε : ℝ => Limit.minimumValue rotProblem (rotWeight (Real.sqrt ε) ε) 1)
      (𝓝[>] 0) (𝓝 (Limit.minimumValue rotProblem rotLstar 1)) := by
  have hval : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 25 →
      Limit.minimumValue rotProblem (rotWeight (Real.sqrt ε) ε) 1 = ENNReal.ofReal 4 :=
    fun ε h0 h1 => rot_value_eq (Real.sqrt ε) ε h0 (pi_mul_le_sin_sqrt ε h0 h1)
  refine ⟨hval, rot_target_le, rotWeight_sqrt_tendsto, fun hlim => ?_⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Limit.minimumValue rotProblem (rotWeight (Real.sqrt ε) ε) 1 = ENNReal.ofReal 4 := by
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 25 by norm_num)] with ε hε hpos
    exact hval ε hpos (le_of_lt hε)
  have h4 : Tendsto (fun ε : ℝ => Limit.minimumValue rotProblem (rotWeight (Real.sqrt ε) ε) 1)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal 4)) :=
    tendsto_const_nhds.congr' (hev.mono fun ε h => h.symm)
  have heq : ENNReal.ofReal 4 = Limit.minimumValue rotProblem rotLstar 1 :=
    tendsto_nhds_unique h4 hlim
  have hlt : ENNReal.ofReal (1 / 2) < ENNReal.ofReal 4 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
  rw [heq] at hlt
  exact absurd rot_target_le (not_le.mpr hlt)

/-- Sequence form: `ε_j → 0`, `θ_j = √ε_j`. -/
theorem rotating_transport_sequence (ε : ℕ → ℝ) (hε0 : ∀ j, 0 < ε j)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => rotWeight (Real.sqrt (ε j)) (ε j)) atTop (𝓝 rotLstar) ∧
    (∀ᶠ j in atTop,
      Limit.minimumValue rotProblem (rotWeight (Real.sqrt (ε j)) (ε j)) 1 = ENNReal.ofReal 4) ∧
    Limit.minimumValue rotProblem rotLstar 1 ≤ ENNReal.ofReal (1 / 2) := by
  have hnhds : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Filter.Eventually.of_forall hε0⟩
  refine ⟨rotWeight_sqrt_tendsto.comp hnhds, ?_, rot_target_le⟩
  have hsmall : ∀ᶠ j in atTop, ε j < 1 / 25 :=
    hε.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 25 by norm_num))
  filter_upwards [hsmall] with j hj
  exact rot_value_eq (Real.sqrt (ε j)) (ε j) (hε0 j) (pi_mul_le_sin_sqrt (ε j) (hε0 j) hj.le)

#print axioms rot_lower_exact
#print axioms rot_upper
#print axioms rot_value_eq
#print axioms rot_target_le
#print axioms rotating_transport_jump
#print axioms rotating_transport_sequence

end LiZouTransport.Examples

end
