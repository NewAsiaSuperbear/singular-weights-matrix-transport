import MatrixTransport.Examples.AtomPaths

/-!
# Affine scalar tests on closed domains

`affF c₀ c₁ c₂ c₃ (s, x) = c₀ + c₁ s + c₂ x₀ + c₃ x₁` has explicit coordinate
partial derivatives and defines a native `ClosedC1Jet Ω 1`. The norm-divergence
example uses `y/4 - s/8`; the Kantorovich–Bures certificate uses the corresponding
entrywise affine tests.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace LiZouTransport.Examples

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain

/-- `c₀ + c₁ s + c₂ x₀ + c₃ x₁` on the ambient space `ℝ × ℝ²`. -/
def affF (c₀ c₁ c₂ c₃ : ℝ) (p : Ambient 2) : ℝ := c₀ + c₁ * p.1 + c₂ * p.2 0 + c₃ * p.2 1

/-- Its spatial gradient along the direction `eⱼ`. -/
def affFx (c₂ c₃ : ℝ) (j : Fin 2) : ℝ :=
  c₂ * (EuclideanSpace.single j (1 : ℝ) : Space 2) 0 +
    c₃ * (EuclideanSpace.single j (1 : ℝ) : Space 2) 1

@[simp] theorem affFx_zero (c₂ c₃ : ℝ) : affFx c₂ c₃ 0 = c₂ := by
  simp [affFx, EuclideanSpace.single_apply]

@[simp] theorem affFx_one (c₂ c₃ : ℝ) : affFx c₂ c₃ 1 = c₃ := by
  simp [affFx, EuclideanSpace.single_apply]

theorem continuous_affF (c₀ c₁ c₂ c₃ : ℝ) : Continuous (affF c₀ c₁ c₂ c₃) := by
  unfold affF
  have h0 : Continuous fun p : Ambient 2 => p.2 0 := (continuous_coord 0).comp continuous_snd
  have h1 : Continuous fun p : Ambient 2 => p.2 1 := (continuous_coord 1).comp continuous_snd
  exact (((continuous_const.add (continuous_const.mul continuous_fst)).add
    (continuous_const.mul h0)).add (continuous_const.mul h1))

theorem hasDerivAt_affF_time (c₀ c₁ c₂ c₃ : ℝ) (p : Ambient 2) :
    HasDerivAt (fun s => affF c₀ c₁ c₂ c₃ (timeLine p s)) c₁ 0 := by
  have h1 := ((((hasDerivAt_const (0 : ℝ) c₀).add
    (((hasDerivAt_id' (0 : ℝ)).const_add p.1).const_mul c₁)).add
    (hasDerivAt_const (0 : ℝ) (c₂ * p.2 0))).add (hasDerivAt_const (0 : ℝ) (c₃ * p.2 1)))
  exact h1.congr_deriv (by ring)

theorem hasDerivAt_affF_space (c₀ c₁ c₂ c₃ : ℝ) (p : Ambient 2) (j : Fin 2) :
    HasDerivAt (fun s => affF c₀ c₁ c₂ c₃ (spaceLine p j s)) (affFx c₂ c₃ j) 0 := by
  have h1 := (((hasDerivAt_const (0 : ℝ) (c₀ + c₁ * p.1)).add
    ((((hasDerivAt_id' (0 : ℝ)).mul_const
      ((EuclideanSpace.single j (1 : ℝ) : Space 2) 0)).const_add (p.2 0)).const_mul c₂)).add
    ((((hasDerivAt_id' (0 : ℝ)).mul_const
      ((EuclideanSpace.single j (1 : ℝ) : Space 2) 1)).const_add (p.2 1)).const_mul c₃))
  have hf : (fun s => affF c₀ c₁ c₂ c₃ (spaceLine p j s)) =
      fun s : ℝ => c₀ + c₁ * p.1 +
        c₂ * (p.2 0 + s * (EuclideanSpace.single j (1 : ℝ) : Space 2) 0) +
        c₃ * (p.2 1 + s * (EuclideanSpace.single j (1 : ℝ) : Space 2) 1) := by
    funext s
    simp [affF, spaceLine] <;> ring
  rw [hf]
  exact h1.congr_deriv (by unfold affFx; ring)

/-- The affine scalar test as a genuine closed-`C¹` jet (value `F`, `∂ₜ = c₁`, `∂ⱼ = affFx`). -/
def affineJet (Ω : Set (Space 2)) (c₀ c₁ c₂ c₃ : ℝ) : ClosedC1Jet Ω 1 :=
  scalarJet (Ω := Ω) (affF c₀ c₁ c₂ c₃) (fun _ => c₁) (fun j _ => affFx c₂ c₃ j)
    (continuous_affF c₀ c₁ c₂ c₃).continuousOn continuousOn_const (fun _ => continuousOn_const)
    (fun p _ => hasDerivAt_affF_time c₀ c₁ c₂ c₃ p.val)
    (fun p j _ => hasDerivAt_affF_space c₀ c₁ c₂ c₃ p.val j)

theorem affineJet_value (Ω : Set (Space 2)) (c₀ c₁ c₂ c₃ : ℝ) (q : Q Ω) :
    (affineJet Ω c₀ c₁ c₂ c₃).value q 0 0 = affF c₀ c₁ c₂ c₃ q.val :=
  scalarJet_value_apply _ _ _ _ _ _ _ _ q

theorem affineJet_dt (Ω : Set (Space 2)) (c₀ c₁ c₂ c₃ : ℝ) (q : Q Ω) :
    (affineJet Ω c₀ c₁ c₂ c₃).dt q 0 0 = c₁ :=
  scalarJet_dt_apply _ _ _ _ _ _ _ _ q

theorem affineJet_dx (Ω : Set (Space 2)) (c₀ c₁ c₂ c₃ : ℝ) (j : Fin 2) (q : Q Ω) :
    (affineJet Ω c₀ c₁ c₂ c₃).dx j q 0 0 = affFx c₂ c₃ j :=
  scalarJet_dx_apply _ _ _ _ _ _ _ _ j q

/-- Coordinates of points on an axis curve with base point `pt2 x y`. -/
theorem axisPt_snd_zero (x y : ℝ) (j : Fin 2) (t u : ℝ) :
    (axisPt (pt2 x y) j t u).2 0 = x + u * (if (0 : Fin 2) = j then 1 else 0) := by
  simp [axisPt, EuclideanSpace.single_apply]

theorem axisPt_snd_one (x y : ℝ) (j : Fin 2) (t u : ℝ) :
    (axisPt (pt2 x y) j t u).2 1 = y + u * (if (1 : Fin 2) = j then 1 else 0) := by
  simp [axisPt, EuclideanSpace.single_apply]

/-- The all-competitor lower certificate for an affine scalar test on `Ω ⊂ ℝ²`. -/
theorem affine_lower_bound (Ω : Set (Space 2)) [Fact (IsCompact Ω)] (a₀ b₀ : ↥Ω)
    (L : Matrix (Fin 2) (Fin 2) ℝ) (c₀ c₁ c₂ c₃ : ℝ)
    (hHJ : ∀ q : Q Ω, c₁ + (1 / 2 : ℝ) * ∑ l, (∑ l', affFx c₂ c₃ l' * L l' l) ^ 2 +
      (1 / 2 : ℝ) * (affF c₀ c₁ c₂ c₃ q.val) ^ 2 ≤ 0) :
    ENNReal.ofReal (affF c₀ c₁ c₂ c₃ (1, b₀.val) - affF c₀ c₁ c₂ c₃ (0, a₀.val)) ≤
      Limit.minimumValue (diracGradProblem a₀ b₀) L 1 :=
  diracGradProblem_lower_bound a₀ b₀ L (affF c₀ c₁ c₂ c₃) (fun _ => c₁)
    (fun j _ => affFx c₂ c₃ j)
    (continuous_affF c₀ c₁ c₂ c₃).continuousOn continuousOn_const (fun _ => continuousOn_const)
    (fun p _ => hasDerivAt_affF_time c₀ c₁ c₂ c₃ p.val)
    (fun p j _ => hasDerivAt_affF_space c₀ c₁ c₂ c₃ p.val j) hHJ

end LiZouTransport.Examples

end
