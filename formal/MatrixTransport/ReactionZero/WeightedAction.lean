import MatrixTransport.SupportFunction
import MatrixTransport.MeasureRepresentation

/-!
# General weighted matrix support action

The dimensions `n` and `k` are arbitrary. This module defines the actual weighted matrix dual
admissible set, its extended-valued support cost, and its integral against the common RN reference of an
arbitrary finite family of signed measures. It proves reaction-weight comparison and equality
when the primal reaction vanishes. There is no density invertibility hypothesis.

The mass ambient space has all `n²` real coordinates. The original paper restricts its mass
measure to symmetric positive semidefinite matrices; a final continuity-equation theorem must
impose that restriction explicitly. The symmetric dual mass alone does not rule out an
antisymmetric primal mass component. The quadratic dual admissible set is not asserted to be
a cone.

These are action lemmas for the reaction-weight-zero limit. This module does not define the
continuity equation, prove weak-star compactness, or assert convergence of minimum values.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.ReactionZero

noncomputable section

abbrev Coord (n k : ℕ) := (Fin n × Fin n) ⊕ ((Fin n × Fin k) ⊕ (Fin n × Fin n))

variable {n k : ℕ}

def mass (a : Coord n k → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ a (Sum.inl (i, j))

def flux (a : Coord n k → ℝ) : Matrix (Fin n) (Fin k) ℝ :=
  fun i j ↦ a (Sum.inr (Sum.inl (i, j)))

def reaction (a : Coord n k → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ a (Sum.inr (Sum.inr (i, j)))

def pack (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Coord n k → ℝ
  | Sum.inl p => A p.1 p.2
  | Sum.inr (Sum.inl p) => B p.1 p.2
  | Sum.inr (Sum.inr p) => C p.1 p.2

def gram {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  X * X.transpose

/-- For the real symmetric weights used in the paper, the Gram term is exactly
`B Λ² Bᵀ`, including singular weights. -/
theorem gram_mul_of_isHermitian {m p : ℕ} (B : Matrix (Fin m) (Fin p) ℝ)
    (L : Matrix (Fin p) (Fin p) ℝ) (hL : L.IsHermitian) :
    gram (B * L) = B * L ^ 2 * B.transpose := by
  have hT : L.transpose = L := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hL.eq
  simp only [gram, Matrix.transpose_mul, hT, pow_two, Matrix.mul_assoc]

/-- Full real Frobenius pairing, in arbitrary finite matrix dimensions. -/
def frob {m p : ℕ} (X Y : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

def dualSet (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ) :
    Set (Coord n k → ℝ) :=
  {a | (mass a).IsHermitian ∧
    (-mass a - (1 / 2 : ℝ) • gram (flux a * L1) - (1 / 2 : ℝ) • gram (reaction a * L2)).PosSemidef}

def cost (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (v : Coord n k → ℝ) : ℝ≥0∞ :=
  supportFunction (fun _ ↦ 1) (dualSet L1 L2) v

@[simp] theorem mass_pack (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : mass (pack A B C) = A := rfl

@[simp] theorem flux_pack (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : flux (pack A B C) = B := rfl

@[simp] theorem reaction_pack (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : reaction (pack A B C) = C := rfl

theorem pack_unpack (a : Coord n k → ℝ) : pack (mass a) (flux a) (reaction a) = a := by
  funext c
  rcases c with p | p | p <;> rfl

theorem weightedPair_expand (a v : Coord n k → ℝ) :
    weightedPair (fun _ ↦ 1) a v =
      (∑ i, ∑ j, mass a i j * mass v i j) + (∑ i, ∑ j, flux a i j * flux v i j)
        + ∑ i, ∑ j, reaction a i j * reaction v i j := by
  simp [weightedPair, Fintype.sum_sum_type, Fintype.sum_prod_type, mass, flux, reaction,
    add_assoc]

theorem weightedPair_pack (a : Coord n k → ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (Y : Matrix (Fin n) (Fin k) ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) :
    weightedPair (fun _ ↦ 1) a (pack X Y Z) =
      frob (mass a) X + frob (flux a) Y + frob (reaction a) Z := by
  rw [weightedPair_expand]
  simp [frob]

theorem cost_zero (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ) :
    cost L1 L2 (0 : Coord n k → ℝ) = 0 :=
  supportFunction_zero _ _

theorem cost_smul_nonneg (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (v : Coord n k → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cost L1 L2 (t • v) = ENNReal.ofReal t * cost L1 L2 v :=
  supportFunction_smul_nonneg _ _ v ht

theorem lowerSemicontinuous_cost (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) : LowerSemicontinuous (cost L1 L2) :=
  lowerSemicontinuous_supportFunction _ _

theorem measurable_cost (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (cost L1 L2) :=
  measurable_supportFunction _ _

theorem cost_fenchel (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (v a : Coord n k → ℝ) (ha : a ∈ dualSet L1 L2) :
    ENNReal.ofReal (weightedPair (fun _ ↦ 1) a v) ≤ cost L1 L2 v :=
  supportFunction_fenchel _ _ v a ha

/-! ### Reaction weight monotonicity -/

theorem posSemidef_gram {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℝ) : (gram X).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose X
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

theorem gram_mul_sub {m p : ℕ} (C : Matrix (Fin m) (Fin p) ℝ)
    (Lb L : Matrix (Fin p) (Fin p) ℝ) :
    gram (C * Lb) - gram (C * L) = C * (Lb * Lb.transpose - L * L.transpose) * C.transpose := by
  simp only [gram, Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

theorem posSemidef_gram_sub {m p : ℕ} (C : Matrix (Fin m) (Fin p) ℝ)
    {Lb L : Matrix (Fin p) (Fin p) ℝ}
    (h : (Lb * Lb.transpose - L * L.transpose).PosSemidef) :
    (gram (C * Lb) - gram (C * L)).PosSemidef := by
  rw [gram_mul_sub]
  have h2 := h.mul_mul_conjTranspose_same C
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  exact h2

theorem dualSet_mono_reaction (L1 : Matrix (Fin k) (Fin k) ℝ)
    {L Lb : Matrix (Fin n) (Fin n) ℝ}
    (h : (Lb * Lb.transpose - L * L.transpose).PosSemidef) :
    dualSet (n := n) L1 Lb ⊆ dualSet L1 L := by
  intro a ha
  obtain ⟨hH, hP⟩ := ha
  refine ⟨hH, ?_⟩
  have hd := (posSemidef_gram_sub (reaction a) h).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have heq : -mass a - (1 / 2 : ℝ) • gram (flux a * L1) - (1 / 2 : ℝ) • gram (reaction a * L)
      = (-mass a - (1 / 2 : ℝ) • gram (flux a * L1) - (1 / 2 : ℝ) • gram (reaction a * Lb))
        + (1 / 2 : ℝ) • (gram (reaction a * Lb) - gram (reaction a * L)) := by
    module
  rw [heq]
  exact hP.add hd

theorem supportFunction_mono_set {ι : Type*} [Fintype ι] (coeff : ι → ℝ)
    {S T : Set (ι → ℝ)} (h : S ⊆ T) (v : ι → ℝ) :
    supportFunction coeff S v ≤ supportFunction coeff T v :=
  iSup₂_le fun a ha ↦ supportFunction_fenchel coeff T v a (h ha)

theorem cost_mono_reaction (L1 : Matrix (Fin k) (Fin k) ℝ)
    {L Lb : Matrix (Fin n) (Fin n) ℝ}
    (h : (Lb * Lb.transpose - L * L.transpose).PosSemidef) (v : Coord n k → ℝ) :
    cost L1 Lb v ≤ cost L1 L v :=
  supportFunction_mono_set _ (dualSet_mono_reaction L1 h) v

/-! ### Projecting the dual reaction away -/

theorem pack_mem_dualSet_of_mem (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L K : Matrix (Fin n) (Fin n) ℝ) {a : Coord n k → ℝ} (ha : a ∈ dualSet L1 L) :
    pack (mass a) (flux a) 0 ∈ dualSet L1 K := by
  obtain ⟨hH, hP⟩ := ha
  refine ⟨?_, ?_⟩
  · rw [mass_pack]
    exact hH
  · rw [mass_pack, flux_pack, reaction_pack]
    have hg : gram ((0 : Matrix (Fin n) (Fin n) ℝ) * K) = 0 := by simp [gram]
    have hd := (posSemidef_gram (reaction a * L)).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    have heq : -mass a - (1 / 2 : ℝ) • gram (flux a * L1) -
          (1 / 2 : ℝ) • gram ((0 : Matrix (Fin n) (Fin n) ℝ) * K)
        = (-mass a - (1 / 2 : ℝ) • gram (flux a * L1) - (1 / 2 : ℝ) • gram (reaction a * L))
          + (1 / 2 : ℝ) • gram (reaction a * L) := by
      rw [hg]
      module
    rw [heq]
    exact hP.add hd

theorem weightedPair_project (a v : Coord n k → ℝ) (hv : reaction v = 0) :
    weightedPair (fun _ ↦ 1) (pack (mass a) (flux a) 0) v =
      weightedPair (fun _ ↦ 1) a v := by
  rw [weightedPair_expand, weightedPair_expand, hv]
  simp [mass_pack, flux_pack, reaction_pack]

theorem cost_le_of_reaction_zero (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L K : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hv : reaction v = 0) :
    cost L1 L v ≤ cost L1 K v := by
  unfold cost supportFunction
  refine iSup₂_le fun a ha ↦ ?_
  calc ENNReal.ofReal (weightedPair (fun _ ↦ 1) a v)
      = ENNReal.ofReal (weightedPair (fun _ ↦ 1) (pack (mass a) (flux a) 0) v) := by
        rw [weightedPair_project a v hv]
    _ ≤ supportFunction (fun _ ↦ 1) (dualSet L1 K) v :=
        supportFunction_fenchel _ _ v _ (pack_mem_dualSet_of_mem L1 L K ha)

theorem cost_eq_of_reaction_zero (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L K : Matrix (Fin n) (Fin n) ℝ) (v : Coord n k → ℝ) (hv : reaction v = 0) :
    cost L1 L v = cost L1 K v :=
  le_antisymm (cost_le_of_reaction_zero L1 L K v hv) (cost_le_of_reaction_zero L1 K L v hv)

theorem cost_pack_zero_eq (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L K : Matrix (Fin n) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (Y : Matrix (Fin n) (Fin k) ℝ) :
    cost L1 L (pack X Y 0) = cost L1 K (pack X Y 0) :=
  cost_eq_of_reaction_zero L1 L K _ (reaction_pack X Y 0)

/-! ### Integrated action -/

section Integrated

variable {α : Type*} [MeasurableSpace α]

def density (μ : Coord n k → SignedMeasure α) (x : α) : Coord n k → ℝ :=
  fun c ↦ (μ c).rnDeriv (jointReference μ) x

def action (L1 : Matrix (Fin k) (Fin k) ℝ) (L2 : Matrix (Fin n) (Fin n) ℝ)
    (μ : Coord n k → SignedMeasure α) : ℝ≥0∞ :=
  ∫⁻ x, cost L1 L2 (density μ x) ∂(jointReference μ)

theorem measurable_density (μ : Coord n k → SignedMeasure α) : Measurable (density μ) :=
  measurable_pi_iff.mpr fun c ↦ measurable_rnDeriv_jointReference μ c

theorem measurable_cost_density (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure α) :
    Measurable fun x ↦ cost L1 L2 (density μ x) :=
  (measurable_cost L1 L2).comp (measurable_density μ)

theorem action_mono_reaction (L1 : Matrix (Fin k) (Fin k) ℝ)
    {L Lb : Matrix (Fin n) (Fin n) ℝ}
    (h : (Lb * Lb.transpose - L * L.transpose).PosSemidef)
    (μ : Coord n k → SignedMeasure α) :
    action L1 Lb μ ≤ action L1 L μ :=
  lintegral_mono fun x ↦ cost_mono_reaction L1 h (density μ x)

theorem action_eq_of_ae_reaction_zero (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L K : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure α)
    (h : ∀ᵐ x ∂(jointReference μ), reaction (density μ x) = 0) :
    action L1 L μ = action L1 K μ :=
  lintegral_congr_ae (h.mono fun _x hx ↦ cost_eq_of_reaction_zero L1 L K _ hx)

theorem rnDeriv_ae_zero_of_eq_zero (μ : Coord n k → SignedMeasure α) (c : Coord n k)
    (h : μ c = 0) : (μ c).rnDeriv (jointReference μ) =ᵐ[jointReference μ] 0 := by
  refine (integrable_rnDeriv_jointReference μ c).ae_eq_zero_of_forall_setIntegral_eq_zero
    fun s hs _ ↦ ?_
  rw [← withDensityᵥ_apply (integrable_rnDeriv_jointReference μ c) hs,
    withDensityᵥ_rnDeriv_jointReference μ c, h]
  simp

/-- The signed RN derivative of a zero coordinate is pointwise zero: the two Jordan
parts give identical derivatives, which cancel. -/
theorem rnDeriv_zero_of_eq_zero (μ : Coord n k → SignedMeasure α) (c : Coord n k)
    (h : μ c = 0) (x : α) : (μ c).rnDeriv (jointReference μ) x = 0 := by
  rw [h]
  simp [SignedMeasure.rnDeriv_def, SignedMeasure.toJordanDecomposition_zero]

theorem reaction_density_zero (μ : Coord n k → SignedMeasure α)
    (h : ∀ i j, μ (Sum.inr (Sum.inr (i, j))) = 0) (x : α) :
    reaction (density μ x) = 0 := by
  ext i j
  exact rnDeriv_zero_of_eq_zero μ _ (h i j) x

theorem ae_reaction_density_zero (μ : Coord n k → SignedMeasure α)
    (h : ∀ i j, μ (Sum.inr (Sum.inr (i, j))) = 0) :
    ∀ᵐ x ∂(jointReference μ), reaction (density μ x) = 0 := by
  have h2 : ∀ i j, ∀ᵐ x ∂(jointReference μ),
      (μ (Sum.inr (Sum.inr (i, j)))).rnDeriv (jointReference μ) x = 0 :=
    fun i j ↦ rnDeriv_ae_zero_of_eq_zero μ _ (h i j)
  have h3 := ae_all_iff.2 fun i ↦ ae_all_iff.2 (h2 i)
  filter_upwards [h3] with x hx
  ext i j
  exact hx i j

theorem action_eq_of_reaction_measures_zero (L1 : Matrix (Fin k) (Fin k) ℝ)
    (L K : Matrix (Fin n) (Fin n) ℝ) (μ : Coord n k → SignedMeasure α)
    (h : ∀ i j, μ (Sum.inr (Sum.inr (i, j))) = 0) :
    action L1 L μ = action L1 K μ :=
  action_eq_of_ae_reaction_zero L1 L K μ (ae_reaction_density_zero μ h)

#print axioms cost_mono_reaction
#print axioms cost_eq_of_reaction_zero
#print axioms action_mono_reaction
#print axioms action_eq_of_reaction_measures_zero

end Integrated

end

end MatrixTransport.ReactionZero
