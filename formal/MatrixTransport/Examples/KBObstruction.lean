import MatrixTransport.Examples.NormDivergence

/-!
# Operator dependence under isotropically diverging transport weights

The Kantorovich–Bures row-divergence operator on the closed unit disk has
`n = d = 2`, `k = 1`, reaction weight `I₂`, and endpoints
`I₂ δ_(0,-1)` and `I₂ δ_(0,1)` with equal total matrices.

For every transport weight and every original competitor, the test
`Φ = diag(y/4 - s/8, -s/8)` has vanishing row divergence and gives `V ≥ 1/4`.
The Hamilton–Jacobi slack is bounded below by `diag(7/128,15/128)` on the
closed domain. The result is this all-competitor lower bound.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace LiZouTransport.Examples

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain

/-! ### Diagonal `2 × 2` matrices -/

def diagM (a b : ℝ) : Mat 2 := !![a, 0; 0, b]
def e00 : Mat 2 := !![1, 0; 0, 0]
def e11 : Mat 2 := !![0, 0; 0, 1]

theorem diagM_eq (a b : ℝ) : diagM a b = a • e00 + b • e11 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagM, e00, e11]

theorem isHermitian_diagM (a b : ℝ) : (diagM a b).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagM]

theorem continuous_diagM : Continuous (fun p : ℝ × ℝ => diagM p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => diagM p.1 p.2) = fun p => p.1 • e00 + p.2 • e11 :=
    funext fun p => diagM_eq _ _
  rw [h]
  exact (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

theorem hasDerivAt_diagM {f g : ℝ → ℝ} {f' g' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) : HasDerivAt (fun s => diagM (f s) (g s)) (diagM f' g') x := by
  have h := (hf.smul_const e00).add (hg.smul_const e11)
  have h2 : HasDerivAt (fun s => diagM (f s) (g s)) (f' • e00 + g' • e11) x :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => diagM_eq (f s) (g s))
  rw [diagM_eq f' g']
  exact h2

/-- Membership in the dual set with `H = I₂` for a diagonal slack. -/
theorem mem_dualSet_of_diag {k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ) (a : Coord 2 k → ℝ)
    (s0 s1 : ℝ) (hm : (mass a).IsHermitian)
    (hs : -mass a - (1 / 2 : ℝ) • gram (flux a * L) -
      (1 / 2 : ℝ) • gram (reaction a * (1 : Mat 2)) = diagM s0 s1)
    (h0 : 0 ≤ s0) (h1 : 0 ≤ s1) : a ∈ dualSet L (1 : Mat 2) := by
  refine ⟨hm, ?_⟩
  rw [hs]
  have hd : diagM s0 s1 = Matrix.diagonal (fun i : Fin 2 => if i = 0 then s0 else s1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagM, Matrix.diagonal_apply]
  rw [hd]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp [h0, h1]

/-! ### The Kantorovich–Bures operator and problem -/

/-- Column `j` of a `2 × 2` matrix as a `2 × 1` matrix. -/
def kbColLinear (j : Fin 2) : Mat 2 →ₗ[ℝ] Matrix (Fin 2) (Fin 1) ℝ where
  toFun M := Matrix.of fun i (_ : Fin 1) => M i j
  map_add' := by
    intro M N
    ext i l
    simp
  map_smul' := by
    intro c M
    ext i l
    simp

/-- The original operator `D*Φ = div Φ` (row divergence), `D0 = 0`, so `D* I = 0`. -/
def kbOp : AdjointOperator 2 2 1 where
  D0 := 0
  Dj j := (kbColLinear j).toContinuousLinearMap
  D0_one := by simp

theorem kbOp_apply {Ω : Set (Space 2)} (φ : ClosedC1Jet Ω 2) (p : Q Ω) (i : Fin 2)
    (l : Fin 1) : kbOp.apply φ p i l = ∑ j, φ.dx j p i j := by
  first
    | simp [AdjointOperator.apply, kbOp, kbColLinear, Matrix.sum_apply]
    | simp [AdjointOperator.apply, kbOp, kbColLinear, Finset.sum_apply]

/-- `I₂ δₓ` as the endpoint measure family (diagonal entries `δₓ`, off-diagonal `0`). -/
def kbEndpoint {Ω : Set (Space 2)} (x : ↥Ω) : Fin 2 × Fin 2 → SignedMeasure ↥Ω :=
  fun ij => if ij.1 = ij.2 then diracAt x 1 else 0

theorem kbEndpoint_posSemidef {Ω : Set (Space 2)} (x : ↥Ω) :
    EndpointPositiveSemidefinite (kbEndpoint x) := by
  intro s hs
  have hd : (fun i j : Fin 2 => kbEndpoint x (i, j) s) =
      Matrix.diagonal (fun _ : Fin 2 => diracAt x 1 s) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [kbEndpoint]
    · simp [kbEndpoint, h, Matrix.diagonal_apply_ne _ h]
  rw [hd]
  exact Matrix.posSemidef_diagonal_iff.mpr fun _ => diracAt_nonneg x zero_le_one s hs

/-- The Kantorovich–Bures problem `I₂ δ_{(0,-1)} → I₂ δ_{(0,1)}` on the closed unit disk. -/
def kbProblem : Limit.Problem disk2 2 1 :=
  ⟨kbOp, kbEndpoint diskA, kbEndpoint diskB, kbEndpoint_posSemidef _, kbEndpoint_posSemidef _⟩

theorem diracAt_univ {Ω : Set (Space 2)} (x : ↥Ω) : diracAt x 1 Set.univ = 1 := by
  have h := signedPair_diracAt x 1 (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
  rw [signedPair_one_eq_univ] at h
  simpa using h

/-- Both endpoint total matrices are the identity `I₂`. -/
theorem kbEndpoint_total {Ω : Set (Space 2)} (x : ↥Ω) :
    (fun i j : Fin 2 => kbEndpoint x (i, j) Set.univ) = (1 : Mat 2) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [kbEndpoint, diracAt_univ]
  · simp [kbEndpoint, h, Matrix.one_apply_ne h]

theorem kb_equal_total_matrices :
    (fun i j : Fin 2 => kbProblem.initial (i, j) Set.univ) =
      (fun i j : Fin 2 => kbProblem.terminal (i, j) Set.univ) := by
  show (fun i j : Fin 2 => kbEndpoint diskA (i, j) Set.univ) =
    (fun i j : Fin 2 => kbEndpoint diskB (i, j) Set.univ)
  rw [kbEndpoint_total, kbEndpoint_total]

/-! ### The diagonal affine jet -/

/-- `diag(affF a, affF b)` as a genuine closed-`C¹` jet in dimension `n = 2`. -/
def affDiagJet (Ω : Set (Space 2)) (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ) : ClosedC1Jet Ω 2 := by
  have hv : Continuous fun q : Q Ω =>
      diagM (affF a₀ a₁ a₂ a₃ q.val) (affF b₀ b₁ b₂ b₃ q.val) :=
    continuous_diagM.comp (((continuous_affF a₀ a₁ a₂ a₃).comp continuous_subtype_val).prodMk
      ((continuous_affF b₀ b₁ b₂ b₃).comp continuous_subtype_val))
  refine ClosedC1Jet.ofAmbient (fun p => diagM (affF a₀ a₁ a₂ a₃ p) (affF b₀ b₁ b₂ b₃ p))
    ⟨fun q => diagM (affF a₀ a₁ a₂ a₃ q.val) (affF b₀ b₁ b₂ b₃ q.val), hv⟩
    ⟨fun _ => diagM a₁ b₁, continuous_const⟩
    (fun j => ⟨fun _ => diagM (affFx a₂ a₃ j) (affFx b₂ b₃ j), continuous_const⟩)
    (fun _ => rfl) ?_ ?_ ?_ ?_ ?_
  · intro p
    exact isHermitian_diagM _ _
  · intro p
    exact isHermitian_diagM _ _
  · intro j p
    exact isHermitian_diagM _ _
  · intro p hp
    exact hasDerivAt_diagM (hasDerivAt_affF_time a₀ a₁ a₂ a₃ p.val)
      (hasDerivAt_affF_time b₀ b₁ b₂ b₃ p.val)
  · intro p j hp
    exact hasDerivAt_diagM (hasDerivAt_affF_space a₀ a₁ a₂ a₃ p.val j)
      (hasDerivAt_affF_space b₀ b₁ b₂ b₃ p.val j)

theorem affDiagJet_value (Ω : Set (Space 2)) (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ) (q : Q Ω) :
    (affDiagJet Ω a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃).value q =
      diagM (affF a₀ a₁ a₂ a₃ q.val) (affF b₀ b₁ b₂ b₃ q.val) := rfl

theorem affDiagJet_dt (Ω : Set (Space 2)) (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ) (q : Q Ω) :
    (affDiagJet Ω a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃).dt q = diagM a₁ b₁ := rfl

theorem affDiagJet_dx (Ω : Set (Space 2)) (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ) (j : Fin 2) (q : Q Ω) :
    (affDiagJet Ω a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃).dx j q = diagM (affFx a₂ a₃ j) (affFx b₂ b₃ j) := rfl

/-- The Kantorovich–Bures test `Φ = diag(y/4 - s/8, -s/8)`. -/
def kbJet : ClosedC1Jet disk2 2 := affDiagJet disk2 0 (-1 / 8) 0 (1 / 4) 0 (-1 / 8) 0 0

theorem kbJet_mass (q : Q disk2) :
    mass (testField kbOp kbJet q) = diagM (-1 / 8) (-1 / 8) := rfl

theorem kbJet_reaction (q : Q disk2) :
    reaction (testField kbOp kbJet q) =
      diagM (affF 0 (-1 / 8) 0 (1 / 4) q.val) (affF 0 (-1 / 8) 0 0 q.val) := rfl

/-- The flux test field `D*Φ` vanishes identically. -/
theorem kbJet_flux_zero (q : Q disk2) : flux (testField kbOp kbJet q) = 0 := by
  ext i l
  show kbOp.apply kbJet q i l = 0
  rw [kbOp_apply]
  simp only [Fin.sum_univ_two, kbJet, affDiagJet_dx]
  fin_cases i <;> simp [diagM]

theorem kb_F0_sq_le (s y : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy0 : -1 ≤ y) (hy1 : y ≤ 1) :
    (-(1 / 8) * s + (1 / 4) * y) ^ 2 ≤ 9 / 64 := by
  have h1 : 0 ≤ 3 / 8 - (-(1 / 8) * s + (1 / 4) * y) := by linarith
  have h2 : 0 ≤ (-(1 / 8) * s + (1 / 4) * y) + 3 / 8 := by linarith
  nlinarith [mul_nonneg h1 h2]

theorem kb_F1_sq_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (-(1 / 8) * s) ^ 2 ≤ 1 / 64 := by
  nlinarith [mul_nonneg hs0 (sub_nonneg.2 hs1)]

/-- The test field lies pointwise in the actual dual set, for **every** transport weight `L`. -/
theorem kb_testField_mem (L : Matrix (Fin 1) (Fin 1) ℝ) (q : Q disk2) :
    testField kbOp kbJet q ∈ dualSet L (1 : Mat 2) := by
  have hs := q.property.1
  have hy := (mem_disk2_iff _).1 q.property.2
  have hs0 : 0 ≤ q.val.1 := hs.1
  have hs1 : q.val.1 ≤ 1 := hs.2
  have hy1 : q.val.2 1 ≤ 1 := by nlinarith [sq_nonneg (q.val.2 0)]
  have hy0 : -1 ≤ q.val.2 1 := by nlinarith [sq_nonneg (q.val.2 0)]
  have hF0 := kb_F0_sq_le q.val.1 (q.val.2 1) hs0 hs1 hy0 hy1
  have hF1 := kb_F1_sq_le q.val.1 hs0 hs1
  refine mem_dualSet_of_diag L (testField kbOp kbJet q)
    (1 / 8 - (1 / 2) * (affF 0 (-1 / 8) 0 (1 / 4) q.val) ^ 2)
    (1 / 8 - (1 / 2) * (affF 0 (-1 / 8) 0 0 q.val) ^ 2) ?_ ?_ ?_ ?_
  · rw [kbJet_mass]
    exact isHermitian_diagM _ _
  · rw [kbJet_mass, kbJet_flux_zero, kbJet_reaction, Matrix.mul_one, Matrix.zero_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagM, gram, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two] <;> ring
  · simp only [affF]
    nlinarith [hF0]
  · simp only [affF]
    nlinarith [hF1]

/-! ### Endpoint evaluation and the lower bound -/

theorem signedPair_zeroMeasure {α : Type*} [MeasurableSpace α] (f : α → ℝ) :
    MatrixTransport.signedPair (0 : SignedMeasure α) f = 0 := by
  have h0p : (0 : SignedMeasure α).toJordanDecomposition.posPart = 0 := by
    rw [SignedMeasure.toJordanDecomposition_zero]
    rfl
  have h0n : (0 : SignedMeasure α).toJordanDecomposition.negPart = 0 := by
    rw [SignedMeasure.toJordanDecomposition_zero]
    rfl
  unfold MatrixTransport.signedPair
  rw [h0p, h0n]
  simp

theorem timeBoundary_val {Ω : Set (Space 2)} (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : ↥Ω) :
    (timeBoundary t ht x).val = (t, x.val) := rfl

theorem endpointPair_kbEndpoint {Ω : Set (Space 2)} [Fact (IsCompact Ω)] (x : ↥Ω)
    (φ : ClosedC1Jet Ω 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    endpointPair (kbEndpoint x) φ t ht =
      φ.value (timeBoundary t ht x) 0 0 + φ.value (timeBoundary t ht x) 1 1 := by
  haveI : CompactSpace ↥Ω := isCompact_iff_compactSpace.mp (Fact.out : IsCompact Ω)
  have hc : ∀ i j : Fin 2, Continuous fun y : ↥Ω => φ.value (timeBoundary t ht y) i j :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp
      (φ.value.continuous.comp (timeBoundary t ht).continuous))
  have hb : ∀ i j : Fin 2, ∃ C : ℝ, ∀ y : ↥Ω, |φ.value (timeBoundary t ht y) i j| ≤ C :=
    fun i j => exists_abs_bound_of_continuous _ (hc i j)
  have hdiag : ∀ i : Fin 2, MatrixTransport.signedPair (diracAt x 1)
      (fun y => φ.value (timeBoundary t ht y) i i) = φ.value (timeBoundary t ht x) i i := by
    intro i
    rw [signedPair_diracAt x 1 _ (hc i i).measurable (hb i i), mul_one]
  unfold endpointPair
  simp [Fin.sum_univ_two, kbEndpoint, signedPair_zeroMeasure, hdiag]

theorem kbJet_value_00 (q : Q disk2) : kbJet.value q 0 0 = affF 0 (-1 / 8) 0 (1 / 4) q.val := by
  show diagM (affF 0 (-1 / 8) 0 (1 / 4) q.val) (affF 0 (-1 / 8) 0 0 q.val) 0 0 = _
  simp [diagM]

theorem kbJet_value_11 (q : Q disk2) : kbJet.value q 1 1 = affF 0 (-1 / 8) 0 0 q.val := by
  show diagM (affF 0 (-1 / 8) 0 (1 / 4) q.val) (affF 0 (-1 / 8) 0 0 q.val) 1 1 = _
  simp [diagM]

/-- **All-competitor lower certificate for the KB problem:** `V ≥ 1/4` for every transport
weight `L` (a `1 × 1` matrix), although both endpoint total matrices equal `I₂`. -/
theorem kb_lower (L : Matrix (Fin 1) (Fin 1) ℝ) :
    ENNReal.ofReal (1 / 4) ≤ Limit.minimumValue kbProblem L (1 : Mat 2) := by
  have h := ofReal_endpoint_le_minimumValue kbProblem L (1 : Mat 2) kbJet
    (fun q => kb_testField_mem L q)
  change ENNReal.ofReal
    (endpointPair (kbEndpoint diskB) kbJet 1 ⟨zero_le_one, le_rfl⟩ -
      endpointPair (kbEndpoint diskA) kbJet 0 ⟨le_rfl, zero_le_one⟩) ≤ _ at h
  erw [endpointPair_kbEndpoint, endpointPair_kbEndpoint] at h
  have hval : (kbJet.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ diskB) 0 0 +
      kbJet.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ diskB) 1 1) -
      (kbJet.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ diskA) 0 0 +
        kbJet.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ diskA) 1 1) = 1 / 4 := by
    simp only [kbJet_value_00, kbJet_value_11, timeBoundary_val]
    norm_num [affF, timeBoundary, diskA, diskB, pt2_zero, pt2_one]
  rw [hval] at h
  exact h

/-- **The KB obstruction.**  For any scalar transport weights `t_j` (in particular `t_j → ∞`)
the minimum values stay `≥ 1/4`, so they do not tend to the total-matrix Bures value `0`
(both total matrices are `I₂`, `kb_equal_total_matrices`). -/
theorem kb_obstruction (t : ℕ → ℝ) :
    (∀ j, ENNReal.ofReal (1 / 4) ≤ Limit.minimumValue kbProblem (!![t j]) (1 : Mat 2)) ∧
    ¬ Tendsto (fun j => Limit.minimumValue kbProblem (!![t j]) (1 : Mat 2)) atTop (𝓝 0) := by
  have hall : ∀ j, ENNReal.ofReal (1 / 4) ≤ Limit.minimumValue kbProblem (!![t j]) (1 : Mat 2) :=
    fun j => kb_lower _
  refine ⟨hall, fun h => ?_⟩
  have h0 : ENNReal.ofReal (1 / 4) ≤ 0 := ge_of_tendsto' h hall
  exact absurd h0 (not_le.mpr (ENNReal.ofReal_pos.mpr (by norm_num)))

#print axioms kb_lower
#print axioms kb_obstruction

end LiZouTransport.Examples

end
