import MatrixTransport.EntrywiseBures.UniformBures

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace LiZouTransport.Reaction
open MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures
open MatrixTransport.ReactionZero.Limit
variable {d n k : ℕ} {Ω : Set (Space d)}

/-- Pure reaction retains the original admissibility conditions and sets each transport
flux coordinate measure equal to zero. -/
def PureReaction (P : Problem Ω n k) (ν : Path Ω n k) : Prop :=
  Good P ν ∧ ∀ (i : Fin n) (j : Fin k), ν (Sum.inr (Sum.inl (i,j))) = 0

/-- The original weighted action minimized over the zero-flux subclass. -/
def pureReactionMinimumValue (P : Problem Ω n k) (L : Matrix (Fin k) (Fin k) ℝ)
    (H : RMat n) : ℝ≥0∞ :=
  MatrixTransport.ReactionZero.constrainedInfimum (PureReaction P)
    (MatrixTransport.ReactionZero.action L H)

/-- Restricting to pure reaction cannot decrease the original minimum. -/
theorem minimumValue_le_pureReactionMinimumValue (P : Problem Ω n k)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : RMat n) :
    minimumValue P L H ≤ pureReactionMinimumValue P L H := by
  apply le_iInf
  intro ν
  apply le_iInf
  intro hν
  exact iInf_le_of_le ν (iInf_le_of_le hν.1 le_rfl)

variable [Fact (IsCompact Ω)]

/-- The weighted Bures value is the exact pure-reaction minimum for uniform PSD endpoints,
and a constructed zero-flux signed Radon path attains it. Singular PSD endpoints and
arbitrary probability references, including boundary atoms, are allowed. -/
theorem pure_reaction_minimum_attained (R : PSDSqrt n) (G : HubGeometry d Ω)
    (D : AdjointOperator d n k)
    (hD0 : ∀ A : RMat n, A.IsHermitian → D.D0 A = 0)
    (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    {H A0 A1 : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    (hA0 : A0.PosSemidef) (hA1 : A1.PosSemidef) (L : Matrix (Fin k) (Fin k) ℝ) :
    pureReactionMinimumValue (uniformProblem D μ A0 A1 hA0 hA1) L H =
      ENNReal.ofReal (buresValue R H A0 A1) ∧
    ∃ ν : Path Ω n k, PureReaction (uniformProblem D μ A0 A1 hA0 hA1) ν ∧
      MatrixTransport.ReactionZero.action L H ν = ENNReal.ofReal (buresValue R H A0 A1) := by
  obtain ⟨P,Δ,hP,hPD,hcost⟩ := exists_bures_reaction_factor R hH hHu hA0 hA1
  let ν : Path Ω n k := reactionPath μ H P Δ 0 1 ⟨le_rfl,zero_le_one⟩
    (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
  have hGood : Good (uniformProblem D μ A0 A1 hA0 hA1) ν := by
    simpa only [hP,hPD] using reactionPath_good_uniform G D μ hH P Δ
  have hPure : PureReaction (uniformProblem D μ A0 A1 hA0 hA1) ν :=
    ⟨hGood, fun i j ↦ reactionPath_flux_zero μ H P Δ 0 1 _ _ _ i j⟩
  have hUpper : MatrixTransport.ReactionZero.action L H ν ≤
      ENNReal.ofReal (buresValue R H A0 A1) := by
    have h := reactionPath_action_le μ L hH P Δ 0 1
      ⟨le_rfl,zero_le_one⟩ (by norm_num : (0 : ℝ) + 1 ∈ Icc 0 1) zero_lt_one
    simpa only [div_one,hμ,mul_one,hcost] using h
  have hLower : ENNReal.ofReal (buresValue R H A0 A1) ≤
      MatrixTransport.ReactionZero.action L H ν :=
    (uniform_bures_lower R D hD0 μ hμ hH hHu hA0 hA1 L).trans
      (iInf_le_of_le ν (iInf_le_of_le hGood le_rfl))
  have hAction := le_antisymm hUpper hLower
  refine ⟨?_,ν,hPure,hAction⟩
  apply le_antisymm
  · exact iInf_le_of_le ν (iInf_le_of_le hPure hUpper)
  · exact (uniform_bures_lower R D hD0 μ hμ hH hHu hA0 hA1 L).trans
      (minimumValue_le_pureReactionMinimumValue _ L H)

#print axioms minimumValue_le_pureReactionMinimumValue
#print axioms pure_reaction_minimum_attained
end LiZouTransport.Reaction
