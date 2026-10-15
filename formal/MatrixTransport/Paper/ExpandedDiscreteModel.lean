import MatrixTransport.ReactionZero.WeightedAction

/-!
# Finite conic constraints used by the numerical illustrations

This module records the displayed discrete continuity constraint, sampling averages,
channel blocks, and trace objective. These are definitions of the finite numerical model.
-/

set_option autoImplicit false

namespace MatrixTransport.Paper.ExpandedDiscreteModel

noncomputable section

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev BlockIndex := Sum (Fin 2) (Fin 2)

def symmetricPart (A : Matrix2) : Matrix2 :=
  (1 / 2 : ℝ) • (A + Matrix.transpose A)

def timeStep (nt : ℕ) : ℝ := 1 / (nt : ℝ)

def spaceStep (nx : ℕ) : ℝ := 1 / (nx : ℝ)

def positiveMesh (nt nx : ℕ) : Prop := 0 < nt ∧ 0 < nx

def nodalContinuity (dt dx : ℝ) (next previous right left reaction : Matrix2) : Prop :=
  dt⁻¹ • (next - previous) + dx⁻¹ • (symmetricPart right - symmetricPart left) =
    symmetricPart reaction

def nodalMassConstraint (M : Matrix2) : Prop := M.PosSemidef

def exteriorFluxConstraint (left right : Matrix2) : Prop := left = 0 ∧ right = 0

def midpointMass (previous next : Matrix2) : Matrix2 :=
  (1 / 2 : ℝ) • (previous + next)

def faceMass (leftPrevious leftNext rightPrevious rightNext : Matrix2) : Matrix2 :=
  midpointMass (midpointMass leftPrevious leftNext) (midpointMass rightPrevious rightNext)

def normalizedChannel (Z K : Matrix2) : Matrix2 := Z * K⁻¹

def positiveWeights (L H : Matrix2) : Prop := L.PosDef ∧ H.PosDef

def channelBlock (M Z S : Matrix2) : Matrix BlockIndex BlockIndex ℝ :=
  Matrix.fromBlocks M Z (Matrix.transpose Z) S

def channelCone (M Z S : Matrix2) : Prop := (channelBlock M Z S).PosSemidef

def traceObjective (dt dx : ℝ) (fluxAux reactionAux : List Matrix2) : ℝ :=
  (dt * dx / 2) * ((fluxAux.map Matrix.trace).sum + (reactionAux.map Matrix.trace).sum)

theorem blockIndex_card : Fintype.card BlockIndex = 4 := by
  simp [BlockIndex]

theorem traceObjective_balanced (dt dx : ℝ) (fluxAux : List Matrix2) :
    traceObjective dt dx fluxAux [] = (dt * dx / 2) * (fluxAux.map Matrix.trace).sum := by
  simp [traceObjective]

end

end MatrixTransport.Paper.ExpandedDiscreteModel
