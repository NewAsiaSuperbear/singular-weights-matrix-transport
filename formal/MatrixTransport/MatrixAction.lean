import MatrixTransport.MatrixBasics
import MatrixTransport.SupportFunction
import MatrixTransport.MeasureRepresentation

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace MatrixTransport

abbrev TransportCoord (r : ℕ) := (Fin 2 × Fin 2) ⊕ ((Fin 2 × Fin r) ⊕ (Fin 2 × Fin 2))

def mass {r : ℕ} (v : TransportCoord r → ℝ) : Mat2 :=
  fun i j => v (Sum.inl (i, j))

def flux {r : ℕ} (v : TransportCoord r → ℝ) : Flux r :=
  fun i j => v (Sum.inr (Sum.inl (i, j)))

def reaction {r : ℕ} (v : TransportCoord r → ℝ) : Mat2 :=
  fun i j => v (Sum.inr (Sum.inr (i, j)))

def packTriplet {r : ℕ} (X : Mat2) (Y : Flux r) (Z : Mat2) : TransportCoord r → ℝ
  | Sum.inl (i, j) => X i j
  | Sum.inr (Sum.inl (i, j)) => Y i j
  | Sum.inr (Sum.inr (i, j)) => Z i j

theorem mass_packTriplet {r : ℕ} (X : Mat2) (Y : Flux r) (Z : Mat2) :
    mass (packTriplet X Y Z) = X := by
  ext i j
  first | rfl | simp [mass, packTriplet]

theorem flux_packTriplet {r : ℕ} (X : Mat2) (Y : Flux r) (Z : Mat2) :
    flux (packTriplet X Y Z) = Y := by
  ext i j
  first | rfl | simp [flux, packTriplet]

theorem reaction_packTriplet {r : ℕ} (X : Mat2) (Y : Flux r) (Z : Mat2) :
    reaction (packTriplet X Y Z) = Z := by
  ext i j
  first | rfl | simp [reaction, packTriplet]

theorem packTriplet_unpacks {r : ℕ} (v : TransportCoord r → ℝ) :
    packTriplet (mass v) (flux v) (reaction v) = v := by
  funext c
  rcases c with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ <;> first | rfl | simp [packTriplet, mass, flux, reaction]

def dualSet (r : ℕ) : Set (TransportCoord r → ℝ) :=
  {a | (mass a).IsHermitian ∧ LocalDualConstraint (mass a) (flux a) (reaction a)}

def matrixCost (r : ℕ) (v : TransportCoord r → ℝ) : ℝ≥0∞ :=
  supportFunction (fun _ => 1) (dualSet r) v

theorem weightedPair_packTriplet {r : ℕ} (a : TransportCoord r → ℝ) (X : Mat2) (Y : Flux r)
    (Z : Mat2) :
    weightedPair (fun _ => 1) a (packTriplet X Y Z) =
      frob X (mass a) + frob Y (flux a) + frob Z (reaction a) := by
  have h : ∀ x y : ℝ, 1 * x * y = y * x := fun x y => by ring
  unfold weightedPair frob
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, packTriplet, mass, flux, reaction, h]
  ring

theorem matrixCost_zero (r : ℕ) : matrixCost r (0 : TransportCoord r → ℝ) = 0 :=
  supportFunction_zero _ _

theorem matrixCost_smul_nonneg (r : ℕ) (v : TransportCoord r → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    matrixCost r (t • v) = ENNReal.ofReal t * matrixCost r v :=
  supportFunction_smul_nonneg _ _ _ ht

theorem measurable_matrixCost (r : ℕ) : Measurable (matrixCost r) :=
  measurable_supportFunction _ _

theorem matrixCost_fenchel (r : ℕ) (v a : TransportCoord r → ℝ) (ha : a ∈ dualSet r) :
    ENNReal.ofReal (weightedPair (fun _ => 1) a v) ≤ matrixCost r v :=
  supportFunction_fenchel _ _ v a ha

theorem matrixCost_fenchel_packTriplet (r : ℕ) (X : Mat2) (Y : Flux r) (Z : Mat2)
    (a : TransportCoord r → ℝ) (ha : a ∈ dualSet r) :
    ENNReal.ofReal (frob X (mass a) + frob Y (flux a) + frob Z (reaction a)) ≤
      matrixCost r (packTriplet X Y Z) := by
  rw [← weightedPair_packTriplet]
  exact matrixCost_fenchel r _ a ha

theorem matrixCost_single_flux_upper {r : ℕ} (j0 : Fin r) (u v : ℝ) (hu : |u| ≤ 1 / 2) :
    matrixCost r (packTriplet (density u) (singleFlux j0 v) (0 : Mat2)) ≤
      ENNReal.ofReal (v ^ 2) := by
  unfold matrixCost supportFunction
  refine iSup_le fun a => iSup_le fun ha => ?_
  apply ENNReal.ofReal_le_ofReal
  rw [weightedPair_packTriplet]
  have h := single_flux_upper j0 u v (mass a) (flux a) (reaction a) hu ha.2
  have hz : frob (0 : Mat2) (reaction a) = 0 := by simp [frob]
  linarith

section Action

variable {α : Type*} [MeasurableSpace α]

def matrixDensity (r : ℕ) (μ : TransportCoord r → SignedMeasure α) (x : α) :
    TransportCoord r → ℝ :=
  fun c => (μ c).rnDeriv (jointReference μ) x

def matrixAction (r : ℕ) (μ : TransportCoord r → SignedMeasure α) : ℝ≥0∞ :=
  ∫⁻ x, matrixCost r (matrixDensity r μ x) ∂(jointReference μ)

theorem measurable_matrixDensity (r : ℕ) (μ : TransportCoord r → SignedMeasure α) :
    Measurable (matrixDensity r μ) :=
  Measurable.of_eval fun c => measurable_rnDeriv_jointReference μ c

theorem measurable_matrixAction_integrand (r : ℕ) (μ : TransportCoord r → SignedMeasure α) :
    Measurable (fun x => matrixCost r (matrixDensity r μ x)) :=
  (measurable_matrixCost r).comp (measurable_matrixDensity r μ)

end Action

end MatrixTransport

end
