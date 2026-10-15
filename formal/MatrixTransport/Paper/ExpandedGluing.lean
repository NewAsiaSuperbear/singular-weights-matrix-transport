import MatrixTransport.Paper.PathScaling
import MatrixTransport.EntrywiseBures.PathOperations

/-!
# Exact action addition on disjoint measurable pieces

The common reference may charge a junction slice. The hypothesis is only almost-everywhere
disjointness of the full coordinate densities, so zero-mass junctions do not contribute.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace MatrixTransport.ReactionZero.ExpandedGluing

variable {n k : ℕ} {X : Type*} [MeasurableSpace X]

/-- At a point occupied by at most one full path density, support cost adds exactly. -/
theorem cost_add_of_disjoint (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (v w : Coord n k → ℝ)
    (hvw : v = 0 ∨ w = 0) : cost L H (v + w) = cost L H v + cost L H w := by
  rcases hvw with rfl | rfl <;> simp [cost_zero]

/-- Original actions add on densities whose full tuples have disjoint essential supports. -/
theorem action_add_of_disjoint_density (L : Matrix (Fin k) (Fin k) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (ν : Measure X) [IsFiniteMeasure ν]
    (v w : Coord n k → X → ℝ)
    (hvM : ∀ c, Measurable (v c)) (hwM : ∀ c, Measurable (w c))
    (hvI : ∀ c, Integrable (v c) ν) (hwI : ∀ c, Integrable (w c) ν)
    (hvw : ∀ᵐ x ∂ν, (fun c ↦ v c x) = 0 ∨ (fun c ↦ w c x) = 0) :
    action L H (fun c ↦ ν.withDensityᵥ (v c) + ν.withDensityᵥ (w c)) =
      action L H (fun c ↦ ν.withDensityᵥ (v c)) +
        action L H (fun c ↦ ν.withDensityᵥ (w c)) := by
  have he : (fun c ↦ ν.withDensityᵥ (v c) + ν.withDensityᵥ (w c)) =
      (fun c ↦ ν.withDensityᵥ (v c + w c)) := by
    funext c
    exact (withDensityᵥ_add (hvI c) (hwI c)).symm
  rw [he, EntrywiseBures.action_densityPath L H (fun c ↦ v c + w c)
    (fun c ↦ (hvM c).add (hwM c)) (fun c ↦ (hvI c).add (hwI c)),
    EntrywiseBures.action_densityPath L H v hvM hvI,
    EntrywiseBures.action_densityPath L H w hwM hwI]
  calc
    (∫⁻ x, cost L H (fun c ↦ (v c + w c) x) ∂ν) =
        ∫⁻ x, cost L H (fun c ↦ v c x) + cost L H (fun c ↦ w c x) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hvw] with x hx
      exact cost_add_of_disjoint L H _ _ hx
    _ = _ := lintegral_add_left ((measurable_cost L H).comp
      (measurable_pi_iff.mpr hvM)) _

omit [MeasurableSpace X] in
/-- Disjoint measurable slabs supply the full-tuple condition used by action addition. -/
theorem tuple_disjoint_of_support (v w : Coord n k → X → ℝ) (S T : Set X)
    (hST : Disjoint S T) (hv : ∀ x ∉ S, ∀ c, v c x = 0)
    (hw : ∀ x ∉ T, ∀ c, w c x = 0) (x : X) :
    (fun c ↦ v c x) = 0 ∨ (fun c ↦ w c x) = 0 := by
  by_cases hx : x ∈ S
  · right
    exact funext (hw x (fun ht ↦ Set.disjoint_left.mp hST hx ht))
  · left
    exact funext (hv x hx)

section NativeTime

open EntrywiseBures MatrixTransport.ReactionZero.ClosedDomain

variable {d : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]

theorem signedPair_smul_measure {Y : Type*} [MeasurableSpace Y] [MetricSpace Y]
    [CompactSpace Y] [BorelSpace Y] (s : SignedMeasure Y) (r : ℝ) (f : C(Y, ℝ)) :
    MatrixTransport.signedPair (r • s) f = r * MatrixTransport.signedPair s f := by
  rw [signedPair_eq_vectorIntegral, signedPair_eq_vectorIntegral,
    VectorMeasure.integral_smul_vectorMeasure]
  rfl

theorem coordinatePair_scaleMassPath
    (μ : Coord n k → SignedMeasure (ClosedDomain.Q Ω)) (r : ℝ)
    (a : C(ClosedDomain.Q Ω, Coord n k → ℝ)) :
    Duality.coordinatePair (fun _ ↦ 1) (scaleMassPath r μ) a =
      Duality.coordinatePair (fun _ ↦ 1) μ (fun p ↦ scaleMassDensity r (a p)) := by
  unfold Duality.coordinatePair
  apply Finset.sum_congr rfl
  intro c _
  simp only [one_mul]
  rcases c with c | c
  · change MatrixTransport.signedPair (r • μ (Sum.inl c)) (Duality.coordinateTest a _) = _
    rw [signedPair_smul_measure]
    unfold MatrixTransport.signedPair
    change r * ((∫ x, a x (Sum.inl c) ∂(μ (Sum.inl c)).toJordanDecomposition.posPart) -
      (∫ x, a x (Sum.inl c) ∂(μ (Sum.inl c)).toJordanDecomposition.negPart)) =
      (∫ x, r * a x (Sum.inl c) ∂(μ (Sum.inl c)).toJordanDecomposition.posPart) -
      (∫ x, r * a x (Sum.inl c) ∂(μ (Sum.inl c)).toJordanDecomposition.negPart)
    rw [integral_const_mul, integral_const_mul]
    ring
  · rfl

/-- Exact pullback of the full native test pairing, including a zeroth-order spatial term. -/
theorem coordinatePair_compressPath (D : AdjointOperator d n k)
    (μ : Coord n k → SignedMeasure (ClosedDomain.Q Ω)) (φ : ClosedC1Jet Ω n)
    (a r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (har : a + r ∈ Icc (0 : ℝ) 1)
    (hr : 0 < r) :
    Duality.coordinatePair (fun _ ↦ 1) (compressPath μ a r ha har hr) (testField D φ) =
      Duality.coordinatePair (fun _ ↦ 1) μ
        (testField D (timePullbackJet φ a r ha har hr)) := by
  rw [compressPath, coordinatePair_pushPath _ (timeScale a r ha har hr).continuous.measurable]
  let field := (testField D φ).comp (timeScale a r ha har hr)
  change Duality.coordinatePair (fun _ ↦ 1) (scaleMassPath r μ) field = _
  rw [coordinatePair_scaleMassPath]
  congr 1
  ext p c
  rcases c with c | c | c <;> rfl

/-- A compressed arbitrary admissible path has the original endpoints at its new times. -/
theorem compressed_continuityEquation (D : AdjointOperator d n k)
    (g0 g1 : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (μ : Coord n k → SignedMeasure (ClosedDomain.Q Ω)) (hμ : PaperContinuityEquation D g0 g1 μ)
    (a r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (har : a + r ∈ Icc (0 : ℝ) 1)
    (hr : 0 < r) (φ : ClosedC1Jet Ω n) :
    Duality.coordinatePair (fun _ ↦ 1) (compressPath μ a r ha har hr) (testField D φ) =
      ClosedDomain.endpointPair g1 φ (a + r) har - ClosedDomain.endpointPair g0 φ a ha := by
  rw [coordinatePair_compressPath]
  have h := hμ (timePullbackJet φ a r ha har hr)
  change Duality.coordinatePair (fun _ ↦ 1) μ
    (testField D (timePullbackJet φ a r ha har hr)) = _ at h
  rw [h]
  simp only [paperTestFamily, ClosedDomain.endpointPair, timePullbackJet_value, timeScale,
    timeScalePoint, timeBoundary, ContinuousMap.coe_mk, mul_one, mul_zero, add_zero]

end NativeTime

#print axioms action_add_of_disjoint_density

end MatrixTransport.ReactionZero.ExpandedGluing
