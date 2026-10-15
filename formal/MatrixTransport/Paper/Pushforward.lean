import MatrixTransport.ReactionZero.LimitTheorem

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.Paper

open MatrixTransport.ReactionZero

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Continuous pushforward preserves the actual signed Jordan pairing. -/
theorem signedPair_map (s : SignedMeasure X) (T : C(X, Y)) (f : C(Y, ℝ)) :
    MatrixTransport.signedPair (s.map T) f = MatrixTransport.signedPair s (f.comp T) := by
  rw [signedPair_eq_vectorIntegral, signedPair_eq_vectorIntegral]
  have hi : s.Integrable (f ∘ T) := by
    change Integrable (f ∘ T) s.variation
    rw [← s.totalVariation_eq_variation]
    exact continuousTest_integrable (f.comp T) s.totalVariation
  exact VectorMeasure.integral_map T.continuous.measurable
    f.continuous.measurable.aestronglyMeasurable hi

variable {n k : ℕ}

/-- Coordinatewise pushforward of a genuine finite signed matrix triple. -/
def mapPath (T : C(X, Y)) (μ : Coord n k → SignedMeasure X) :
    Coord n k → SignedMeasure Y := fun c ↦ (μ c).map T

/-- Pullback identity for the complete continuous dual pairing. -/
theorem coordinatePair_map (T : C(X, Y)) (μ : Coord n k → SignedMeasure X)
    (a : C(Y, Coord n k → ℝ)) :
    Duality.coordinatePair (fun _ ↦ 1) (mapPath T μ) a =
      Duality.coordinatePair (fun _ ↦ 1) μ (a.comp T) := by
  unfold Duality.coordinatePair mapPath
  apply Finset.sum_congr rfl
  intro c _
  simp only [one_mul]
  exact signedPair_map (μ c) T (Duality.coordinateTest a c)

/-- Continuous pushforward cannot increase the original constant-weight support action. -/
theorem action_map_le (L : Matrix (Fin k) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (T : C(X, Y)) (μ : Coord n k → SignedMeasure X) :
    ReactionZero.action L H (mapPath T μ) ≤ ReactionZero.action L H μ := by
  rw [WeightedSet.action_eq_continuousDual, WeightedSet.action_eq_continuousDual]
  unfold Duality.continuousDual
  apply iSup_le
  intro a
  apply iSup_le
  intro ha
  rw [coordinatePair_map]
  exact le_iSup₂ (f := fun (b : C(X, Coord n k → ℝ))
    (_ : ∀ x, b x ∈ ReactionZero.dualSet L H) ↦
      ENNReal.ofReal (Duality.coordinatePair (fun _ ↦ 1) μ b))
    (a.comp T) (fun x ↦ ha (T x))

#print axioms signedPair_map
#print axioms coordinatePair_map
#print axioms action_map_le

end MatrixTransport.Paper
