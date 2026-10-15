import MatrixTransport.Paper.ExpandedSlabGluing
import MatrixTransport.EntrywiseBures.HubRecovery

/-! # Exact additivity for the concrete three-piece hub path

The contraction, hub reaction and expansion are the original signed-coordinate constructors.
Positive durations give null junction slices, including for singular spatial endpoint data.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace MatrixTransport.Paper.ExpandedHubGluing

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain
open MatrixTransport.EntrywiseBures MatrixTransport.Paper.ExpandedTimeSupport
open MatrixTransport.Paper.ExpandedSlabGluing

variable {d n : ℕ} {Ω : Set (Space d)}

/-- Half-open time cuts allocate each null junction to the later segment. -/
def timeBefore (t : ℝ) : Set (MatrixTransport.ReactionZero.ClosedDomain.Q Ω) :=
  {q | q.val.1 < t}

theorem measurableSet_timeBefore (t : ℝ) : MeasurableSet (timeBefore (Ω := Ω) t) :=
  (isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const).measurableSet

/-- A closed slab starting after the cut has no mass on the earlier half-open slab. -/
theorem totalVariation_before_zero
    (μ : SignedMeasure (MatrixTransport.ReactionZero.ClosedDomain.Q Ω)) (a b t : ℝ)
    (ht : t ≤ min a (a + b))
    (hμ : μ.totalVariation (timeSlab a b)ᶜ = 0) :
    μ.totalVariation (timeBefore t) = 0 := by
  apply measure_mono_null ?_ hμ
  intro q hq hslab
  change q.val.1 < t at hq
  change min a (a + b) ≤ q.val.1 ∧ q.val.1 ≤ max a (a + b) at hslab
  linarith [hslab.1]

/-- A slab ending at the cut is supported in the half-open slab once its junction is null. -/
theorem totalVariation_after_zero
    (μ : SignedMeasure (MatrixTransport.ReactionZero.ClosedDomain.Q Ω)) (a b t : ℝ)
    (ht : max a (a + b) ≤ t)
    (hμ : μ.totalVariation (timeSlab a b)ᶜ = 0)
    (hslice : μ.totalVariation (timeSlice t) = 0) :
    μ.totalVariation (timeBefore t)ᶜ = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    μ.totalVariation (timeBefore t)ᶜ ≤
        μ.totalVariation ((timeSlab a b)ᶜ ∪ timeSlice t) := by
      apply measure_mono
      intro q hq
      by_cases hslab : q ∈ timeSlab a b
      · right
        change q.val.1 = t
        change ¬q.val.1 < t at hq
        change min a (a + b) ≤ q.val.1 ∧ q.val.1 ≤ max a (a + b) at hslab
        linarith [hslab.2]
      · exact Or.inl hslab
    _ ≤ μ.totalVariation (timeSlab a b)ᶜ + μ.totalVariation (timeSlice t) :=
      measure_union_le _ _
    _ = 0 := by rw [hμ, hslice, add_zero]

variable [Fact (IsCompact Ω)]

/-- The actual first Lagrangian piece from the initial endpoint to the hub. -/
def contraction (G : HubGeometry d Ω) (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (r0 r1 r2 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) : Limit.Path Ω n (d * n) :=
  lagPath G g 0 1 r0 ⟨le_rfl, zero_le_one⟩ (by constructor <;> linarith)

/-- The actual middle reaction piece, concentrated at the interior hub. -/
def hubReaction (G : HubGeometry d Ω) (H W Δ : RMat n)
    (r0 r1 r2 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) : Limit.Path Ω n (d * n) :=
  LiZouTransport.Reaction.reactionPath (LiZouTransport.Hub.hubMeasure G) H W Δ r0 r1
    (by constructor <;> linarith) (by constructor <;> linarith) hr1

/-- The original backward parametrization of expansion from the hub to the terminal endpoint. -/
def expansion (G : HubGeometry d Ω) (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (r0 r1 r2 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) : Limit.Path Ω n (d * n) :=
  lagPath G g 1 (-1) r2 ⟨zero_le_one, le_rfl⟩ (by constructor <;> linarith)

/-- The literal contraction-plus-reaction-plus-expansion coordinate family. -/
def hubPath (G : HubGeometry d Ω)
    (g0 g1 : (Fin n × Fin n) → SignedMeasure ↥Ω) (H W Δ : RMat n)
    (r0 r1 r2 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) : Limit.Path Ω n (d * n) :=
  (contraction G g0 r0 r1 r2 hr0 hr1 hr2 hsum +
    hubReaction G H W Δ r0 r1 r2 hr0 hr1 hr2 hsum) +
    expansion G g1 r0 r1 r2 hr0 hr1 hr2 hsum

/-- Every contraction coordinate is supported before the first junction. -/
theorem contraction_before_first (G : HubGeometry d Ω)
    (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (r0 r1 r2 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) (c : Coord n (d * n)) :
    (contraction G g r0 r1 r2 hr0 hr1 hr2 hsum c).totalVariation
      (timeBefore r0)ᶜ = 0 := by
  unfold contraction
  apply totalVariation_after_zero _ 0 (1 * r0) r0
  · simp [max_eq_right hr0.le]
  · exact lagPath_totalVariation_outside_zero G g 0 1 r0 _ _ c
  · exact lagPath_totalVariation_timeSlice_zero G g 0 1 r0 r0 _ _
      (by simpa using hr0.ne') c

/-- Every middle-piece coordinate vanishes on the earlier half-open slab. -/
theorem reaction_after_first (G : HubGeometry d Ω) (H W Δ : RMat n)
    (r0 r1 r2 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) (c : Coord n (d * n)) :
    (hubReaction G H W Δ r0 r1 r2 hr0 hr1 hr2 hsum c).totalVariation
      (timeBefore r0) = 0 := by
  unfold hubReaction
  apply totalVariation_before_zero _ r0 r1 r0
  · rw [min_eq_left (by linarith)]
  · exact reactionPath_totalVariation_outside_zero _ H W Δ r0 r1 _ _ hr1 c

/-- Contraction has no total variation beyond the second junction either. -/
theorem contraction_before_second (G : HubGeometry d Ω)
    (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (r0 r1 r2 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) (c : Coord n (d * n)) :
    (contraction G g r0 r1 r2 hr0 hr1 hr2 hsum c).totalVariation
      (timeBefore (r0 + r1))ᶜ = 0 := by
  unfold contraction
  apply totalVariation_after_zero _ 0 (1 * r0) (r0 + r1)
  · simp only [one_mul, zero_add, max_eq_right hr0.le]
    linarith
  · exact lagPath_totalVariation_outside_zero G g 0 1 r0 _ _ c
  · exact lagPath_totalVariation_timeSlice_zero G g 0 1 r0 (r0 + r1) _ _
      (by simpa using hr0.ne') c

/-- The reaction piece is supported before its terminal junction. -/
theorem reaction_before_second (G : HubGeometry d Ω) (H W Δ : RMat n)
    (r0 r1 r2 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) (c : Coord n (d * n)) :
    (hubReaction G H W Δ r0 r1 r2 hr0 hr1 hr2 hsum c).totalVariation
      (timeBefore (r0 + r1))ᶜ = 0 := by
  unfold hubReaction
  apply totalVariation_after_zero _ r0 r1 (r0 + r1)
  · rw [max_eq_right (by linarith)]
  · exact reactionPath_totalVariation_outside_zero _ H W Δ r0 r1 _ _ hr1 c
  · exact reactionPath_totalVariation_timeSlice_zero _ H W Δ r0 r1 (r0 + r1) _ _ hr1 c

/-- The concrete expansion has no total variation before the second junction. -/
theorem expansion_after_second (G : HubGeometry d Ω)
    (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (r0 r1 r2 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) (c : Coord n (d * n)) :
    (expansion G g r0 r1 r2 hr0 hr1 hr2 hsum c).totalVariation
      (timeBefore (r0 + r1)) = 0 := by
  unfold expansion
  apply totalVariation_before_zero _ 1 ((-1) * r2) (r0 + r1)
  · rw [min_eq_right (by linarith)]
    linarith
  · exact lagPath_totalVariation_outside_zero G g 1 (-1) r2 _ _ c

/-- Exact action additivity of the original three concrete hub pieces. -/
theorem hubPath_action_eq (G : HubGeometry d Ω)
    (g0 g1 : (Fin n × Fin n) → SignedMeasure ↥Ω) (H W Δ : RMat n)
    (L : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)
    (r0 r1 r2 : ℝ) (hr0 : 0 < r0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hsum : r0 + r1 + r2 = 1) :
    action L H (hubPath G g0 g1 H W Δ r0 r1 r2 hr0 hr1 hr2 hsum) =
      (action L H (contraction G g0 r0 r1 r2 hr0 hr1 hr2 hsum) +
        action L H (hubReaction G H W Δ r0 r1 r2 hr0 hr1 hr2 hsum)) +
        action L H (expansion G g1 r0 r1 r2 hr0 hr1 hr2 hsum) := by
  let μ0 := contraction G g0 r0 r1 r2 hr0 hr1 hr2 hsum
  let μ1 := hubReaction G H W Δ r0 r1 r2 hr0 hr1 hr2 hsum
  let μ2 := expansion G g1 r0 r1 r2 hr0 hr1 hr2 hsum
  have h01 : action L H (μ0 + μ1) = action L H μ0 + action L H μ1 :=
    action_add_of_disjoint_measures L H μ0 μ1 (timeBefore r0)
      (measurableSet_timeBefore r0)
      (fun c ↦ contraction_before_first G g0 r0 r1 r2 hr0 hr1 hr2 hsum c)
      (fun c ↦ reaction_after_first G H W Δ r0 r1 r2 hr0 hr1 hr2 hsum c)
  have hleft : ∀ c, ((μ0 + μ1) c).totalVariation (timeBefore (r0 + r1))ᶜ = 0 := by
    intro c
    exact totalVariation_add_zero (μ0 c) (μ1 c) _
      (contraction_before_second G g0 r0 r1 r2 hr0 hr1 hr2 hsum c)
      (reaction_before_second G H W Δ r0 r1 r2 hr0 hr1 hr2 hsum c)
  have h012 := action_add_of_disjoint_measures L H (μ0 + μ1) μ2
    (timeBefore (r0 + r1)) (measurableSet_timeBefore (r0 + r1)) hleft
    (fun c ↦ expansion_after_second G g1 r0 r1 r2 hr0 hr1 hr2 hsum c)
  change action L H ((μ0 + μ1) + μ2) = (action L H μ0 + action L H μ1) + action L H μ2
  rw [h012, h01]

#print axioms contraction_before_first
#print axioms reaction_after_first
#print axioms contraction_before_second
#print axioms reaction_before_second
#print axioms expansion_after_second
#print axioms hubPath_action_eq

end MatrixTransport.Paper.ExpandedHubGluing
