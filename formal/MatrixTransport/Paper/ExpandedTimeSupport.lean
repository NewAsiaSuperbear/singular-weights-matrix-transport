import MatrixTransport.EntrywiseBures.ReactionPiece

/-!
# Time support of the concrete transport and reaction segments

The source time reference is Lebesgue measure on the unit interval. Its affine images
have no time-slice atoms when the duration is nonzero. Every coordinate of the actual
constructed path is supported in its closed time slab, including singular spatial data.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace MatrixTransport.Paper.ExpandedTimeSupport

open MatrixTransport.EntrywiseBures MatrixTransport.ReactionZero.ClosedDomain

theorem unitTime_level_zero (t : ℝ) : unitTime {s : UnitI | s.val = t} = 0 := by
  unfold unitTime
  rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
  · apply le_antisymm ?_ bot_le
    calc
      volume (Subtype.val '' {s : UnitI | s.val = t}) ≤ volume ({t} : Set ℝ) := by
        apply measure_mono
        rintro x ⟨s, hs, rfl⟩
        exact hs
      _ = 0 := by simp

theorem product_time_level_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (t : ℝ) :
    (unitTime.prod μ) {p : UnitI × X | p.1.val = t} = 0 := by
  have he : {p : UnitI × X | p.1.val = t} = {s : UnitI | s.val = t} ×ˢ univ := by
    ext p
    simp
  rw [he, Measure.prod_prod, unitTime_level_zero, zero_mul]

theorem product_affine_level_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (a b t : ℝ) (hb : b ≠ 0) :
    (unitTime.prod μ) {p : UnitI × X | a + b * p.1.val = t} = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    (unitTime.prod μ) {p : UnitI × X | a + b * p.1.val = t} ≤
        (unitTime.prod μ) {p : UnitI × X | p.1.val = (t - a) / b} := by
      apply measure_mono
      intro p hp
      apply (eq_div_iff hb).2
      change a + b * p.1.val = t at hp
      nlinarith
    _ = 0 := product_time_level_zero μ _

theorem pushed_density_totalVariation_zero {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (f : X → ℝ)
    (T : X → Y) (hT : Measurable T) (B : Set Y) (hB : MeasurableSet B)
    (hnull : μ (T ⁻¹' B) = 0) :
    (pushSigned T (μ.withDensityᵥ f)).totalVariation B = 0 := by
  have hvec : pushSigned T (μ.withDensityᵥ f) ≪ᵥ (μ.map T).toENNRealVectorMeasure := by
    refine VectorMeasure.AbsolutelyContinuous.mk fun A hA hzero ↦ ?_
    rw [Measure.toENNRealVectorMeasure_apply_measurable hA, Measure.map_apply hT hA] at hzero
    rw [pushSigned_apply hT _ hA]
    apply μ.withDensityᵥ_absolutelyContinuous f
    rwa [Measure.toENNRealVectorMeasure_apply_measurable (hT hA)]
  have hac : (pushSigned T (μ.withDensityᵥ f)).totalVariation ≪ μ.map T := by
    simpa only [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] using
      (SignedMeasure.absolutelyContinuous_ennreal_iff _ _).1 hvec
  apply hac
  rwa [Measure.map_apply hT hB]

theorem affine_time_bounds (a b : ℝ) (s : UnitI) :
    min a (a + b) ≤ a + b * s.val ∧ a + b * s.val ≤ max a (a + b) := by
  rcases s.property with ⟨hs0, hs1⟩
  by_cases hb : 0 ≤ b
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg hb hs0)
    · have h := mul_le_mul_of_nonneg_left hs1 hb
      linarith
  · have hb' : b ≤ 0 := le_of_lt (lt_of_not_ge hb)
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    constructor
    · have h := mul_le_mul_of_nonpos_left hs1 hb'
      linarith
    · exact add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hb' hs0)

variable {d n k : ℕ} {Ω : Set (Space d)}

def timeSlab (a b : ℝ) : Set (MatrixTransport.ReactionZero.ClosedDomain.Q Ω) :=
  {q | min a (a + b) ≤ q.val.1 ∧ q.val.1 ≤ max a (a + b)}

def timeSlice (t : ℝ) : Set (MatrixTransport.ReactionZero.ClosedDomain.Q Ω) := {q | q.val.1 = t}

theorem measurableSet_timeSlab (a b : ℝ) : MeasurableSet (timeSlab (Ω := Ω) a b) := by
  exact ((isClosed_le continuous_const (continuous_fst.comp continuous_subtype_val)).inter
    (isClosed_le (continuous_fst.comp continuous_subtype_val) continuous_const)).measurableSet

theorem measurableSet_timeSlice (t : ℝ) : MeasurableSet (timeSlice (Ω := Ω) t) := by
  exact (isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const).measurableSet

theorem charMap_mem_timeSlab (G : HubGeometry d Ω) (a b : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + b ∈ Icc (0 : ℝ) 1)
    (p : UnitI × ↥Ω) : charMap G a b ha hab p ∈ timeSlab a b :=
  affine_time_bounds a b p.1

variable [Fact (IsCompact Ω)]

theorem lagPath_totalVariation_timeSlice_zero (G : HubGeometry d Ω)
    (g : (Fin n × Fin n) → SignedMeasure ↥Ω) (a σ r t : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + σ * r ∈ Icc (0 : ℝ) 1)
    (hσr : σ * r ≠ 0) (c : MatrixTransport.ReactionZero.Coord n (d * n)) :
    (lagPath G g a σ r ha hab c).totalVariation (timeSlice t) = 0 := by
  apply pushed_density_totalVariation_zero (lagRef g) _ (charMap G a (σ * r) ha hab)
    (continuous_charMap G a (σ * r) ha hab).measurable _ (measurableSet_timeSlice t)
  exact product_affine_level_zero (endpointRef g) a (σ * r) t hσr

theorem lagPath_totalVariation_outside_zero (G : HubGeometry d Ω)
    (g : (Fin n × Fin n) → SignedMeasure ↥Ω) (a σ r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + σ * r ∈ Icc (0 : ℝ) 1)
    (c : MatrixTransport.ReactionZero.Coord n (d * n)) :
    (lagPath G g a σ r ha hab c).totalVariation (timeSlab a (σ * r))ᶜ = 0 := by
  apply pushed_density_totalVariation_zero (lagRef g) _ (charMap G a (σ * r) ha hab)
    (continuous_charMap G a (σ * r) ha hab).measurable _
    (measurableSet_timeSlab a (σ * r)).compl
  have he : (charMap G a (σ * r) ha hab) ⁻¹' (timeSlab a (σ * r))ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact hp (charMap_mem_timeSlab G a (σ * r) ha hab p)
  rw [he, measure_empty]

theorem reactionMap_mem_timeSlab (a r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r) (p : UnitI × ↥Ω) :
    LiZouTransport.Reaction.reactionMap a r ha hab hr p ∈ timeSlab a r :=
  affine_time_bounds a r p.1

theorem reactionPath_totalVariation_timeSlice_zero (μ : Measure ↥Ω) [IsFiniteMeasure μ]
    (H P Δ : RMat n) (a r t : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r)
    (c : MatrixTransport.ReactionZero.Coord n k) :
    (LiZouTransport.Reaction.reactionPath μ H P Δ a r ha hab hr c).totalVariation
      (timeSlice t) = 0 := by
  apply pushed_density_totalVariation_zero (LiZouTransport.Reaction.reactionRef μ) _
    (LiZouTransport.Reaction.reactionMap a r ha hab hr)
    (LiZouTransport.Reaction.reactionMap a r ha hab hr).continuous.measurable _
    (measurableSet_timeSlice t)
  exact product_affine_level_zero μ a r t hr.ne'

theorem reactionPath_totalVariation_outside_zero (μ : Measure ↥Ω) [IsFiniteMeasure μ]
    (H P Δ : RMat n) (a r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + r ∈ Icc (0 : ℝ) 1) (hr : 0 < r)
    (c : MatrixTransport.ReactionZero.Coord n k) :
    (LiZouTransport.Reaction.reactionPath μ H P Δ a r ha hab hr c).totalVariation
      (timeSlab a r)ᶜ = 0 := by
  apply pushed_density_totalVariation_zero (LiZouTransport.Reaction.reactionRef μ) _
    (LiZouTransport.Reaction.reactionMap a r ha hab hr)
    (LiZouTransport.Reaction.reactionMap a r ha hab hr).continuous.measurable _
    (measurableSet_timeSlab a r).compl
  have he : (LiZouTransport.Reaction.reactionMap (Ω := Ω) a r ha hab hr) ⁻¹'
      (timeSlab (Ω := Ω) a r)ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact hp (reactionMap_mem_timeSlab a r ha hab hr p)
  rw [he, measure_empty]

end MatrixTransport.Paper.ExpandedTimeSupport
