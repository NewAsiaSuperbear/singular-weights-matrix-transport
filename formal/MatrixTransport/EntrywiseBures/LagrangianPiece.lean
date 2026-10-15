import MatrixTransport.EntrywiseBures.PathOperations
import MatrixTransport.EntrywiseBures.PointwiseCost
import MatrixTransport.EntrywiseBures.EndpointDensity

/-!
# Lagrangian contraction and expansion of an arbitrary PSD Radon endpoint

For a PSD endpoint family `g` with RN density `m` against `λ = jointReference g`, a time
segment `[a, a + σ r]` (`σ = ±1`, `r > 0`) and a hub `x*` in the interior of the convex compact
domain, the piece is the GENUINE signed pushforward of the density path
`(r m(x), σ m(x) V(x* - x), 0) ds ⊗ λ` on `[0,1] × Ω` along
`Θ(s, x) = (a + σ r s, (1 - s) x + s x*)`.

* `lagPiece_coordinatePair`: for EVERY original closed-domain jet `φ`, the original pairing is
  `σ (⟨φ(a + σ r, x*), G(Ω)⟩ - endpointPair g φ a)`.  The proof uses the jet chain rule of
  `Partials.lean`, the interval FTC and Fubini; boundary atoms of `g` are included because
  every trajectory with `s > 0` lies in the interior.
* `lagPiece_action_le`: at transport weight `t I`, the ORIGINAL action is at most
  `M_g / (2 t² r)`, `M_g = Σᵢ ⟨gᵢᵢ, ‖x - x*‖²⟩`.

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace MatrixTransport.EntrywiseBures

open MatrixTransport.ReactionZero.ClosedDomain

/-! ### The unit time interval -/

abbrev UnitI := ↥(Icc (0 : ℝ) 1)

instance unitI_compactSpace : CompactSpace UnitI :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- Lebesgue measure on `[0,1]`. -/
def unitTime : Measure UnitI := Measure.comap Subtype.val volume

theorem unitTime_univ : unitTime univ = 1 := by
  unfold unitTime
  rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply, Set.image_univ,
    Subtype.range_coe, Real.volume_Icc]
  simp

instance unitTime_isFiniteMeasure : IsFiniteMeasure unitTime :=
  ⟨by rw [unitTime_univ]; exact ENNReal.one_lt_top⟩

theorem integral_unitTime (f : ℝ → ℝ) :
    ∫ s, f s.val ∂unitTime = ∫ s in (0 : ℝ)..1, f s := by
  unfold unitTime
  rw [integral_subtype_comap measurableSet_Icc f, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]

/-! ### Small frob lemmas -/

section Frob

variable {n : ℕ}

theorem frob_add_left (X Y M : RMat n) :
    ReactionZero.frob (X + Y) M = ReactionZero.frob X M + ReactionZero.frob Y M := by
  simp only [ReactionZero.frob, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem frob_sum_left {ι : Type*} (s : Finset ι) (X : ι → RMat n) (M : RMat n) :
    ReactionZero.frob (∑ ℓ ∈ s, X ℓ) M = ∑ ℓ ∈ s, ReactionZero.frob (X ℓ) M := by
  unfold ReactionZero.frob
  simp only [Matrix.sum_apply, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact Finset.sum_comm

theorem continuous_frob_left (M : RMat n) : Continuous fun X : RMat n ↦ ReactionZero.frob X M := by
  unfold ReactionZero.frob
  exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
    by fun_prop

end Frob

/-! ### Geometry of the hub -/

/-- A convex domain with an interior hub. -/
structure HubGeometry (d : ℕ) (Ω : Set (Space d)) where
  hub : Space d
  convex : Convex ℝ Ω
  hub_mem : hub ∈ interior Ω

variable {d n : ℕ} {Ω : Set (Space d)}

/-- `Θ(s, x) = (a + b s, (1 - s) x + s x*)`. -/
def charPoint (G : HubGeometry d Ω) (a b s : ℝ) (x : Space d) : Ambient d :=
  (a + b * s, (1 - s) • x + s • G.hub)

theorem charPoint_mem_domain (G : HubGeometry d Ω) {a b s : ℝ} {x : Space d}
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + b ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Ω) : charPoint G a b s x ∈ domain Ω := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 : 0 ≤ (1 - s) * a := mul_nonneg (sub_nonneg.2 hs.2) ha.1
    have h2 : 0 ≤ s * (a + b) := mul_nonneg hs.1 hab.1
    show 0 ≤ a + b * s
    nlinarith
  · have h1 : (1 - s) * a ≤ (1 - s) * 1 := mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.2 hs.2)
    have h2 : s * (a + b) ≤ s * 1 := mul_le_mul_of_nonneg_left hab.2 hs.1
    show a + b * s ≤ 1
    nlinarith
  · exact G.convex hx (interior_subset G.hub_mem) (sub_nonneg.2 hs.2) hs.1 (by ring)

theorem charPoint_mem_interior (G : HubGeometry d Ω) {a σ r s : ℝ} {x : Space d}
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + σ * r ∈ Icc (0 : ℝ) 1) (hσ : σ = 1 ∨ σ = -1)
    (hr : 0 < r) (hs : s ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ω) :
    charPoint G a (σ * r) s x ∈ interior (domain Ω) := by
  rw [interior_domain_eq]
  have hrs : r * s < r := mul_lt_of_lt_one_right hr hs.2
  have hrs0 : 0 < r * s := mul_pos hr hs.1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show 0 < a + σ * r * s
    rcases hσ with rfl | rfl
    · nlinarith [ha.1]
    · nlinarith [hab.1]
  · show a + σ * r * s < 1
    rcases hσ with rfl | rfl
    · nlinarith [hab.2]
    · nlinarith [ha.2]
  · show (1 - s) • x + s • G.hub ∈ interior Ω
    have h : s • G.hub + (1 - s) • x ∈ interior Ω := by
      first
        | exact G.convex.combo_interior_self_mem_interior G.hub_mem hx hs.1
            (sub_nonneg.2 hs.2.le) (by ring)
        | exact G.convex.combo_interior_closure_mem_interior G.hub_mem (subset_closure hx) hs.1
            (sub_nonneg.2 hs.2.le) (by ring)
    rwa [add_comm] at h

theorem charPoint_affine (G : HubGeometry d Ω) (a b s s0 : ℝ) (x : Space d) :
    charPoint G a b s x = charPoint G a b s0 x + (s - s0) • ((b, G.hub - x) : Ambient d) := by
  refine Prod.ext ?_ ?_
  · simp only [charPoint, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    ring
  · simp only [charPoint, Prod.snd_add, Prod.smul_snd]
    module

theorem charPoint_zero (G : HubGeometry d Ω) (a b : ℝ) (x : Space d) :
    charPoint G a b 0 x = (a, x) := by
  simp [charPoint]

theorem charPoint_one (G : HubGeometry d Ω) (a b : ℝ) (x : Space d) :
    charPoint G a b 1 x = (a + b, G.hub) := by
  simp [charPoint]

theorem continuous_charPoint (G : HubGeometry d Ω) (a b : ℝ) (x : Space d) :
    Continuous fun s ↦ charPoint G a b s x := by
  unfold charPoint
  exact (continuous_const.add (continuous_const.mul continuous_id)).prodMk
    (((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const))

/-- The characteristic map from `[0,1] × Ω` into the closed space-time domain. -/
def charMap (G : HubGeometry d Ω) (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + b ∈ Icc (0 : ℝ) 1) (p : UnitI × ↥Ω) : Q Ω :=
  ⟨charPoint G a b p.1.val p.2.val, charPoint_mem_domain G ha hab p.1.property p.2.property⟩

theorem continuous_charMap (G : HubGeometry d Ω) (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + b ∈ Icc (0 : ℝ) 1) : Continuous (charMap G a b ha hab) := by
  apply Continuous.subtype_mk
  unfold charPoint
  exact (continuous_const.add (continuous_const.mul (continuous_subtype_val.comp continuous_fst))).prodMk
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const))

/-! ### Velocity towards the hub -/

def hubVel (G : HubGeometry d Ω) (x : ↥Ω) : Fin d → ℝ := fun ℓ ↦ (G.hub - (x : Space d)) ℓ

theorem continuous_hubVel (G : HubGeometry d Ω) (ℓ : Fin d) :
    Continuous fun x : ↥Ω ↦ hubVel G x ℓ :=
  (EuclideanSpace.proj ℓ : Space d →L[ℝ] ℝ).continuous.comp
    (continuous_const.sub continuous_subtype_val)

theorem sum_hubVel_sq (G : HubGeometry d Ω) (x : ↥Ω) :
    ∑ ℓ, hubVel G x ℓ ^ 2 = ‖(x : Space d) - G.hub‖ ^ 2 := by
  rw [norm_sub_rev, EuclideanSpace.norm_eq, Real.sq_sqrt
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
  rw [Real.norm_eq_abs, sq_abs]
  rfl

/-! ### The density path -/

/-- Pointwise density `(r m, σ m V(x* - x), 0)`. -/
def lagDensity (G : HubGeometry d Ω) (g : (Fin n × Fin n) → SignedMeasure ↥Ω) (r σ : ℝ)
    (x : ↥Ω) : ReactionZero.Coord n (d * n) → ℝ :=
  ReactionZero.pack (r • endpointDensity g x)
    (σ • (endpointDensity g x * velocityMatrix (n := n) (hubVel G x))) 0

variable [Fact (IsCompact Ω)]

theorem hubVel_bounded (G : HubGeometry d Ω) (ℓ : Fin d) :
    ∃ C : ℝ, ∀ x : ↥Ω, |hubVel G x ℓ| ≤ C := by
  let f : C(↥Ω, ℝ) := ⟨fun x ↦ hubVel G x ℓ, continuous_hubVel G ℓ⟩
  exact ⟨‖f‖, fun x ↦ by simpa only [Real.norm_eq_abs, f, ContinuousMap.coe_mk] using f.norm_coe_le_norm x⟩

theorem measurable_lagDensity (G : HubGeometry d Ω) (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (r σ : ℝ) (c : ReactionZero.Coord n (d * n)) :
    Measurable fun x ↦ lagDensity G g r σ x c := by
  rcases c with ⟨i, j⟩ | ⟨i, c⟩ | ⟨i, j⟩
  · simp only [lagDensity, ReactionZero.pack, Matrix.smul_apply, smul_eq_mul]
    exact (measurable_endpointDensity_entry g i j).const_mul r
  · simp only [lagDensity, ReactionZero.pack, Matrix.smul_apply, smul_eq_mul,
      mul_velocityMatrix_apply]
    exact ((continuous_hubVel G _).measurable.mul
      (measurable_endpointDensity_entry g _ _)).const_mul σ
  · simp only [lagDensity, ReactionZero.pack, Matrix.zero_apply]
    exact measurable_const

theorem integrable_lagDensity (G : HubGeometry d Ω) (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (r σ : ℝ) (c : ReactionZero.Coord n (d * n)) :
    Integrable (fun x ↦ lagDensity G g r σ x c) (endpointRef g) := by
  rcases c with ⟨i, j⟩ | ⟨i, c⟩ | ⟨i, j⟩
  · simp only [lagDensity, ReactionZero.pack, Matrix.smul_apply, smul_eq_mul]
    exact (integrable_endpointDensity_entry g i j).const_mul r
  · simp only [lagDensity, ReactionZero.pack, Matrix.smul_apply, smul_eq_mul,
      mul_velocityMatrix_apply]
    obtain ⟨C, hC⟩ := hubVel_bounded G ((col d n).symm c).1
    refine Integrable.const_mul ?_ σ
    exact (integrable_endpointDensity_entry g _ _).bdd_mul
      (f := fun x ↦ hubVel G x ((col d n).symm c).1) (c := C)
      (continuous_hubVel G _).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)
  · simp only [lagDensity, ReactionZero.pack, Matrix.zero_apply]
    exact integrable_zero _ _ _

theorem integrable_comp_snd {μ : Measure ↥Ω} [IsFiniteMeasure μ] {f : ↥Ω → ℝ}
    (hf : Integrable f μ) : Integrable (fun p : UnitI × ↥Ω ↦ f p.2) (unitTime.prod μ) := by
  exact hf.comp_snd unitTime

/-- The source reference measure `ds ⊗ λ`. -/
def lagRef (g : (Fin n × Fin n) → SignedMeasure ↥Ω) : Measure (UnitI × ↥Ω) :=
  unitTime.prod (endpointRef g)

instance lagRef_isFiniteMeasure (g : (Fin n × Fin n) → SignedMeasure ↥Ω) :
    IsFiniteMeasure (lagRef g) := by
  unfold lagRef
  infer_instance

/-- The Lagrangian piece: a genuine pushforward of an actual density path. -/
def lagPath (G : HubGeometry d Ω) (g : (Fin n × Fin n) → SignedMeasure ↥Ω) (a σ r : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + σ * r ∈ Icc (0 : ℝ) 1) :
    ReactionZero.Coord n (d * n) → SignedMeasure (Q Ω) :=
  pushPath (charMap G a (σ * r) ha hab)
    (fun c ↦ (lagRef g).withDensityᵥ (fun p ↦ lagDensity G g r σ p.2 c))

theorem lagPath_massSymmetric (G : HubGeometry d Ω) {g : (Fin n × Fin n) → SignedMeasure ↥Ω}
    (hg : EndpointPositiveSemidefinite g) (a σ r : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + σ * r ∈ Icc (0 : ℝ) 1) : ReactionZero.MassSymmetric (lagPath G g a σ r ha hab) := by
  intro i j
  have hfun : (fun p : UnitI × ↥Ω ↦ lagDensity G g r σ p.2 (Sum.inl (i, j))) =
      fun p ↦ lagDensity G g r σ p.2 (Sum.inl (j, i)) := by
    funext p
    simp only [lagDensity, ReactionZero.pack, Matrix.smul_apply, smul_eq_mul]
    rw [endpointDensity_symm hg]
  unfold lagPath pushPath
  simp only
  rw [hfun]

/-! ### The pairing with every original jet -/

/-- The jet value along a characteristic. -/
def charValue (G : HubGeometry d Ω) (φ : ClosedC1Jet Ω n) (a b : ℝ) (x : ↥Ω) (s : ℝ) : RMat n :=
  zeroExtend φ.value (charPoint G a b s x.val)

/-- Its derivative given by the jet partials. -/
def charDeriv (G : HubGeometry d Ω) (φ : ClosedC1Jet Ω n) (a b : ℝ) (x : ↥Ω) (s : ℝ) : RMat n :=
  b • zeroExtend φ.dt (charPoint G a b s x.val) +
    ∑ ℓ, hubVel G x ℓ • zeroExtend (φ.dx ℓ) (charPoint G a b s x.val)

theorem hasDerivAt_charValue (G : HubGeometry d Ω) (φ : ClosedC1Jet Ω n) {a σ r : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + σ * r ∈ Icc (0 : ℝ) 1) (hσ : σ = 1 ∨ σ = -1)
    (hr : 0 < r) (x : ↥Ω) {s0 : ℝ} (hs0 : s0 ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (charValue G φ a (σ * r) x) (charDeriv G φ a (σ * r) x s0) s0 := by
  have hp := charPoint_mem_interior G ha hab hσ hr hs0 x.property
  have h := jet_hasDerivAt_affine φ hp ((σ * r, G.hub - x.val) : Ambient d) s0
  have hfun : (fun s : ℝ ↦ zeroExtend φ.value (charPoint G a (σ * r) s0 x.val +
      (s - s0) • ((σ * r, G.hub - x.val) : Ambient d))) = charValue G φ a (σ * r) x := by
    funext s
    unfold charValue
    rw [← charPoint_affine]
  rw [hfun] at h
  exact h

theorem continuousOn_charValue (G : HubGeometry d Ω) (φ : ClosedC1Jet Ω n) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + b ∈ Icc (0 : ℝ) 1) (x : ↥Ω) :
    ContinuousOn (charValue G φ a b x) (Icc 0 1) :=
  (continuousOn_zeroExtend φ.value).comp (continuous_charPoint G a b x.val).continuousOn
    fun s hs ↦ charPoint_mem_domain G ha hab hs x.property

theorem continuousOn_charDeriv (G : HubGeometry d Ω) (φ : ClosedC1Jet Ω n) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + b ∈ Icc (0 : ℝ) 1) (x : ↥Ω) :
    ContinuousOn (charDeriv G φ a b x) (Icc 0 1) := by
  have hmaps : MapsTo (fun s ↦ charPoint G a b s x.val) (Icc 0 1) (domain Ω) :=
    fun s hs ↦ charPoint_mem_domain G ha hab hs x.property
  have hdt := ((continuousOn_zeroExtend φ.dt).comp
    (continuous_charPoint G a b x.val).continuousOn hmaps).const_smul b
  have hdx : ContinuousOn (fun s ↦ ∑ ℓ, hubVel G x ℓ •
      zeroExtend (φ.dx ℓ) (charPoint G a b s x.val)) (Icc 0 1) :=
    continuousOn_finset_sum _ fun ℓ _ ↦ ((continuousOn_zeroExtend (φ.dx ℓ)).comp
      (continuous_charPoint G a b x.val).continuousOn hmaps).const_smul (hubVel G x ℓ)
  exact hdt.add hdx

/-- Fundamental theorem of calculus along one characteristic, against the endpoint density. -/
theorem integral_charDeriv (G : HubGeometry d Ω) (φ : ClosedC1Jet Ω n) {a σ r : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + σ * r ∈ Icc (0 : ℝ) 1) (hσ : σ = 1 ∨ σ = -1)
    (hr : 0 < r) (x : ↥Ω) (M : RMat n) :
    ∫ s in (0 : ℝ)..1, ReactionZero.frob (charDeriv G φ a (σ * r) x s) M =
      ReactionZero.frob (zeroExtend φ.value (a + σ * r, G.hub)) M -
        ReactionZero.frob (zeroExtend φ.value (a, x.val)) M := by
  have hcont : ContinuousOn (fun s ↦ ReactionZero.frob (charValue G φ a (σ * r) x s) M) (Icc 0 1) :=
    (continuous_frob_left M).comp_continuousOn (continuousOn_charValue G φ ha hab x)
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun s ↦ ReactionZero.frob (charValue G φ a (σ * r) x s) M)
      (ReactionZero.frob (charDeriv G φ a (σ * r) x s) M) s := fun s hs ↦
    HasDerivAt.frob_const (hasDerivAt_charValue G φ ha hab hσ hr x hs) M
  have hint : IntervalIntegrable (fun s ↦ ReactionZero.frob (charDeriv G φ a (σ * r) x s) M)
      volume 0 1 :=
    ((continuous_frob_left M).comp_continuousOn
      (continuousOn_charDeriv G φ ha hab x)).intervalIntegrable_of_Icc zero_le_one
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  simp only [charValue, charPoint_one, charPoint_zero]

/-- Pointwise identity: the original pairing integrand is `σ` times the characteristic
derivative. -/
theorem weightedPair_lag (G : HubGeometry d Ω) (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (φ : ClosedC1Jet Ω n) {a σ r : ℝ} (hσ : σ ^ 2 = 1) (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + σ * r ∈ Icc (0 : ℝ) 1) (p : UnitI × ↥Ω) :
    weightedPair (fun _ ↦ 1) (testField (entrywiseDivergence d n) φ (charMap G a (σ * r) ha hab p))
        (lagDensity G g r σ p.2) =
      σ * ReactionZero.frob (charDeriv G φ a (σ * r) p.2 p.1.val) (endpointDensity g p.2) := by
  have hval : ∀ v : C(Q Ω, RMat n),
      v (charMap G a (σ * r) ha hab p) = zeroExtend v (charPoint G a (σ * r) p.1.val p.2.val) :=
    fun v ↦ (zeroExtend_val v _).symm
  simp only [testField, ContinuousMap.coe_mk, lagDensity, ReactionZero.weightedPair_pack_left,
    ReactionZero.mass_pack, ReactionZero.flux_pack, ReactionZero.reaction_pack,
    entrywiseDivergence_apply, ReactionZero.frob_smul_right, frob_blocks_velocity, frob_zero_right,
    add_zero]
  unfold charDeriv
  rw [frob_add_left, frob_sum_left, ReactionZero.frob_smul_left, hval φ.dt]
  simp only [ReactionZero.frob_smul_left, hval]
  have hσ' : σ * (σ * r) = r := by
    have : σ * σ = 1 := by rw [← sq]; exact hσ
    calc σ * (σ * r) = (σ * σ) * r := by ring
      _ = r := by rw [this, one_mul]
  rw [mul_add, ← mul_assoc, hσ']

theorem integrable_lagIntegrand (G : HubGeometry d Ω) (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (r σ : ℝ) {Θ : UnitI × ↥Ω → Q Ω} (hΘ : Continuous Θ)
    (b : C(Q Ω, ReactionZero.Coord n (d * n) → ℝ)) :
    Integrable (fun p ↦ weightedPair (fun _ ↦ 1) (b (Θ p)) (lagDensity G g r σ p.2)) (lagRef g) := by
  unfold weightedPair
  refine integrable_finsetSum _ fun c _ ↦ ?_
  obtain ⟨C, hC⟩ := ReactionZero.Duality.continuousField_coordinate_bounded b c
  have hz : Integrable (fun p : UnitI × ↥Ω ↦ lagDensity G g r σ p.2 c) (lagRef g) :=
    integrable_comp_snd (integrable_lagDensity G g r σ c)
  simpa only [one_mul] using hz.bdd_mul (f := fun p ↦ b (Θ p) c) (c := C)
    ((continuous_apply c).comp (b.continuous.comp hΘ)).aestronglyMeasurable
    (ae_of_all _ fun p ↦ by rw [Real.norm_eq_abs]; exact hC (Θ p))

/-- The ORIGINAL pairing of the Lagrangian piece with every original closed-domain jet. -/
theorem lagPiece_coordinatePair (G : HubGeometry d Ω) {g : (Fin n × Fin n) → SignedMeasure ↥Ω}
    (hg : EndpointPositiveSemidefinite g) {a σ r : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hab : a + σ * r ∈ Icc (0 : ℝ) 1) (hσ : σ = 1 ∨ σ = -1) (hr : 0 < r)
    (φ : ClosedC1Jet Ω n) :
    ReactionZero.Duality.coordinatePair (fun _ ↦ 1) (lagPath G g a σ r ha hab)
        (testField (entrywiseDivergence d n) φ) =
      σ * (ReactionZero.frob (zeroExtend φ.value (a + σ * r, G.hub)) (totalMatrix g) -
        endpointPair g φ a ha) := by
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hzM : ∀ c, Measurable (fun p : UnitI × ↥Ω ↦ lagDensity G g r σ p.2 c) :=
    fun c ↦ (measurable_lagDensity G g r σ c).comp measurable_snd
  have hzI : ∀ c, Integrable (fun p : UnitI × ↥Ω ↦ lagDensity G g r σ p.2 c) (lagRef g) :=
    fun c ↦ integrable_comp_snd (integrable_lagDensity G g r σ c)
  unfold lagPath
  rw [coordinatePair_pushDensity (lagRef g) (fun c p ↦ lagDensity G g r σ p.2 c) hzM hzI
    (continuous_charMap G a (σ * r) ha hab)]
  have hpt : (fun p : UnitI × ↥Ω ↦ weightedPair (fun _ ↦ 1)
      (testField (entrywiseDivergence d n) φ (charMap G a (σ * r) ha hab p))
        (fun c ↦ lagDensity G g r σ p.2 c)) =
      fun p ↦ σ * ReactionZero.frob (charDeriv G φ a (σ * r) p.2 p.1.val) (endpointDensity g p.2) :=
    funext fun p ↦ weightedPair_lag G g φ hσ2 ha hab p
  have hintegrand : Integrable (fun p : UnitI × ↥Ω ↦
      σ * ReactionZero.frob (charDeriv G φ a (σ * r) p.2 p.1.val) (endpointDensity g p.2))
      (lagRef g) := by
    rw [← hpt]
    exact integrable_lagIntegrand G g r σ (continuous_charMap G a (σ * r) ha hab) _
  rw [hpt]
  unfold lagRef at hintegrand ⊢
  rw [integral_prod_symm _ hintegrand]
  have hinner : ∀ x : ↥Ω, ∫ s : UnitI, σ * ReactionZero.frob (charDeriv G φ a (σ * r) x s.val)
      (endpointDensity g x) ∂unitTime =
      σ * (ReactionZero.frob (zeroExtend φ.value (a + σ * r, G.hub)) (endpointDensity g x) -
        ReactionZero.frob (zeroExtend φ.value (a, x.val)) (endpointDensity g x)) := by
    intro x
    rw [integral_const_mul,
      integral_unitTime (fun s ↦ ReactionZero.frob (charDeriv G φ a (σ * r) x s) (endpointDensity g x)),
      integral_charDeriv G φ ha hab hσ hr x]
  simp_rw [hinner]
  have hbnd : ∀ x : ↥Ω, zeroExtend φ.value (a, x.val) = φ.value (timeBoundary a ha x) :=
    fun x ↦ zeroExtend_of_mem φ.value _
  have hint1 : Integrable (fun x ↦ ReactionZero.frob (zeroExtend φ.value (a + σ * r, G.hub))
      (endpointDensity g x)) (endpointRef g) := by
    unfold ReactionZero.frob
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (integrable_endpointDensity_entry g i j).const_mul _
  have hint0 : Integrable (fun x ↦ ReactionZero.frob (zeroExtend φ.value (a, x.val))
      (endpointDensity g x)) (endpointRef g) := by
    have h0 : (fun x ↦ ReactionZero.frob (zeroExtend φ.value (a, x.val)) (endpointDensity g x)) =
        fun x ↦ ReactionZero.frob (φ.value (timeBoundary a ha x)) (endpointDensity g x) :=
      funext fun x ↦ by rw [hbnd]
    rw [h0]
    unfold ReactionZero.frob
    refine integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ?_
    let f : C(↥Ω, ℝ) := ⟨fun x ↦ φ.value (timeBoundary a ha x) i j,
      (continuous_apply j).comp ((continuous_apply i).comp
        (φ.value.continuous.comp (timeBoundary a ha).continuous))⟩
    exact (integrable_endpointDensity_entry g i j).bdd_mul (f := f) (c := ‖f‖)
      f.continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ f.norm_coe_le_norm x)
  rw [integral_const_mul, integral_sub hint1 hint0, integral_frob_endpointDensity,
    endpointPair_eq_integral g φ a ha]
  congr 2
  exact integral_congr_ae (ae_of_all _ fun x ↦ by dsimp only; rw [hbnd])

/-! ### Action bound -/

theorem lagPiece_action_le (R : PSDSqrt n) (G : HubGeometry d Ω)
    {g : (Fin n × Fin n) → SignedMeasure ↥Ω} (hg : EndpointPositiveSemidefinite g)
    {a σ r t : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hab : a + σ * r ∈ Icc (0 : ℝ) 1)
    (hσ : σ ^ 2 = 1) (hr : 0 < r) (ht : 0 < t) (H : RMat n) :
    ReactionZero.action (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H
        (lagPath G g a σ r ha hab) ≤
      ENNReal.ofReal (hubMoment g G.hub / (2 * t ^ 2 * r)) := by
  have hzM : ∀ c, Measurable (fun p : UnitI × ↥Ω ↦ lagDensity G g r σ p.2 c) :=
    fun c ↦ (measurable_lagDensity G g r σ c).comp measurable_snd
  have hzI : ∀ c, Integrable (fun p : UnitI × ↥Ω ↦ lagDensity G g r σ p.2 c) (lagRef g) :=
    fun c ↦ integrable_comp_snd (integrable_lagDensity G g r σ c)
  have h1 := action_pushDensity_le (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H (lagRef g)
    (fun c p ↦ lagDensity G g r σ p.2 c) hzM hzI (continuous_charMap G a (σ * r) ha hab)
  refine h1.trans ?_
  set h : ↥Ω → ℝ := fun x ↦ ‖(x : Space d) - G.hub‖ ^ 2 * (endpointDensity g x).trace /
    (2 * t ^ 2 * r) with hhdef
  have hpt : ∀ᵐ p ∂(lagRef g), ReactionZero.cost (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H
      (fun c ↦ lagDensity G g r σ p.2 c) ≤ ENNReal.ofReal (h p.2) := by
    have hae := (Measure.quasiMeasurePreserving_snd (μ := unitTime) (ν := endpointRef g)).ae
      (ae_endpointDensity_posSemidef hg)
    unfold lagRef
    filter_upwards [hae] with p hp
    have hc := cost_contraction_le R H hp (hubVel G p.2) hr ht hσ
    rw [sum_hubVel_sq] at hc
    have heq : (fun c ↦ lagDensity G g r σ p.2 c) = lagDensity G g r σ p.2 := rfl
    rw [heq]
    exact hc
  have hmono := lintegral_mono_ae hpt
  refine hmono.trans ?_
  have hhM : Measurable h := by
    rw [hhdef]
    exact (((hubDistSq (Ω := Ω) G.hub).continuous.measurable.mul
      (Finset.measurable_sum _ fun i _ ↦ measurable_endpointDensity_entry g i i)).div_const _)
  have hprod : ∫⁻ p, ENNReal.ofReal (h p.2) ∂(lagRef g) =
      ∫⁻ x, ENNReal.ofReal (h x) ∂endpointRef g := by
    unfold lagRef
    erw [lintegral_prod _ ((ENNReal.measurable_ofReal.comp (hhM.comp measurable_snd)).aemeasurable)]
    simp [unitTime_univ]
  rw [hprod]
  have hh0 : 0 ≤ᵐ[endpointRef g] h := by
    filter_upwards [ae_endpointDensity_posSemidef hg] with x hx
    rw [hhdef]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hx.trace_nonneg) (by positivity)
  have hhI : Integrable h (endpointRef g) := by
    rw [hhdef]
    refine Integrable.div_const ?_ _
    have hfun : (fun x : ↥Ω ↦ ‖(x : Space d) - G.hub‖ ^ 2 * (endpointDensity g x).trace) =
        fun x : ↥Ω ↦ ∑ i, ‖(x : Space d) - G.hub‖ ^ 2 * endpointDensity g x i i := by
      funext x
      simp only [Matrix.trace, Matrix.diag, Finset.mul_sum]
    rw [hfun]
    refine integrable_finsetSum _ fun i _ ↦ ?_
    obtain ⟨C, hC⟩ := hubDistSq_bounded (Ω := Ω) G.hub
    exact (integrable_endpointDensity_entry g i i).bdd_mul (f := hubDistSq (Ω := Ω) G.hub) (c := C)
      (hubDistSq (Ω := Ω) G.hub).continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)
  rw [← ofReal_integral_eq_lintegral_ofReal hhI hh0]
  apply le_of_eq
  congr 1
  rw [hhdef, integral_div, ← hubMoment_eq_integral]

#print axioms lagPiece_coordinatePair
#print axioms lagPiece_action_le

end MatrixTransport.EntrywiseBures
