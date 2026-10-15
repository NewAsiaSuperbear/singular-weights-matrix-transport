import MatrixTransport.ReactionZero.MatrixPositivity
import MatrixTransport.EntrywiseBures.DualCertificate

/-!
# RN matrix density of an arbitrary PSD endpoint family

For the ORIGINAL endpoint data `g : (Fin n × Fin n) → SignedMeasure Ω` with
`EndpointPositiveSemidefinite g`, the canonical reference is the existing
`jointReference g`.  This file proves, without regularizing or discarding any singular part:

* every coordinate is the reference integral of its RN density;
* the density matrix is symmetric everywhere and PSD almost everywhere;
* the hub second moment, defined as a genuine Jordan pairing with the trace measure, equals
  the reference integral `∫ ‖x - x*‖² tr m(x) dλ`.

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace MatrixTransport.EntrywiseBures

open MatrixTransport.ReactionZero.ClosedDomain

variable {d n : ℕ} {Ω : Set (Space d)}

/-- The canonical finite reference of an endpoint family. -/
abbrev endpointRef (g : (Fin n × Fin n) → SignedMeasure ↥Ω) : Measure ↥Ω :=
  MatrixTransport.jointReference g

/-- The RN matrix density of an endpoint family against its canonical reference. -/
def endpointDensity (g : (Fin n × Fin n) → SignedMeasure ↥Ω) (x : ↥Ω) : RMat n :=
  fun i j ↦ (g (i, j)).rnDeriv (endpointRef g) x

theorem measurable_endpointDensity_entry (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (i j : Fin n) : Measurable (fun x ↦ endpointDensity g x i j) :=
  measurable_rnDeriv_jointReference g (i, j)

theorem integrable_endpointDensity_entry (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (i j : Fin n) : Integrable (fun x ↦ endpointDensity g x i j) (endpointRef g) :=
  integrable_rnDeriv_jointReference g (i, j)

theorem endpoint_apply_eq_setIntegral (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (i j : Fin n) (B : Set ↥Ω) (hB : MeasurableSet B) :
    g (i, j) B = ∫ x in B, endpointDensity g x i j ∂endpointRef g := by
  rw [← withDensityᵥ_rnDeriv_jointReference g (i, j),
    withDensityᵥ_apply (integrable_rnDeriv_jointReference g (i, j)) hB]
  rfl

theorem endpoint_univ_eq_integral (g : (Fin n × Fin n) → SignedMeasure ↥Ω) (i j : Fin n) :
    g (i, j) univ = ∫ x, endpointDensity g x i j ∂endpointRef g := by
  rw [endpoint_apply_eq_setIntegral g i j univ MeasurableSet.univ, Measure.restrict_univ]

theorem endpoint_symm {g : (Fin n × Fin n) → SignedMeasure ↥Ω}
    (hg : EndpointPositiveSemidefinite g) (i j : Fin n) : g (i, j) = g (j, i) := by
  apply VectorMeasure.ext
  intro B hB
  have h := (hg B hB).isHermitian.apply i j
  simp only [star_trivial] at h
  exact h.symm

theorem endpointDensity_symm {g : (Fin n × Fin n) → SignedMeasure ↥Ω}
    (hg : EndpointPositiveSemidefinite g) (x : ↥Ω) (i j : Fin n) :
    endpointDensity g x i j = endpointDensity g x j i := by
  unfold endpointDensity
  rw [endpoint_symm hg i j]

theorem endpointDensity_isHermitian {g : (Fin n × Fin n) → SignedMeasure ↥Ω}
    (hg : EndpointPositiveSemidefinite g) (x : ↥Ω) : (endpointDensity g x).IsHermitian :=
  Matrix.IsHermitian.ext fun i j ↦ by
    rw [star_trivial]
    exact endpointDensity_symm hg x j i

theorem endpointDensity_transpose {g : (Fin n × Fin n) → SignedMeasure ↥Ω}
    (hg : EndpointPositiveSemidefinite g) (x : ↥Ω) :
    (endpointDensity g x)ᵀ = endpointDensity g x :=
  transpose_eq_of_isHermitian (endpointDensity_isHermitian hg x)

/-- The RN density of a PSD endpoint family is PSD almost everywhere. -/
theorem ae_endpointDensity_posSemidef {g : (Fin n × Fin n) → SignedMeasure ↥Ω}
    (hg : EndpointPositiveSemidefinite g) :
    ∀ᵐ x ∂(endpointRef g), (endpointDensity g x).PosSemidef := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Fin n → ℝ)
  have hq : ∀ k : ℕ, ∀ᵐ x ∂(endpointRef g),
      0 ≤ u k ⬝ᵥ (endpointDensity g x *ᵥ u k) := by
    intro k
    have hint : Integrable (fun x ↦ u k ⬝ᵥ (endpointDensity g x *ᵥ u k)) (endpointRef g) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ?_
      exact ((integrable_endpointDensity_entry g i j).mul_const (u k j)).const_mul (u k i)
    refine ae_nonneg_of_forall_setIntegral_nonneg hint fun B hB _ ↦ ?_
    have hset := ReactionZero.MatrixPositivity.quadraticForm_setIntegral (endpointDensity g)
      (integrable_endpointDensity_entry g) B (u k)
    simp only [star_trivial] at hset
    rw [← hset]
    have hval : (fun i j ↦ ∫ x in B, endpointDensity g x i j ∂(endpointRef g)) =
        fun i j ↦ g (i, j) B := by
      funext i j
      exact (endpoint_apply_eq_setIntegral g i j B hB).symm
    rw [hval]
    simpa only [star_trivial] using (hg B hB).dotProduct_mulVec_nonneg (u k)
  filter_upwards [ae_all_iff.2 hq] with x hx
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (endpointDensity_isHermitian hg x)
    fun v ↦ ?_
  have hclosed : IsClosed {w : Fin n → ℝ | 0 ≤ w ⬝ᵥ (endpointDensity g x *ᵥ w)} :=
    isClosed_le continuous_const
      (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))
  have hv : 0 ≤ v ⬝ᵥ (endpointDensity g x *ᵥ v) := hu.induction_on v hclosed hx
  simpa only [star_trivial] using hv

/-! ### The hub second moment -/

/-- Second moment of the endpoint trace measure about `xstar`, as a genuine Jordan pairing. -/
def hubMoment (g : (Fin n × Fin n) → SignedMeasure ↥Ω) (xstar : Space d) : ℝ :=
  ∑ i, MatrixTransport.signedPair (g (i, i)) (fun x : ↥Ω ↦ ‖(x : Space d) - xstar‖ ^ 2)

/-- The squared distance to the hub as a continuous function on the domain. -/
def hubDistSq (xstar : Space d) : C(↥Ω, ℝ) :=
  ⟨fun x : ↥Ω ↦ ‖(x : Space d) - xstar‖ ^ 2,
    ((continuous_subtype_val.sub continuous_const).norm).pow 2⟩

variable [Fact (IsCompact Ω)]

instance endpointCompactSpace : CompactSpace ↥Ω :=
  isCompact_iff_compactSpace.mp (Fact.out : IsCompact Ω)

theorem hubDistSq_bounded (xstar : Space d) : ∃ C : ℝ, ∀ x : ↥Ω, |hubDistSq xstar x| ≤ C :=
  ⟨‖hubDistSq (Ω := Ω) xstar‖, fun x ↦ by
    simpa only [Real.norm_eq_abs] using (hubDistSq (Ω := Ω) xstar).norm_coe_le_norm x⟩

theorem hubMoment_eq_integral (g : (Fin n × Fin n) → SignedMeasure ↥Ω) (xstar : Space d) :
    hubMoment g xstar =
      ∫ x : ↥Ω, ‖(x : Space d) - xstar‖ ^ 2 * (endpointDensity g x).trace ∂endpointRef g := by
  have hterm : ∀ i, MatrixTransport.signedPair (g (i, i)) (fun x : ↥Ω ↦ ‖(x : Space d) - xstar‖ ^ 2) =
      ∫ x : ↥Ω, ‖(x : Space d) - xstar‖ ^ 2 * endpointDensity g x i i ∂endpointRef g := fun i ↦
    MatrixTransport.signedPair_rnDeriv (endpointRef g) (g (i, i))
      (absolutelyContinuous_jointReference g (i, i)) (hubDistSq (Ω := Ω) xstar).continuous.measurable
      (hubDistSq_bounded xstar)
  have hint : ∀ i, Integrable (fun x : ↥Ω ↦ ‖(x : Space d) - xstar‖ ^ 2 * endpointDensity g x i i)
      (endpointRef g) := fun i ↦ by
    obtain ⟨C, hC⟩ := hubDistSq_bounded (Ω := Ω) xstar
    exact (integrable_endpointDensity_entry g i i).bdd_mul (f := hubDistSq (Ω := Ω) xstar) (c := C)
      (hubDistSq (Ω := Ω) xstar).continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)
  unfold hubMoment
  simp_rw [hterm]
  rw [← integral_finsetSum Finset.univ fun i _ ↦ hint i]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum]

theorem integral_frob_endpointDensity (g : (Fin n × Fin n) → SignedMeasure ↥Ω) (K : RMat n) :
    ∫ x, ReactionZero.frob K (endpointDensity g x) ∂endpointRef g =
      ReactionZero.frob K (totalMatrix g) := by
  have hint : ∀ i j, Integrable (fun x ↦ K i j * endpointDensity g x i j) (endpointRef g) :=
    fun i j ↦ (integrable_endpointDensity_entry g i j).const_mul (K i j)
  unfold ReactionZero.frob totalMatrix
  rw [integral_finsetSum Finset.univ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum Finset.univ fun j _ ↦ hint i j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_const_mul, endpoint_univ_eq_integral]

/-- Pairing of a continuous symmetric field at a fixed time with the endpoint, through its RN
density: this is exactly the ORIGINAL `endpointPair`. -/
theorem endpointPair_eq_integral (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (φ : ClosedC1Jet Ω n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    endpointPair g φ t ht =
      ∫ x, ReactionZero.frob (φ.value (timeBoundary t ht x)) (endpointDensity g x)
        ∂endpointRef g := by
  have hcont : ∀ i j, Continuous fun x ↦ φ.value (timeBoundary t ht x) i j := fun i j ↦
    (continuous_apply j).comp ((continuous_apply i).comp
      (φ.value.continuous.comp (timeBoundary t ht).continuous))
  have hbd : ∀ i j, ∃ C : ℝ, ∀ x, |φ.value (timeBoundary t ht x) i j| ≤ C := fun i j ↦ by
    let f : C(↥Ω, ℝ) := ⟨fun x ↦ φ.value (timeBoundary t ht x) i j, hcont i j⟩
    exact ⟨‖f‖, fun x ↦ by simpa only [Real.norm_eq_abs, f, ContinuousMap.coe_mk] using f.norm_coe_le_norm x⟩
  have hint : ∀ i j, Integrable
      (fun x ↦ φ.value (timeBoundary t ht x) i j * endpointDensity g x i j) (endpointRef g) :=
    fun i j ↦ by
      obtain ⟨C, hC⟩ := hbd i j
      exact (integrable_endpointDensity_entry g i j).bdd_mul
        (f := fun x ↦ φ.value (timeBoundary t ht x) i j) (c := C)
        (hcont i j).aestronglyMeasurable (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)
  unfold endpointPair ReactionZero.frob
  rw [integral_finsetSum Finset.univ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum Finset.univ fun j _ ↦ hint i j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact MatrixTransport.signedPair_rnDeriv (endpointRef g) (g (i, j))
    (absolutelyContinuous_jointReference g (i, j)) (hcont i j).measurable (hbd i j)

#print axioms ae_endpointDensity_posSemidef
#print axioms hubMoment_eq_integral
#print axioms integral_frob_endpointDensity
#print axioms endpointPair_eq_integral

end MatrixTransport.EntrywiseBures
