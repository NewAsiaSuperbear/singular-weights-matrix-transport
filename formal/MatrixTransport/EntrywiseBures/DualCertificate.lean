import MatrixTransport.ReactionZero.LimitTheorem
import MatrixTransport.EntrywiseBures.Partials
import MatrixTransport.EntrywiseBures.PathOperations
import MatrixTransport.EntrywiseBures.BuresAlgebra

/-!
# Lower bound for every signed Radon competitor via a spatially constant Riccati test

The pure-reaction lower bound follows from the Fenchel inequality and the signed-measure
continuity equation `PaperContinuityEquation`. The test is a spatially constant closed-domain
jet `Φ(s)` satisfying the Riccati equation `Φ' + ½ Φ H² Φ = 0`. Its spatial derivatives vanish,
and the operator's zero-order part vanishes on symmetric matrices, so the bound holds at every
transport weight. The explicit Riccati field yields an endpoint estimate in terms of
regularized Bures expressions. Their limit as the regularization vanishes gives the bound for
arbitrary positive semidefinite endpoints, including singular matrices. The construction and
lower bound apply to every signed Radon competitor in the original `Good` class.

* `TimeField.jet`: every time-`C¹` symmetric field is an ORIGINAL `ClosedC1Jet`.
* `action_ge_of_timeField`: for any original problem whose operator has no zero-order part on
  symmetric matrices, every `Good` path has `action ≥ ⟨Φ(1), A₁⟩ - ⟨Φ(0), A₀⟩` for every
  admissible field, at EVERY transport weight.
* `ricField`: the explicit admissible field `Φ = H⁻¹ 2 (T - I)((1-s)I + sT)⁻¹ H⁻¹`.
* `buresValue_le_action`: `2 d_BW²(H⁻¹A₀H⁻¹, H⁻¹A₁H⁻¹) ≤ action` for every `Good` path, all PSD
  endpoints (singular allowed), via regularization `δ ↓ 0`.

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix Matrix.Norms.Elementwise

namespace MatrixTransport.EntrywiseBures

open MatrixTransport.ReactionZero.ClosedDomain
open MatrixTransport.ReactionZero.Limit (Problem Path Good minimumValue)

/-! ### Spatially constant jets -/

/-- A time-dependent symmetric matrix field with a derivative on `(0,1)` and continuous
extensions on `[0,1]`. -/
structure TimeField (n : ℕ) where
  Φ : ℝ → RMat n
  Φ' : ℝ → RMat n
  contΦ : ContinuousOn Φ (Icc 0 1)
  contΦ' : ContinuousOn Φ' (Icc 0 1)
  deriv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ (Φ' s) s
  sym : ∀ s ∈ Icc (0 : ℝ) 1, (Φ s).IsHermitian
  sym' : ∀ s ∈ Icc (0 : ℝ) 1, (Φ' s).IsHermitian

variable {d n k : ℕ} {Ω : Set (Space d)}

theorem time_mem_Icc (p : Q Ω) : p.val.1 ∈ Icc (0 : ℝ) 1 := p.property.1

theorem interior_domain_eq : interior (domain Ω) = Ioo (0 : ℝ) 1 ×ˢ interior Ω := by
  unfold domain
  rw [interior_prod_eq, interior_Icc]

theorem time_mem_Ioo_of_interior {p : Ambient d} (hp : p ∈ interior (domain Ω)) :
    p.1 ∈ Ioo (0 : ℝ) 1 := by
  rw [interior_domain_eq] at hp
  exact hp.1

/-- The field as an ORIGINAL closed-domain jet, constant in space. -/
def TimeField.jet (F : TimeField n) : ClosedC1Jet Ω n :=
  ClosedC1Jet.ofAmbient (fun p ↦ F.Φ p.1)
    ⟨fun p ↦ F.Φ p.val.1, F.contΦ.comp_continuous
      (continuous_fst.comp continuous_subtype_val) time_mem_Icc⟩
    ⟨fun p ↦ F.Φ' p.val.1, F.contΦ'.comp_continuous
      (continuous_fst.comp continuous_subtype_val) time_mem_Icc⟩
    (fun _ ↦ ContinuousMap.const _ 0)
    (fun _ ↦ rfl)
    (fun p ↦ F.sym _ (time_mem_Icc p))
    (fun p ↦ F.sym' _ (time_mem_Icc p))
    (fun _ _ ↦ Matrix.isHermitian_zero)
    (fun p hp ↦ by
      have hs := time_mem_Ioo_of_interior hp
      have h1 : HasDerivAt (fun s : ℝ ↦ p.val.1 + s) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add p.val.1
      have h2 : HasDerivAt F.Φ (F.Φ' p.val.1) ((fun s : ℝ ↦ p.val.1 + s) 0) := by
        simpa using F.deriv _ hs
      have h3 : HasDerivAt (F.Φ ∘ fun s : ℝ ↦ p.val.1 + s) ((1 : ℝ) • F.Φ' p.val.1) 0 := by
        first
          | exact h2.scomp 0 h1
          | exact HasDerivAt.scomp 0 h2 h1
      rw [one_smul] at h3
      exact h3)
    (fun p j _ ↦ hasDerivAt_const (0 : ℝ) (F.Φ p.val.1))

@[simp] theorem TimeField.jet_value (F : TimeField n) (p : Q Ω) :
    (F.jet (Ω := Ω)).value p = F.Φ p.val.1 := rfl

@[simp] theorem TimeField.jet_dt (F : TimeField n) (p : Q Ω) :
    (F.jet (Ω := Ω)).dt p = F.Φ' p.val.1 := rfl

@[simp] theorem TimeField.jet_dx (F : TimeField n) (j : Fin d) (p : Q Ω) :
    (F.jet (Ω := Ω)).dx j p = 0 := rfl

/-- The total matrix `G(Ω)` of an endpoint coordinate family. -/
def totalMatrix (g : (Fin n × Fin n) → SignedMeasure ↥Ω) : RMat n :=
  fun i j ↦ g (i, j) univ

theorem totalMatrix_posSemidef {g : (Fin n × Fin n) → SignedMeasure ↥Ω}
    (hg : EndpointPositiveSemidefinite g) : (totalMatrix g).PosSemidef :=
  hg univ MeasurableSet.univ

theorem endpointPair_timeField (F : TimeField n) (g : (Fin n × Fin n) → SignedMeasure ↥Ω)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    endpointPair g (F.jet (Ω := Ω)) t ht = ReactionZero.frob (F.Φ t) (totalMatrix g) := by
  unfold endpointPair ReactionZero.frob totalMatrix
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  exact signedPair_const (g (i, j)) (F.Φ t i j)

theorem testField_timeField (D : AdjointOperator d n k)
    (hD0 : ∀ A : RMat n, A.IsHermitian → D.D0 A = 0) (F : TimeField n) (p : Q Ω) :
    testField D (F.jet (Ω := Ω)) p = ReactionZero.pack (F.Φ' p.val.1) 0 (F.Φ p.val.1) := by
  have happ : D.apply (F.jet (Ω := Ω)) p = 0 := by
    simp only [AdjointOperator.apply, ContinuousMap.coe_mk, TimeField.jet_value,
      TimeField.jet_dx, map_zero, Finset.sum_const_zero, add_zero]
    exact hD0 _ (F.sym _ (time_mem_Icc p))
  simp only [testField, ContinuousMap.coe_mk, happ, TimeField.jet_value, TimeField.jet_dt]

variable [Fact (IsCompact Ω)]

/-- The ORIGINAL Fenchel/CE lower bound with a spatially constant admissible field.  It holds
for every signed Radon competitor in the original `Good` class and every transport weight. -/
theorem action_ge_of_timeField (P : Problem Ω n k)
    (hD0 : ∀ A : RMat n, A.IsHermitian → P.operator.D0 A = 0)
    (L : Matrix (Fin k) (Fin k) ℝ) (H : RMat n) (F : TimeField n)
    (hadm : ∀ s ∈ Icc (0 : ℝ) 1,
      (-(F.Φ' s) - (1 / 2 : ℝ) • ReactionZero.gram (F.Φ s * H)).PosSemidef)
    (μ : Path Ω n k) (hμ : Good P μ) :
    ENNReal.ofReal (ReactionZero.frob (F.Φ 1) (totalMatrix P.terminal) -
        ReactionZero.frob (F.Φ 0) (totalMatrix P.initial)) ≤ ReactionZero.action L H μ := by
  have hCE := hμ.2 (F.jet (Ω := Ω))
  change ReactionZero.Duality.coordinatePair (fun _ ↦ 1) μ (testField P.operator F.jet) =
    endpointPair P.terminal F.jet 1 ⟨zero_le_one, le_rfl⟩ -
      endpointPair P.initial F.jet 0 ⟨le_rfl, zero_le_one⟩ at hCE
  erw [endpointPair_timeField, endpointPair_timeField] at hCE
  rw [← hCE]
  have hmem : ∀ p, testField P.operator (F.jet (Ω := Ω)) p ∈ ReactionZero.dualSet L H := by
    intro p
    rw [testField_timeField P.operator hD0 F p]
    refine ⟨F.sym' _ (time_mem_Icc p), ?_⟩
    have h0 : ReactionZero.gram ((0 : Matrix (Fin n) (Fin k) ℝ) * L) = 0 := by
      simp [ReactionZero.gram]
    show (-(F.Φ' p.val.1) - (1 / 2 : ℝ) • ReactionZero.gram ((0 : Matrix (Fin n) (Fin k) ℝ) * L) -
      (1 / 2 : ℝ) • ReactionZero.gram (F.Φ p.val.1 * H)).PosSemidef
    rw [h0, smul_zero, sub_zero]
    exact hadm _ (time_mem_Icc p)
  exact ReactionZero.Duality.coordinatePair_le_integratedSupport (fun _ ↦ 1)
    (ReactionZero.dualSet L H) μ (testField P.operator F.jet)
    (fun i ↦ (ReactionZero.Duality.coordinateTest (testField P.operator (F.jet (Ω := Ω))) i).continuous.measurable)
    (ReactionZero.Duality.continuousField_coordinate_bounded _) hmem

/-! ### The Riccati solution -/

section Riccati

variable {n : ℕ}

/-- `N(s) = (1 - s) I + s T`. -/
def interpMat (T : RMat n) (s : ℝ) : RMat n := (1 - s) • (1 : RMat n) + s • T

theorem interpMat_zero (T : RMat n) : interpMat T 0 = 1 := by simp [interpMat]

theorem interpMat_one (T : RMat n) : interpMat T 1 = T := by simp [interpMat]

theorem interpMat_sub (T : RMat n) (r s : ℝ) :
    interpMat T r - interpMat T s = (r - s) • (T - 1) := by
  unfold interpMat
  module

theorem continuous_interpMat (T : RMat n) : Continuous (interpMat T) := by
  unfold interpMat
  exact ((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)

theorem interpMat_transpose {T : RMat n} (hT : Tᵀ = T) (s : ℝ) :
    (interpMat T s)ᵀ = interpMat T s := by
  unfold interpMat
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one, hT]

theorem interpMat_comm (T : RMat n) (s : ℝ) :
    interpMat T s * (T - 1) = (T - 1) * interpMat T s := by
  have hT : T * (T - 1) = (T - 1) * T := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  unfold interpMat
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hT]

theorem inv_comm_of_comm {N X : RMat n} (hN : IsUnit N.det) (hc : N * X = X * N) :
    N⁻¹ * X = X * N⁻¹ := by
  calc N⁻¹ * X = N⁻¹ * X * (N * N⁻¹) := by rw [Matrix.mul_nonsing_inv N hN, Matrix.mul_one]
    _ = N⁻¹ * (X * N) * N⁻¹ := by simp only [Matrix.mul_assoc]
    _ = N⁻¹ * (N * X) * N⁻¹ := by rw [hc]
    _ = N⁻¹ * N * X * N⁻¹ := by simp only [Matrix.mul_assoc]
    _ = X * N⁻¹ := by rw [Matrix.nonsing_inv_mul N hN, Matrix.one_mul]

theorem continuousAt_inv_interpMat (T : RMat n) {s : ℝ} (hs : IsUnit (interpMat T s).det) :
    ContinuousAt (fun r ↦ (interpMat T r)⁻¹) s := by
  have hne : (interpMat T s).det ≠ 0 := isUnit_iff_ne_zero.mp hs
  have hinv : ContinuousAt (fun A : RMat n ↦ A⁻¹) (interpMat T s) := by
    first
      | exact continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hne)
      | exact continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hs.unit)
  exact hinv.comp (continuous_interpMat T).continuousAt

theorem hasDerivAt_inv_interpMat (T : RMat n) {s : ℝ} (hs : IsUnit (interpMat T s).det) :
    HasDerivAt (fun r ↦ (interpMat T r)⁻¹)
      (-((interpMat T s)⁻¹ * (T - 1) * (interpMat T s)⁻¹)) s := by
  have hcont := continuousAt_inv_interpMat T hs
  have hdet : ∀ᶠ r in 𝓝 s, IsUnit (interpMat T r).det := by
    have hc : ContinuousAt (fun r ↦ (interpMat T r).det) s :=
      ((continuous_interpMat T).matrix_det).continuousAt
    filter_upwards [hc.eventually_ne (isUnit_iff_ne_zero.mp hs)] with r hr
    exact isUnit_iff_ne_zero.mpr hr
  erw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun r ↦ -((interpMat T r)⁻¹ * (T - 1) * (interpMat T s)⁻¹)) (𝓝[≠] s)
      (𝓝 (-((interpMat T s)⁻¹ * (T - 1) * (interpMat T s)⁻¹))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    exact ((hcont.tendsto.mul tendsto_const_nhds).mul tendsto_const_nhds).neg
  refine hlim.congr' ?_
  have hev : ∀ᶠ r in 𝓝[≠] s, IsUnit (interpMat T r).det ∧ r ∈ ({s}ᶜ : Set ℝ) :=
    (hdet.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  filter_upwards [hev] with r hr
  obtain ⟨hru, hrs⟩ := hr
  have hrs' : r ≠ s := hrs
  rw [slope_def_module]
  have h1 : (interpMat T r)⁻¹ * (interpMat T s - interpMat T r) * (interpMat T s)⁻¹ =
      (interpMat T r)⁻¹ - (interpMat T s)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hs,
      Matrix.mul_one, Matrix.nonsing_inv_mul _ hru, Matrix.one_mul]
  have hne : r - s ≠ 0 := sub_ne_zero.mpr hrs'
  have hcoef : (r - s)⁻¹ * (s - r) = -1 := by
    rw [show s - r = -(r - s) by ring, mul_neg, inv_mul_cancel₀ hne]
  rw [← h1, interpMat_sub, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hcoef, neg_one_smul]

theorem det_interpMat_ne_zero {T : RMat n} (hT : T.PosSemidef) (hdet : T.det ≠ 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : (interpMat T s).det ≠ 0 := by
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · rw [h1, interpMat_one]
    exact hdet
  · intro h0
    obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hq : v ⬝ᵥ (interpMat T s *ᵥ v) = (1 - s) * (v ⬝ᵥ v) + s * (v ⬝ᵥ (T *ᵥ v)) := by
      unfold interpMat
      rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [hzero, dotProduct_zero] at hq
    have hT1 : 0 ≤ v ⬝ᵥ (T *ᵥ v) := by
      simpa only [star_trivial] using hT.dotProduct_mulVec_nonneg v
    have hpos := mul_pos (sub_pos.mpr h1) (dotProduct_self_pos hv)
    have hs2 := mul_nonneg hs.1 hT1
    linarith

/-- Riccati potential in congruence coordinates, `Ψ(s) = 2 (T - I) N(s)⁻¹`. -/
def ricPsi (T : RMat n) (s : ℝ) : RMat n := (2 : ℝ) • ((T - 1) * (interpMat T s)⁻¹)

def ricPsi' (T : RMat n) (s : ℝ) : RMat n :=
  (2 : ℝ) • ((T - 1) * (-((interpMat T s)⁻¹ * (T - 1) * (interpMat T s)⁻¹)))

theorem hasDerivAt_ricPsi (T : RMat n) {s : ℝ} (hs : IsUnit (interpMat T s).det) :
    HasDerivAt (ricPsi T) (ricPsi' T s) s :=
  (HasDerivAt.const_matrix_mul (hasDerivAt_inv_interpMat T hs) (T - 1)).const_smul (2 : ℝ)

theorem continuousAt_ricPsi' (T : RMat n) {s : ℝ} (hs : IsUnit (interpMat T s).det) :
    ContinuousAt (ricPsi' T) s := by
  have hc := continuousAt_inv_interpMat T hs
  exact (continuousAt_const.mul ((hc.mul continuousAt_const).mul hc).neg).const_smul (2 : ℝ)

theorem ricPsi'_eq (T : RMat n) (s : ℝ) :
    ricPsi' T s = (-(1 / 2 : ℝ)) • (ricPsi T s * ricPsi T s) := by
  unfold ricPsi ricPsi'
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_neg, smul_neg,
    Matrix.mul_assoc]
  module

theorem ricPsi_transpose {T : RMat n} (hT : Tᵀ = T) {s : ℝ} (hs : IsUnit (interpMat T s).det) :
    (ricPsi T s)ᵀ = ricPsi T s := by
  have hNt := interpMat_transpose hT s
  have hcomm := inv_comm_of_comm hs (interpMat_comm T s)
  unfold ricPsi
  rw [Matrix.transpose_smul, Matrix.transpose_mul, transpose_inv_of_symm hNt,
    Matrix.transpose_sub, Matrix.transpose_one, hT, hcomm]

/-- The field in the original coordinates, `Φ = H⁻¹ Ψ H⁻¹`. -/
def ricPhi (H T : RMat n) (s : ℝ) : RMat n := H⁻¹ * ricPsi T s * H⁻¹

def ricPhi' (H T : RMat n) (s : ℝ) : RMat n := H⁻¹ * ricPsi' T s * H⁻¹

theorem ricPhi_transpose {H T : RMat n} (hHt : Hᵀ = H) (hT : Tᵀ = T) {s : ℝ}
    (hs : IsUnit (interpMat T s).det) : (ricPhi H T s)ᵀ = ricPhi H T s := by
  unfold ricPhi
  rw [Matrix.transpose_mul, Matrix.transpose_mul, transpose_inv_of_symm hHt,
    ricPsi_transpose hT hs, Matrix.mul_assoc]

theorem ricPhi_admissible {H T : RMat n} (hHt : Hᵀ = H) (hHu : IsUnit H.det) (hT : Tᵀ = T)
    {s : ℝ} (hs : IsUnit (interpMat T s).det) :
    -(ricPhi' H T s) - (1 / 2 : ℝ) • ReactionZero.gram (ricPhi H T s * H) = 0 := by
  have hΦt := ricPhi_transpose hHt hT hs
  have h1 : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hHu
  have h2 : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hHu
  have hgram : ReactionZero.gram (ricPhi H T s * H) =
      H⁻¹ * (ricPsi T s * ricPsi T s) * H⁻¹ := by
    unfold ReactionZero.gram
    rw [Matrix.transpose_mul, hΦt, hHt]
    unfold ricPhi
    calc H⁻¹ * ricPsi T s * H⁻¹ * H * (H * (H⁻¹ * ricPsi T s * H⁻¹))
        = H⁻¹ * ricPsi T s * (H⁻¹ * H) * (H * H⁻¹) * ricPsi T s * H⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = H⁻¹ * (ricPsi T s * ricPsi T s) * H⁻¹ := by
          rw [h1, h2]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hgram]
  unfold ricPhi'
  rw [ricPsi'_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  module

theorem frob_congr_left {K : RMat n} (hK : Kᵀ = K) (Ψ A : RMat n) :
    ReactionZero.frob (K * Ψ * K) A = ReactionZero.frob Ψ (K * A * K) := by
  rw [ReactionZero.frob_eq_trace, ReactionZero.frob_eq_trace, Matrix.transpose_mul,
    Matrix.transpose_mul, hK]
  rw [show K * (Ψᵀ * K) * A = K * (Ψᵀ * K * A) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm K]
  simp only [Matrix.mul_assoc]

/-- The admissible Riccati field for an invertible PSD symmetric `T`. -/
def ricField (H T : RMat n) (hHt : Hᵀ = H) (hHu : IsUnit H.det) (hTp : T.PosSemidef)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) : TimeField n where
  Φ := ricPhi H T
  Φ' := ricPhi' H T
  contΦ := fun s hs ↦ by
    have hd := hasDerivAt_ricPsi T
      (isUnit_iff_ne_zero.mpr (det_interpMat_ne_zero hTp hdet hs))
    exact (HasDerivAt.matrix_mul_const (HasDerivAt.const_matrix_mul hd H⁻¹) H⁻¹).continuousAt.continuousWithinAt
  contΦ' := fun s hs ↦
    ((continuousAt_const.mul (continuousAt_ricPsi' T
      (isUnit_iff_ne_zero.mpr (det_interpMat_ne_zero hTp hdet hs)))).mul
        continuousAt_const).continuousWithinAt
  deriv := fun s hs ↦ by
    have hd := hasDerivAt_ricPsi T
      (isUnit_iff_ne_zero.mpr (det_interpMat_ne_zero hTp hdet (Ioo_subset_Icc_self hs)))
    exact HasDerivAt.matrix_mul_const (HasDerivAt.const_matrix_mul hd H⁻¹) H⁻¹
  sym := fun s hs ↦ by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact ricPhi_transpose hHt hT (isUnit_iff_ne_zero.mpr (det_interpMat_ne_zero hTp hdet hs))
  sym' := fun s hs ↦ by
    have hs' := isUnit_iff_ne_zero.mpr (det_interpMat_ne_zero hTp hdet hs)
    have h := ricPhi_admissible hHt hHu hT hs'
    rw [sub_eq_zero, neg_eq_iff_eq_neg] at h
    rw [h]
    exact (((ReactionZero.posSemidef_gram (ricPhi H T s * H)).isHermitian).smul
      (by rfl : IsSelfAdjoint (1 / 2 : ℝ))).neg

theorem ricField_admissible (H T : RMat n) (hHt : Hᵀ = H) (hHu : IsUnit H.det)
    (hTp : T.PosSemidef) (hT : Tᵀ = T) (hdet : T.det ≠ 0) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (-((ricField H T hHt hHu hTp hT hdet).Φ' s) - (1 / 2 : ℝ) •
      ReactionZero.gram ((ricField H T hHt hHu hTp hT hdet).Φ s * H)).PosSemidef := by
  have h := ricPhi_admissible hHt hHu hT
    (isUnit_iff_ne_zero.mpr (det_interpMat_ne_zero hTp hdet hs))
  change (-(ricPhi' H T s) - (1 / 2 : ℝ) • ReactionZero.gram (ricPhi H T s * H)).PosSemidef
  rw [h]
  exact Matrix.PosSemidef.zero

/-! ### Value of the regularized certificate -/

theorem ricPsi_zero (T : RMat n) : ricPsi T 0 = (2 : ℝ) • (T - 1) := by
  unfold ricPsi
  rw [interpMat_zero, inv_one, Matrix.mul_one]

theorem ricPsi_one {T : RMat n} (hTu : IsUnit T.det) : ricPsi T 1 = (2 : ℝ) • (1 - T⁻¹) := by
  unfold ricPsi
  rw [interpMat_one, Matrix.sub_mul, Matrix.mul_nonsing_inv T hTu, Matrix.one_mul]

/-- The certificate's endpoint value dominates the regularized Bures expression. -/
theorem riccati_value_ge (R : PSDSqrt n) {X0 X1 : RMat n} (hX0 : X0.PosSemidef)
    (hX1 : X1.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    2 * (X0.trace + X1.trace - 2 * (R.sqrt (R.sqrt (X0 + δ • (1 : RMat n)) *
        (X1 + δ • (1 : RMat n)) * R.sqrt (X0 + δ • (1 : RMat n)))).trace) ≤
      ReactionZero.frob (ricPsi (regMap R X0 X1 δ) 1) X1 -
        ReactionZero.frob (ricPsi (regMap R X0 X1 δ) 0) X0 := by
  set T := regMap R X0 X1 δ with hTdef
  have hTu : IsUnit T.det := isUnit_iff_ne_zero.mpr (det_regMap_ne_zero R hX0 hX1 hδ)
  have hTt : Tᵀ = T := regMap_transpose R hX0 hX1 hδ.le
  have hTp : T.PosSemidef := regMap_posSemidef R hX0 hX1 hδ.le
  have hTit : (T⁻¹)ᵀ = T⁻¹ := transpose_inv_of_symm hTt
  have hTip : (T⁻¹).PosSemidef := by
    have h := posSemidef_congr_symm hTit hTp
    rwa [Matrix.nonsing_inv_mul T hTu, Matrix.one_mul] at h
  have hpush : T * (X0 + δ • (1 : RMat n)) * T = X1 + δ • (1 : RMat n) :=
    regMap_push R hX0 hX1 hδ
  have htrF := trace_regMap_mul R (Y := X1) hX0 hδ
  rw [← hTdef] at htrF
  have hA : (T⁻¹ * X1).trace = (T * (X0 + δ • (1 : RMat n))).trace - δ * (T⁻¹).trace := by
    have e1 : (T⁻¹ * (X1 + δ • (1 : RMat n))).trace = (T⁻¹ * X1).trace + δ * (T⁻¹).trace := by
      rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
        smul_eq_mul]
    have e2 : (T⁻¹ * (X1 + δ • (1 : RMat n))).trace = (T * (X0 + δ • (1 : RMat n))).trace := by
      rw [← hpush]
      calc (T⁻¹ * (T * (X0 + δ • (1 : RMat n)) * T)).trace
          = ((T⁻¹ * T) * (X0 + δ • (1 : RMat n)) * T).trace := by simp only [Matrix.mul_assoc]
        _ = ((X0 + δ • (1 : RMat n)) * T).trace := by rw [Matrix.nonsing_inv_mul T hTu, Matrix.one_mul]
        _ = (T * (X0 + δ • (1 : RMat n))).trace := Matrix.trace_mul_comm _ _
    linarith
  have hB : (T * X0).trace = (T * (X0 + δ • (1 : RMat n))).trace - δ * T.trace := by
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
      smul_eq_mul]
    ring
  have h1 : ReactionZero.frob (ricPsi T 1) X1 = 2 * (X1.trace - (T⁻¹ * X1).trace) := by
    rw [ricPsi_one hTu, ReactionZero.frob_smul_left, ReactionZero.pw_frob_sub_left,
      ReactionZero.pw_frob_one_left, ReactionZero.frob_eq_trace T⁻¹, hTit]
  have h0 : ReactionZero.frob (ricPsi T 0) X0 = 2 * ((T * X0).trace - X0.trace) := by
    rw [ricPsi_zero, ReactionZero.frob_smul_left, ReactionZero.pw_frob_sub_left,
      ReactionZero.pw_frob_one_left, ReactionZero.frob_eq_trace T, hTt]
  rw [h1, h0, hA, hB, htrF]
  have hT0 := hTp.trace_nonneg
  have hT1 := hTip.trace_nonneg
  nlinarith [mul_nonneg hδ.le hT0, mul_nonneg hδ.le hT1]

/-! ### The Bures lower bound for every original competitor -/

/-- The weighted Bures target `E_H(A₀, A₁) = 2 d²_BW(H⁻¹A₀H⁻¹, H⁻¹A₁H⁻¹)`. -/
def buresValue (R : PSDSqrt n) (H A0 A1 : RMat n) : ℝ :=
  2 * buresSq R (H⁻¹ * A0 * H⁻¹) (H⁻¹ * A1 * H⁻¹)

end Riccati

theorem buresValue_le_action (R : PSDSqrt n) (P : Problem Ω n k)
    (hD0 : ∀ A : RMat n, A.IsHermitian → P.operator.D0 A = 0)
    {H : RMat n} (hHt : Hᵀ = H) (hHu : IsUnit H.det) (L : Matrix (Fin k) (Fin k) ℝ)
    (μ : Path Ω n k) (hμ : Good P μ) :
    ENNReal.ofReal (buresValue R H (totalMatrix P.initial) (totalMatrix P.terminal)) ≤
      ReactionZero.action L H μ := by
  set A0 := totalMatrix P.initial
  set A1 := totalMatrix P.terminal
  have hKt : (H⁻¹)ᵀ = H⁻¹ := transpose_inv_of_symm hHt
  have hX0 : (H⁻¹ * A0 * H⁻¹).PosSemidef :=
    posSemidef_congr_symm hKt (totalMatrix_posSemidef P.initial_positive)
  have hX1 : (H⁻¹ * A1 * H⁻¹).PosSemidef :=
    posSemidef_congr_symm hKt (totalMatrix_posSemidef P.terminal_positive)
  have hbound : ∀ j, ENNReal.ofReal (2 * ((H⁻¹ * A0 * H⁻¹).trace + (H⁻¹ * A1 * H⁻¹).trace -
      2 * (R.sqrt (R.sqrt (H⁻¹ * A0 * H⁻¹ + regSeq j • (1 : RMat n)) *
        (H⁻¹ * A1 * H⁻¹ + regSeq j • (1 : RMat n)) *
          R.sqrt (H⁻¹ * A0 * H⁻¹ + regSeq j • (1 : RMat n)))).trace)) ≤
        ReactionZero.action L H μ := by
    intro j
    have hδ := regSeq_pos j
    set T := regMap R (H⁻¹ * A0 * H⁻¹) (H⁻¹ * A1 * H⁻¹) (regSeq j) with hTdef
    have hTt : Tᵀ = T := regMap_transpose R hX0 hX1 hδ.le
    have hTp : T.PosSemidef := regMap_posSemidef R hX0 hX1 hδ.le
    have hdet : T.det ≠ 0 := det_regMap_ne_zero R hX0 hX1 hδ
    have hlow := action_ge_of_timeField P hD0 L H (ricField H T hHt hHu hTp hTt hdet)
      (ricField_admissible H T hHt hHu hTp hTt hdet) μ hμ
    have hval := riccati_value_ge R hX0 hX1 hδ
    rw [← hTdef] at hval
    have hc1 : ReactionZero.frob ((ricField H T hHt hHu hTp hTt hdet).Φ 1) A1 =
        ReactionZero.frob (ricPsi T 1) (H⁻¹ * A1 * H⁻¹) := frob_congr_left hKt _ _
    have hc0 : ReactionZero.frob ((ricField H T hHt hHu hTp hTt hdet).Φ 0) A0 =
        ReactionZero.frob (ricPsi T 0) (H⁻¹ * A0 * H⁻¹) := frob_congr_left hKt _ _
    rw [hc1, hc0] at hlow
    exact (ENNReal.ofReal_le_ofReal hval).trans hlow
  have hlim : Tendsto (fun j ↦ ENNReal.ofReal (2 * ((H⁻¹ * A0 * H⁻¹).trace +
      (H⁻¹ * A1 * H⁻¹).trace - 2 * (R.sqrt (R.sqrt (H⁻¹ * A0 * H⁻¹ + regSeq j • (1 : RMat n)) *
        (H⁻¹ * A1 * H⁻¹ + regSeq j • (1 : RMat n)) *
          R.sqrt (H⁻¹ * A0 * H⁻¹ + regSeq j • (1 : RMat n)))).trace))) atTop
      (𝓝 (ENNReal.ofReal (buresValue R H A0 A1))) :=
    ENNReal.tendsto_ofReal ((tendsto_reg_buresSq R hX0 hX1).const_mul 2)
  exact le_of_tendsto' hlim hbound

/-- The same lower bound for the infimum over the ORIGINAL `Good` class, at every transport
weight. -/
theorem buresValue_le_minimumValue (R : PSDSqrt n) (P : Problem Ω n k)
    (hD0 : ∀ A : RMat n, A.IsHermitian → P.operator.D0 A = 0)
    {H : RMat n} (hHt : Hᵀ = H) (hHu : IsUnit H.det) (L : Matrix (Fin k) (Fin k) ℝ) :
    ENNReal.ofReal (buresValue R H (totalMatrix P.initial) (totalMatrix P.terminal)) ≤
      minimumValue P L H := by
  unfold minimumValue ReactionZero.constrainedInfimum
  exact le_iInf fun μ ↦ le_iInf fun hμ ↦ buresValue_le_action R P hD0 hHt hHu L μ hμ

#print axioms action_ge_of_timeField
#print axioms ricPhi_admissible
#print axioms riccati_value_ge
#print axioms buresValue_le_action
#print axioms buresValue_le_minimumValue

end MatrixTransport.EntrywiseBures
