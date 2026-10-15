import MatrixTransport.Paper.HubLimit
import MatrixTransport.Paper.GeneralUniformReaction
import MatrixTransport.TransportInfinity.UniformLimit
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.Regular

/-! Guarded operator, square-completion, and regularized Bures identities used in the paper. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace LiZouTransport.GenericBridges
open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain
open MatrixTransport.ReactionZero.Limit MatrixTransport.EntrywiseBures
open LiZouTransport.Reaction LiZouTransport.HubLimit

theorem closure_isCompact_of_bounded {d : ℕ} {U : Set (Space d)}
    (hU : Bornology.IsBounded U) : IsCompact (closure U) := hU.isCompact_closure

theorem closure_open_setup {d : ℕ} {U : Set (Space d)}
    (ho : IsOpen U) (hb : Bornology.IsBounded U) :
    IsCompact (closure U) ∧ closure U ⊆ closure (interior (closure U)) :=
  ⟨closure_isCompact_of_bounded hb, LiZouTransport.RegularReaction.closure_open_regular ho⟩

/-- Finite signed coordinates on a compact metric Borel domain have regular variation. -/
theorem signed_totalVariation_regular {X : Type*} [MeasurableSpace X] [MetricSpace X]
    [CompactSpace X] [BorelSpace X] (μ : SignedMeasure X) : μ.totalVariation.Regular :=
  inferInstance

/-- Only the forward implication is needed; it also covers an empty spatial domain. -/
theorem operator_annihilates_spatial_constants {d n k : ℕ} {Ω : Set (Space d)}
    (D : AdjointOperator d n k)
    (hD0 : ∀ A : Mat n, A.IsHermitian → D.D0 A = 0)
    (φ : ClosedC1Jet Ω n) (hx : ∀ j p, φ.dx j p = 0) (p : Q Ω) :
    D.apply φ p = 0 := by
  simp [AdjointOperator.apply, hD0 _ (φ.value_symmetric p), hx]

theorem factorMassDeriv_eq_sym {n : ℕ} {H : RMat n} (hH : Hᵀ = H)
    (P Δ : RMat n) (s : ℝ) :
    factorMassDeriv H P Δ s =
      (1 / 2 : ℝ) • (factorRate H P Δ s + (factorRate H P Δ s)ᵀ) := by
  simp only [factorMassDeriv, factorRate, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hH, Matrix.mul_assoc, smul_add, smul_smul]
  norm_num
  exact add_comm _ _

theorem factorPoint_transformed {n : ℕ} (H P Δ : RMat n) (s : ℝ) :
    factorPoint (H * P) (H * Δ) s = H * factorPoint P Δ s := by
  simp only [factorPoint, Matrix.mul_add, Matrix.mul_smul]

theorem factorMass_transformed {n : ℕ} {H : RMat n} (hH : Hᵀ = H)
    (P Δ : RMat n) (s : ℝ) :
    factorMass H (H * P) Δ s = H * factorPoint P Δ s * (factorPoint P Δ s)ᵀ * H := by
  simp only [factorMass, factorPoint_transformed, gram, Matrix.transpose_mul, hH,
    Matrix.mul_assoc]

theorem factorRate_transformed {n : ℕ} (H P Δ : RMat n) (s : ℝ) :
    factorRate H (H * P) Δ s = (2 : ℝ) • (H * factorPoint P Δ s * Δᵀ * H) := by
  rw [factorRate, factorPoint_transformed]

theorem frobeniusSq_factor_eq_trace {n : ℕ} (P Y : RMat n) (hP : P * Pᵀ = Y) :
    frobeniusSq P = Y.trace := by rw [frobeniusSq_eq_trace, hP]

theorem abs_apply_le_half_diag_of_posSemidef {n : ℕ} {G : RMat n}
    (hG : G.PosSemidef) (i j : Fin n) :
    |G i j| ≤ (G i i + G j j) / 2 ∧ (G i i + G j j) / 2 ≤ G.trace := by
  have hT : Gᵀ = G := transpose_eq_of_posSemidef hG
  have hs : G j i = G i j := congrFun (congrFun hT i) j
  have h1 := dotProduct_mulVec_nonneg_of_posSemidef hG (twoPoint i j 1)
  have h2 := dotProduct_mulVec_nonneg_of_posSemidef hG (twoPoint i j (-1))
  rw [dotProduct_twoPoint, hs] at h1 h2
  constructor
  · rw [abs_le]
    constructor <;> nlinarith
  · have hi := diag_le_trace hG i
    have hj := diag_le_trace hG j
    linarith

/-- The actual Bures reaction pairing, with the symmetric reaction-weight guard. -/
theorem reaction_pair_le_completedSquare {n k : ℕ}
    (L : Matrix (Fin k) (Fin k) ℝ) {H : RMat n} (hH : Hᵀ = H)
    (W Δ : RMat n) (a : Coord n k → ℝ) (ha : a ∈ dualSet L H) :
    frob (mass a) (gram W) + frob (reaction a) ((2 : ℝ) • (W * Δᵀ * H)) ≤
      -(1 / 2 : ℝ) * frob (Wᵀ * (reaction a * H)) (Wᵀ * (reaction a * H)) +
        2 * frob (Wᵀ * (reaction a * H)) Δᵀ ∧
    -(1 / 2 : ℝ) * frob (Wᵀ * (reaction a * H)) (Wᵀ * (reaction a * H)) +
        2 * frob (Wᵀ * (reaction a * H)) Δᵀ ≤ 2 * frobeniusSq Δ := by
  have hslack := frob_gram_nonneg ha.2 W
  rw [frob_comm, pw_frob_sub_left, pw_frob_sub_left, frob_neg_left,
    frob_smul_left, frob_smul_left, frob_gram_reaction] at hslack
  have hB := frob_gram_nonneg (posSemidef_gram W) (flux a * L)
  constructor
  · rw [frob_smul_right, frob_reaction_cross hH]
    linarith
  · have h := frob_cross_le (Wᵀ * (reaction a * H)) Δᵀ (by norm_num : (0 : ℝ) < 1)
    rw [frob_transpose_self] at h
    norm_num at h
    linarith

theorem frob_transpose_pair {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) : frob Aᵀ Bᵀ = frob A B := by
  unfold frob
  rw [Finset.sum_comm]
  rfl

/-- The same completion in the paper's literal orientation Y=(CH)ᵀW. -/
theorem reaction_pair_le_completedSquare_original {n k : ℕ}
    (L : Matrix (Fin k) (Fin k) ℝ) {H : RMat n} (hH : Hᵀ = H)
    (W Δ : RMat n) (a : Coord n k → ℝ) (ha : a ∈ dualSet L H) :
    let Y := (reaction a * H)ᵀ * W
    frob (mass a) (gram W) + frob (reaction a) ((2 : ℝ) • (W * Δᵀ * H)) ≤
      -(1 / 2 : ℝ) * frob Y Y + 2 * frob Y Δ ∧
      -(1 / 2 : ℝ) * frob Y Y + 2 * frob Y Δ ≤ 2 * frobeniusSq Δ := by
  dsimp only
  let Y := (reaction a * H)ᵀ * W
  have he : Wᵀ * (reaction a * H) = Yᵀ := by simp [Y]
  have h := reaction_pair_le_completedSquare L hH W Δ a ha
  rw [he, frob_transpose_pair, frob_transpose_pair] at h
  exact h

theorem regMap_posDef {n : ℕ} (R : PSDSqrt n) {X0 X1 : RMat n}
    (hX0 : X0.PosSemidef) (hX1 : X1.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    (regMap R X0 X1 δ).PosDef :=
  (regMap_posSemidef R hX0 hX1 hδ.le).posDef_iff_det_ne_zero.mpr
    (det_regMap_ne_zero R hX0 hX1 hδ)

/-- The transport square completion before the support supremum is taken. -/
theorem contraction_pair_le_completedSquare {d n : ℕ} (R : PSDSqrt n) (H : RMat n)
    {M : RMat n} (hM : M.PosSemidef) (v : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    (a : Coord n (d * n) → ℝ)
    (ha : a ∈ dualSet (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H) :
    frob (mass a) M + frob (flux a) (M * velocityMatrix v) ≤
      -(t ^ 2 / 2) * frob (gram (flux a)) M +
        frob (flux a) (M * velocityMatrix v) ∧
    -(t ^ 2 / 2) * frob (gram (flux a)) M +
        frob (flux a) (M * velocityMatrix v) ≤
      (∑ ℓ, v ℓ ^ 2) * M.trace / (2 * t ^ 2) := by
  have hslack := frob_nonneg_of_posSemidef R ha.2 hM
  have hgB : gram (flux a * (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ))) =
      t ^ 2 • gram (flux a) := by
    rw [Matrix.mul_smul, Matrix.mul_one, gram_smul]
  rw [pw_frob_sub_left, pw_frob_sub_left, frob_neg_left, frob_smul_left,
    frob_smul_left, hgB, frob_smul_left] at hslack
  have hq := frob_gram_nonneg hM (reaction a * H)
  constructor
  · nlinarith
  · have hs := frob_gram_nonneg hM
      ((t ^ 2) • flux a - velocityMatrix (n := n) v)
    have hMt : Mᵀ = M := transpose_eq_of_posSemidef hM
    have he : (t ^ 2) • flux a - velocityMatrix (n := n) v =
        (t ^ 2) • flux a - (1 : ℝ) • velocityMatrix (n := n) v := by simp
    rw [he, frob_gram_sub_expand M hMt, velocity_gram, frob_smul_left,
      pw_frob_one_left] at hs
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t ^ 2)).mpr
    apply sub_nonpos.mp
    have hid : (-(t ^ 2 / 2) * frob (gram (flux a)) M +
        frob (flux a) (M * velocityMatrix v)) * (2 * t ^ 2) -
        (∑ ℓ, v ℓ ^ 2) * M.trace =
        -((t ^ 2) ^ 2 * frob (gram (flux a)) M -
          2 * t ^ 2 * 1 * frob (flux a) (M * velocityMatrix v) +
          1 ^ 2 * ((∑ ℓ, v ℓ ^ 2) * M.trace)) := by ring
    rw [hid]
    exact neg_nonpos.mpr hs

/-- The Gram contraction quadratic is exactly the Frobenius square in the factor frame. -/
theorem frob_gram_factor_frame {n k : ℕ} (S : RMat n)
    (B : Matrix (Fin n) (Fin k) ℝ) :
    frob (gram B) (gram S) = frob (Sᵀ * B) (Sᵀ * B) := by
  rw [frob_gram_eq_trace, frob_eq_trace]
  simp only [gram, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem frob_cross_factor_frame {n k : ℕ} (S : RMat n)
    (B V : Matrix (Fin n) (Fin k) ℝ) :
    frob B (gram S * V) = frob (Sᵀ * B) (Sᵀ * V) := by
  rw [frob_eq_trace, frob_eq_trace]
  simp only [gram, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem gram_blockSum {d n : ℕ} (B : Fin d → RMat n) :
    gram (∑ ℓ, blockPlace d n ℓ (B ℓ)) = ∑ ℓ, gram (B ℓ) := by
  ext i j
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, blockSum_apply]
  rw [← (col d n).sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [Matrix.sum_apply]
  rfl

theorem frob_sum_left {ι m n : ℕ} (A : Fin ι → Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) : frob (∑ i, A i) B = ∑ i, frob (A i) B := by
  simp_rw [frob_eq_trace, Matrix.transpose_sum, Matrix.sum_mul, Matrix.trace_sum]

theorem frob_factor_cross {n : ℕ} (S B : RMat n) :
    frob B (gram S) = frob S (Bᵀ * S) := by
  rw [frob_eq_trace, frob_eq_trace]
  change (Bᵀ * (S * Sᵀ)).trace = (Sᵀ * (Bᵀ * S)).trace
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]

/-- The literal blockwise transport square-completion display. -/
theorem contraction_pair_le_completedSquare_blocks {d n : ℕ} (R : PSDSqrt n)
    (H A C S : RMat n) (B : Fin d → RMat n) (v : Fin d → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : pack A (∑ ℓ, blockPlace d n ℓ (B ℓ)) C ∈
      dualSet (t • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ)) H) :
    frob A (gram S) + ∑ ℓ, frob (B ℓ) (v ℓ • gram S) ≤
      ∑ ℓ, (-(t ^ 2 / 2) * frob ((B ℓ)ᵀ * S) ((B ℓ)ᵀ * S) +
        v ℓ * frob S ((B ℓ)ᵀ * S)) ∧
    (∑ ℓ, (-(t ^ 2 / 2) * frob ((B ℓ)ᵀ * S) ((B ℓ)ᵀ * S) +
        v ℓ * frob S ((B ℓ)ᵀ * S))) ≤
      (∑ ℓ, v ℓ ^ 2) * (gram S).trace / (2 * t ^ 2) := by
  have h := contraction_pair_le_completedSquare R H (posSemidef_gram S) v ht
    (pack A (∑ ℓ, blockPlace d n ℓ (B ℓ)) C) ha
  simp only [mass_pack, flux_pack] at h
  erw [frob_blocks_velocity, gram_blockSum, frob_sum_left] at h
  have he (ℓ : Fin d) : frob (gram (B ℓ)) (gram S) =
      frob ((B ℓ)ᵀ * S) ((B ℓ)ᵀ * S) := by
    rw [frob_gram_factor_frame]
    have het : Sᵀ * B ℓ = ((B ℓ)ᵀ * S)ᵀ := by simp
    rw [het, frob_transpose_pair]
  simp_rw [he, frob_factor_cross] at h
  simp_rw [frob_smul_right]
  simpa only [Finset.mul_sum, Finset.sum_add_distrib, frob_factor_cross] using h

def regularizedCrossTrace {n : ℕ} (R : PSDSqrt n) (X0 X1 : RMat n) (δ : ℝ) : ℝ :=
  (R.sqrt (R.sqrt (X0 + δ • (1 : RMat n)) * (X1 + δ • (1 : RMat n)) *
    R.sqrt (X0 + δ • (1 : RMat n)))).trace

theorem trace_regMap_X0 {n : ℕ} (R : PSDSqrt n) {X0 X1 : RMat n}
    (hX0 : X0.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    (regMap R X0 X1 δ * X0).trace =
      regularizedCrossTrace R X0 X1 δ - δ * (regMap R X0 X1 δ).trace := by
  have h := trace_regMap_mul R (Y := X1) hX0 hδ
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul] at h
  change _ = _ - _
  exact eq_sub_iff_add_eq.mpr h

theorem trace_regMap_inv_X1 {n : ℕ} (R : PSDSqrt n) {X0 X1 : RMat n}
    (hX0 : X0.PosSemidef) (hX1 : X1.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    ((regMap R X0 X1 δ)⁻¹ * X1).trace =
      regularizedCrossTrace R X0 X1 δ - δ * ((regMap R X0 X1 δ)⁻¹).trace := by
  let T := regMap R X0 X1 δ
  have hTu : IsUnit T.det := isUnit_iff_ne_zero.mpr (det_regMap_ne_zero R hX0 hX1 hδ)
  have hpush := regMap_push R hX0 hX1 hδ
  have e1 : (T⁻¹ * (X1 + δ • (1 : RMat n))).trace =
      (T⁻¹ * X1).trace + δ * (T⁻¹).trace := by
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, smul_eq_mul]
  have e2 : (T⁻¹ * (X1 + δ • (1 : RMat n))).trace =
      (T * (X0 + δ • (1 : RMat n))).trace := by
    rw [← hpush]
    calc
      (T⁻¹ * (T * (X0 + δ • (1 : RMat n)) * T)).trace =
          ((T⁻¹ * T) * (X0 + δ • (1 : RMat n)) * T).trace := by
            simp only [Matrix.mul_assoc]
      _ = ((X0 + δ • (1 : RMat n)) * T).trace := by
        rw [Matrix.nonsing_inv_mul T hTu, Matrix.one_mul]
      _ = (T * (X0 + δ • (1 : RMat n))).trace := Matrix.trace_mul_comm _ _
  have htr := trace_regMap_mul R (Y := X1) hX0 hδ
  change (T * (X0 + δ • (1 : RMat n))).trace = regularizedCrossTrace R X0 X1 δ at htr
  change (T⁻¹ * X1).trace = _ - δ * (T⁻¹).trace
  linarith

theorem riccati_endpoint_pairing_eq {n : ℕ} (R : PSDSqrt n) {X0 X1 : RMat n}
    (hX0 : X0.PosSemidef) (hX1 : X1.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    frob (ricPsi (regMap R X0 X1 δ) 1) X1 -
      frob (ricPsi (regMap R X0 X1 δ) 0) X0 =
      2 * (X0.trace + X1.trace - 2 * regularizedCrossTrace R X0 X1 δ) +
        2 * δ * ((regMap R X0 X1 δ).trace + ((regMap R X0 X1 δ)⁻¹).trace) := by
  let T := regMap R X0 X1 δ
  have hTu : IsUnit T.det := isUnit_iff_ne_zero.mpr (det_regMap_ne_zero R hX0 hX1 hδ)
  have hTt : Tᵀ = T := regMap_transpose R hX0 hX1 hδ.le
  have hTit : (T⁻¹)ᵀ = T⁻¹ := transpose_inv_of_symm hTt
  have h1 : frob (ricPsi T 1) X1 = 2 * (X1.trace - (T⁻¹ * X1).trace) := by
    rw [ricPsi_one hTu, frob_smul_left, pw_frob_sub_left, pw_frob_one_left,
      frob_eq_trace T⁻¹, hTit]
  have h0 : frob (ricPsi T 0) X0 = 2 * ((T * X0).trace - X0.trace) := by
    rw [ricPsi_zero, frob_smul_left, pw_frob_sub_left, pw_frob_one_left,
      frob_eq_trace T, hTt]
  change frob (ricPsi T 1) X1 - frob (ricPsi T 0) X0 = _
  rw [h1, h0]
  have hA := trace_regMap_inv_X1 R hX0 hX1 hδ
  have hB := trace_regMap_X0 R (X1 := X1) hX0 hδ
  change (T⁻¹ * X1).trace = _ - δ * (T⁻¹).trace at hA
  change (T * X0).trace = _ - δ * T.trace at hB
  rw [hA, hB]
  ring

theorem uniform_divergence_bures_limit {d n : ℕ} {Ω : Set (Space d)}
    [Fact (IsCompact Ω)] (R : PSDSqrt n) (G : HubGeometry d Ω)
    (P : Problem Ω n (d * n)) (hD : P.operator = entrywiseDivergence d n)
    {H : RMat n} (hH : Hᵀ = H) (hHu : IsUnit H.det)
    (L : ℕ → Matrix (Fin (d * n)) (Fin (d * n)) ℝ) (t : ℕ → ℝ)
    (ht : Tendsto t atTop atTop)
    (hL : ∀ᶠ j in atTop, (gram (L j) - gram
      (t j • (1 : Matrix (Fin (d * n)) (Fin (d * n)) ℝ))).PosSemidef) :
    Tendsto (fun j ↦ minimumValue P (L j) H) atTop
      (𝓝 (ENNReal.ofReal (endpointEnergy R P H))) := by
  have h := MatrixTransport.TransportInfinity.uniform_transport_infinity_regime P L H t ht hL
  rwa [freeTransportValue_eq_endpointEnergy R G P hD hH hHu] at h

end LiZouTransport.GenericBridges

#print axioms LiZouTransport.GenericBridges.closure_isCompact_of_bounded
#print axioms LiZouTransport.GenericBridges.closure_open_setup
#print axioms LiZouTransport.GenericBridges.signed_totalVariation_regular
#print axioms LiZouTransport.GenericBridges.operator_annihilates_spatial_constants
#print axioms LiZouTransport.GenericBridges.factorMassDeriv_eq_sym
#print axioms LiZouTransport.GenericBridges.factorPoint_transformed
#print axioms LiZouTransport.GenericBridges.factorMass_transformed
#print axioms LiZouTransport.GenericBridges.factorRate_transformed
#print axioms LiZouTransport.GenericBridges.frobeniusSq_factor_eq_trace
#print axioms LiZouTransport.GenericBridges.abs_apply_le_half_diag_of_posSemidef
#print axioms LiZouTransport.GenericBridges.reaction_pair_le_completedSquare
#print axioms LiZouTransport.GenericBridges.frob_transpose_pair
#print axioms LiZouTransport.GenericBridges.reaction_pair_le_completedSquare_original
#print axioms LiZouTransport.GenericBridges.regMap_posDef
#print axioms LiZouTransport.GenericBridges.contraction_pair_le_completedSquare
#print axioms LiZouTransport.GenericBridges.frob_gram_factor_frame
#print axioms LiZouTransport.GenericBridges.frob_cross_factor_frame
#print axioms LiZouTransport.GenericBridges.gram_blockSum
#print axioms LiZouTransport.GenericBridges.frob_sum_left
#print axioms LiZouTransport.GenericBridges.frob_factor_cross
#print axioms LiZouTransport.GenericBridges.contraction_pair_le_completedSquare_blocks
#print axioms LiZouTransport.GenericBridges.trace_regMap_X0
#print axioms LiZouTransport.GenericBridges.trace_regMap_inv_X1
#print axioms LiZouTransport.GenericBridges.riccati_endpoint_pairing_eq
#print axioms LiZouTransport.GenericBridges.uniform_divergence_bures_limit
