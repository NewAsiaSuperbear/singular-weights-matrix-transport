import MatrixTransport.ReactionZero.ClosedDomainTests

/-!
# Directional derivatives of closed-domain `C¹` jets

`ClosedDomain.ClosedC1Jet` (the ORIGINAL test class of `PaperContinuityEquation`) only records
partial derivatives along the time line and the coordinate space lines at interior points,
with continuous extensions to the closed domain.  The hub construction needs the chain rule
along characteristics `s ↦ (a + b s, (1 - s) x + s x*)`, which move in time and space
simultaneously.  This file proves the classical fact that continuous partial derivatives give
every directional derivative, by a telescoping mean-value argument, and specializes it to
jets.  No smoothness of an ambient extension is assumed.

-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set Asymptotics
open scoped BigOperators Matrix.Norms.Elementwise

namespace MatrixTransport.EntrywiseBures

theorem abs_le_abs_of_mem_uIcc_zero {θ b : ℝ} (h : θ ∈ uIcc (0 : ℝ) b) : |θ| ≤ |b| := by
  rcases Set.mem_uIcc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
    linarith

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A derivative at `0` along the line through `q + θ e` is the derivative at `θ` along the
line through `q`. -/
theorem hasDerivAt_line_shift (f : E → F) (q e : E) (D : F) (θ : ℝ)
    (h : HasDerivAt (fun s : ℝ ↦ f ((q + θ • e) + s • e)) D 0) :
    HasDerivAt (fun s : ℝ ↦ f (q + s • e)) D θ := by
  have h2 : HasDerivAt (fun s : ℝ ↦ s - θ) 1 θ := by
    simpa using (hasDerivAt_id θ).sub_const θ
  have h1 : HasDerivAt (fun s : ℝ ↦ f ((q + θ • e) + s • e)) D ((fun s : ℝ ↦ s - θ) θ) := by
    simpa using h
  have h3 : HasDerivAt ((fun s : ℝ ↦ f ((q + θ • e) + s • e)) ∘ fun s : ℝ ↦ s - θ)
      ((1 : ℝ) • D) θ := by
    first
      | exact h1.scomp θ h2
      | exact HasDerivAt.scomp θ h1 h2
  have h4 : ((fun s : ℝ ↦ f ((q + θ • e) + s • e)) ∘ fun s : ℝ ↦ s - θ) =
      fun s ↦ f (q + s • e) := by
    funext s
    simp only [Function.comp]
    congr 1
    module
  rw [h4, one_smul] at h3
  exact h3

/-- One mean-value step along a fixed direction. -/
theorem norm_step_le (f : E → F) (U : Set E) (e : E) (D : E → F)
    (hD : ∀ q ∈ U, HasDerivAt (fun s : ℝ ↦ f (q + s • e)) (D q) 0)
    (q : E) (u : ℝ) (hseg : ∀ θ ∈ uIcc (0 : ℝ) u, q + θ • e ∈ U) (D0 : F) (ε : ℝ)
    (hε : ∀ θ ∈ uIcc (0 : ℝ) u, ‖D (q + θ • e) - D0‖ ≤ ε) :
    ‖f (q + u • e) - f q - u • D0‖ ≤ ε * |u| := by
  let g : ℝ → F := fun θ ↦ f (q + θ • e) - θ • D0
  have hg : ∀ θ ∈ uIcc (0 : ℝ) u,
      HasDerivWithinAt g (D (q + θ • e) - D0) (uIcc 0 u) θ := by
    intro θ hθ
    have h1 : HasDerivAt (fun s : ℝ ↦ f (q + s • e)) (D (q + θ • e)) θ :=
      hasDerivAt_line_shift f q e _ θ (hD _ (hseg θ hθ))
    have h5 : HasDerivAt (fun s : ℝ ↦ s • D0) D0 θ := by
      simpa using (hasDerivAt_id θ).smul_const D0
    exact (h1.sub h5).hasDerivWithinAt
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hε (convex_uIcc 0 u)
    left_mem_uIcc right_mem_uIcc
  have hgu : g u - g 0 = f (q + u • e) - f q - u • D0 := by
    simp only [g, zero_smul, add_zero, sub_zero]
    abel
  rw [hgu, sub_zero, Real.norm_eq_abs] at hb
  exact hb

/-- Continuous partial derivatives along finitely many directions give the directional
derivative along every linear combination of those directions. -/
theorem hasDerivAt_dir_of_partials {ι : Type*} (f : E → F) (U : Set E) (hU : IsOpen U)
    (e : ι → E) (D : ι → E → F)
    (hD : ∀ i, ∀ q ∈ U, HasDerivAt (fun s : ℝ ↦ f (q + s • e i)) (D i q) 0)
    (p : E) (hp : p ∈ U) (hcont : ∀ i, ContinuousAt (D i) p) (c : ι → ℝ) (s : Finset ι) :
    HasDerivAt (fun h : ℝ ↦ f (p + h • ∑ i ∈ s, c i • e i)) (∑ i ∈ s, c i • D i p) 0 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, smul_zero, add_zero]
    exact hasDerivAt_const 0 (f p)
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hfirst : HasDerivAt
        (fun h : ℝ ↦ f ((p + h • ∑ i ∈ s, c i • e i) + (h * c a) • e a) -
          f (p + h • ∑ i ∈ s, c i • e i)) (c a • D a p) 0 := by
      rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
      intro ε hε
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU p hp
      obtain ⟨δ, hδ, hδD⟩ :=
        Metric.continuousAt_iff.mp (hcont a) (ε / (|c a| + 1)) (by positivity)
      set W := ∑ i ∈ s, c i • e i with hW
      have hR : 0 < min r δ := lt_min hr hδ
      have hK : 0 < ‖W‖ + |c a| * ‖e a‖ + 1 := by positivity
      have hev : ∀ᶠ h : ℝ in 𝓝 0, |h| < min r δ / (‖W‖ + |c a| * ‖e a‖ + 1) := by
        have hball := Metric.ball_mem_nhds (0 : ℝ) (div_pos hR hK)
        filter_upwards [hball] with h hh
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
        exact hh
      filter_upwards [hev] with h hh
      have hhK : |h| * (‖W‖ + |c a| * ‖e a‖ + 1) < min r δ := by
        have := mul_lt_mul_of_pos_right hh hK
        rwa [div_mul_cancel₀ _ hK.ne'] at this
      have hpt : ∀ θ ∈ uIcc (0 : ℝ) (h * c a),
          dist ((p + h • W) + θ • e a) p < min r δ := by
        intro θ hθ
        have hθ' := abs_le_abs_of_mem_uIcc_zero hθ
        rw [dist_eq_norm]
        have e1 : (p + h • W) + θ • e a - p = h • W + θ • e a := by abel
        rw [e1]
        calc ‖h • W + θ • e a‖ ≤ ‖h • W‖ + ‖θ • e a‖ := norm_add_le _ _
          _ = |h| * ‖W‖ + |θ| * ‖e a‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ |h| * ‖W‖ + |h * c a| * ‖e a‖ := by gcongr
          _ = |h| * (‖W‖ + |c a| * ‖e a‖) := by rw [abs_mul]; ring
          _ ≤ |h| * (‖W‖ + |c a| * ‖e a‖ + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg h)
          _ < min r δ := hhK
      have hstep := norm_step_le f U (e a) (D a) (hD a) (p + h • W) (h * c a)
        (fun θ hθ ↦ hrU (Metric.mem_ball.mpr
          (lt_of_lt_of_le (hpt θ hθ) (min_le_left _ _))))
        (D a p) (ε / (|c a| + 1))
        (fun θ hθ ↦ by
          have := hδD (lt_of_lt_of_le (hpt θ hθ) (min_le_right _ _))
          rw [dist_eq_norm] at this
          exact this.le)
      have hfin : ε / (|c a| + 1) * |h * c a| ≤ ε * ‖h‖ := by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |c a| / (|c a| + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
        calc ε / (|c a| + 1) * (|h| * |c a|) = ε * |h| * (|c a| / (|c a| + 1)) := by ring
          _ ≤ ε * |h| * 1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hε.le (abs_nonneg h))
          _ = ε * |h| := mul_one _
      simp only [zero_add, zero_smul, zero_mul, add_zero, sub_self, sub_zero, smul_smul]
      exact hstep.trans hfin
    have hsum := hfirst.add ih
    have hfun : (fun h : ℝ ↦ f (p + h • (c a • e a + ∑ i ∈ s, c i • e i))) =
        fun h ↦ (f ((p + h • ∑ i ∈ s, c i • e i) + (h * c a) • e a) -
          f (p + h • ∑ i ∈ s, c i • e i)) + f (p + h • ∑ i ∈ s, c i • e i) := by
      funext h
      rw [sub_add_cancel]
      congr 1
      rw [smul_add, smul_smul]
      abel
    rw [hfun]
    exact hsum

/-- Reparametrize a derivative along an affine line. -/
theorem hasDerivAt_along_shift (f : E → F) (p w : E) (D : F)
    (h : HasDerivAt (fun h : ℝ ↦ f (p + h • w)) D 0) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (p + (s - s0) • w)) D s0 := by
  have h2 : HasDerivAt (fun s : ℝ ↦ s - s0) 1 s0 := by
    simpa using (hasDerivAt_id s0).sub_const s0
  have h1 : HasDerivAt (fun h : ℝ ↦ f (p + h • w)) D ((fun s : ℝ ↦ s - s0) s0) := by
    simpa using h
  have h3 : HasDerivAt ((fun h : ℝ ↦ f (p + h • w)) ∘ fun s : ℝ ↦ s - s0) ((1 : ℝ) • D) s0 := by
    first
      | exact h1.scomp s0 h2
      | exact HasDerivAt.scomp s0 h1 h2
  rw [one_smul] at h3
  exact h3

end General

/-! ### Matrix-valued calculus helpers (elementwise norm, as in `ClosedC1Jet`) -/

section MatrixCalculus

variable {n : ℕ}

theorem hasDerivAt_entry {X : ℝ → Matrix (Fin n) (Fin n) ℝ} {X' : Matrix (Fin n) (Fin n) ℝ}
    {s : ℝ} (hX : HasDerivAt X X' s) (i j : Fin n) :
    HasDerivAt (fun r ↦ X r i j) (X' i j) s :=
  hasDerivAt_pi.mp (hasDerivAt_pi.mp hX i) j

theorem hasDerivAt_of_entries {X : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {X' : Matrix (Fin n) (Fin n) ℝ} {s : ℝ}
    (h : ∀ i j, HasDerivAt (fun r ↦ X r i j) (X' i j) s) : HasDerivAt X X' s :=
  hasDerivAt_pi.mpr fun i ↦ hasDerivAt_pi.mpr fun j ↦ h i j

theorem HasDerivAt.frob_const {X : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {X' : Matrix (Fin n) (Fin n) ℝ} {s : ℝ} (hX : HasDerivAt X X' s)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun r ↦ ReactionZero.frob (X r) M) (ReactionZero.frob X' M) s := by
  unfold ReactionZero.frob
  exact HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦
    (hasDerivAt_entry hX i j).mul_const (M i j)

theorem HasDerivAt.frob_mul {X Y : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {X' Y' : Matrix (Fin n) (Fin n) ℝ} {s : ℝ} (hX : HasDerivAt X X' s)
    (hY : HasDerivAt Y Y' s) :
    HasDerivAt (fun r ↦ ReactionZero.frob (X r) (Y r))
      (ReactionZero.frob X' (Y s) + ReactionZero.frob (X s) Y') s := by
  have h : HasDerivAt (fun r ↦ ∑ i, ∑ j, X r i j * Y r i j)
      (∑ i, ∑ j, (X' i j * Y s i j + X s i j * Y' i j)) s :=
    HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦
      (hasDerivAt_entry hX i j).mul (hasDerivAt_entry hY i j)
  unfold ReactionZero.frob
  convert h using 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]

theorem HasDerivAt.const_matrix_mul {X : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {X' : Matrix (Fin n) (Fin n) ℝ} {s : ℝ} (hX : HasDerivAt X X' s)
    (K : Matrix (Fin n) (Fin n) ℝ) : HasDerivAt (fun r ↦ K * X r) (K * X') s := by
  refine hasDerivAt_of_entries fun i j ↦ ?_
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun l _ ↦ (hasDerivAt_entry hX l j).const_mul (K i l)

theorem HasDerivAt.matrix_mul_const {X : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {X' : Matrix (Fin n) (Fin n) ℝ} {s : ℝ} (hX : HasDerivAt X X' s)
    (K : Matrix (Fin n) (Fin n) ℝ) : HasDerivAt (fun r ↦ X r * K) (X' * K) s := by
  refine hasDerivAt_of_entries fun i j ↦ ?_
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun l _ ↦ (hasDerivAt_entry hX i l).mul_const (K l j)

end MatrixCalculus

/-! ### Specialization to the original closed-domain jets -/

section Jets

open MatrixTransport.ReactionZero.ClosedDomain

variable {d n : ℕ} {Ω : Set (Space d)}

theorem zeroExtend_of_mem (v : C(Q Ω, Mat n)) {q : Ambient d} (hq : q ∈ domain Ω) :
    zeroExtend v q = v ⟨q, hq⟩ := by
  unfold zeroExtend
  rw [dif_pos hq]

theorem zeroExtend_val (v : C(Q Ω, Mat n)) (p : Q Ω) : zeroExtend v p.val = v p :=
  zeroExtend_of_mem v p.property

theorem continuousOn_zeroExtend (v : C(Q Ω, Mat n)) :
    ContinuousOn (zeroExtend v) (domain Ω) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (domain Ω).domRestrict (zeroExtend v) = v := by
    funext p
    exact zeroExtend_val v p
  rw [h]
  exact v.continuous

theorem continuousAt_zeroExtend (v : C(Q Ω, Mat n)) {p : Ambient d}
    (hp : p ∈ interior (domain Ω)) : ContinuousAt (zeroExtend v) p :=
  (continuousOn_zeroExtend v).continuousAt (mem_interior_iff_mem_nhds.mp hp)

/-- The time direction and the coordinate space directions. -/
def dirVec : Option (Fin d) → Ambient d
  | none => ((1 : ℝ), 0)
  | some j => (0, EuclideanSpace.single j (1 : ℝ))

/-- The partial derivative fields of a jet, extended by zero off the closed domain. -/
def jetPartial (φ : ClosedC1Jet Ω n) : Option (Fin d) → Ambient d → Mat n
  | none => zeroExtend φ.dt
  | some j => zeroExtend (φ.dx j)

theorem jet_hasDerivAt_partial (φ : ClosedC1Jet Ω n) (i : Option (Fin d)) (q : Ambient d)
    (hq : q ∈ interior (domain Ω)) :
    HasDerivAt (fun s : ℝ ↦ zeroExtend φ.value (q + s • dirVec i)) (jetPartial φ i q) 0 := by
  have hqd : q ∈ domain Ω := interior_subset hq
  cases i with
  | none =>
    have h := φ.time_deriv ⟨q, hqd⟩ hq
    have hline : (fun s : ℝ ↦ zeroExtend φ.value (q + s • dirVec (d := d) none)) =
        fun s ↦ zeroExtend φ.value (timeLine q s) := by
      funext s
      congr 1
      refine Prod.ext ?_ ?_ <;> simp [dirVec, timeLine]
    rw [hline]
    simp only [jetPartial, zeroExtend_of_mem φ.dt hqd]
    exact h
  | some j =>
    have h := φ.space_deriv ⟨q, hqd⟩ j hq
    have hline : (fun s : ℝ ↦ zeroExtend φ.value (q + s • dirVec (d := d) (some j))) =
        fun s ↦ zeroExtend φ.value (spaceLine q j s) := by
      funext s
      congr 1
      refine Prod.ext ?_ ?_ <;> simp [dirVec, spaceLine]
    rw [hline]
    simp only [jetPartial, zeroExtend_of_mem (φ.dx j) hqd]
    exact h

theorem euclidean_sum_single (y : Space d) :
    ∑ j, y j • EuclideanSpace.single j (1 : ℝ) = y := by
  first
    | (have h := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.sum_repr y
       simpa [EuclideanSpace.basisFun_apply] using h)
    | (have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr y
       simpa [EuclideanSpace.basisFun_apply] using h)
    | (ext i
       simp [EuclideanSpace.single_apply, Finset.sum_apply])

/-- The full chain rule for a jet along any direction at an interior point. -/
theorem jet_hasDerivAt_dir (φ : ClosedC1Jet Ω n) {p : Ambient d}
    (hp : p ∈ interior (domain Ω)) (w : Ambient d) :
    HasDerivAt (fun h : ℝ ↦ zeroExtend φ.value (p + h • w))
      (w.1 • zeroExtend φ.dt p + ∑ j, w.2 j • zeroExtend (φ.dx j) p) 0 := by
  classical
  have h := hasDerivAt_dir_of_partials (zeroExtend φ.value) (interior (domain Ω))
    isOpen_interior dirVec (jetPartial φ) (fun i q hq ↦ jet_hasDerivAt_partial φ i q hq) p hp
    (fun i ↦ by cases i <;> exact continuousAt_zeroExtend _ hp)
    (fun i ↦ Option.elim i w.1 fun j ↦ w.2 j) Finset.univ
  have hw : ∑ i, (Option.elim i w.1 fun j ↦ w.2 j) • dirVec (d := d) i = w := by
    rw [Fintype.sum_option]
    refine Prod.ext ?_ ?_
    · simp [dirVec, Prod.fst_sum]
    · have h2 : (∑ x : Fin d, (Option.elim (some x) w.1 fun j ↦ w.2 j) •
            dirVec (d := d) (some x)).2 = ∑ j : Fin d, w.2 j • EuclideanSpace.single j (1 : ℝ) := by
        rw [Prod.snd_sum]
        rfl
      rw [Prod.snd_add, h2, euclidean_sum_single]
      simp [dirVec]
  have hD : ∑ i, (Option.elim i w.1 fun j ↦ w.2 j) • jetPartial φ i p =
      w.1 • zeroExtend φ.dt p + ∑ j, w.2 j • zeroExtend (φ.dx j) p := by
    rw [Fintype.sum_option]
    rfl
  rw [hw, hD] at h
  exact h

/-- Chain rule at time `s0` along the affine curve `s ↦ p + (s - s0) w`. -/
theorem jet_hasDerivAt_affine (φ : ClosedC1Jet Ω n) {p : Ambient d}
    (hp : p ∈ interior (domain Ω)) (w : Ambient d) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ ↦ zeroExtend φ.value (p + (s - s0) • w))
      (w.1 • zeroExtend φ.dt p + ∑ j, w.2 j • zeroExtend (φ.dx j) p) s0 :=
  hasDerivAt_along_shift _ p w _ (jet_hasDerivAt_dir φ hp w) s0

end Jets

#print axioms hasDerivAt_dir_of_partials
#print axioms jet_hasDerivAt_dir
#print axioms jet_hasDerivAt_affine
#print axioms HasDerivAt.frob_mul

end MatrixTransport.EntrywiseBures
