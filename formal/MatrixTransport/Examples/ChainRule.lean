import MatrixTransport.Examples.Jets

/-!
# Native closed-domain chain rule along axis-aligned curves

For a native closed-domain C¹ jet and an interior affine curve
`s ↦ (s, y₀ + c s eⱼ)`, continuous coordinate partial derivatives give
`d/ds φ(s, y₀ + c s eⱼ) = ∂ₜφ + c ∂ⱼφ`. The scalar two-variable chain rule is
proved by a mean-value argument. Its weighted fundamental theorem of calculus
supplies the continuity equation for the atom paths. This module treats
axis-aligned velocities.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace LiZouTransport.Examples

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain

/-! ### One-variable mean-value bound -/

theorem mvt_bound (g g' : ℝ → ℝ) (a b C : ℝ)
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hC : ∀ x ∈ Set.uIcc a b, |g' x| ≤ C) :
    |g b - g a| ≤ C * |b - a| := by
  have h : ‖g b - g a‖ ≤ C * ‖b - a‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hg x hx).hasDerivWithinAt)
      (fun x hx => by simpa [Real.norm_eq_abs] using hC x hx)
      (convex_uIcc a b) Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using h

/-! ### The planar chain rule -/

/-- **Planar chain rule from continuous partials.**  If the partials `A = ∂ₜK`, `B = ∂ᵤK` exist
on a box around `(t₀,u₀)` and are continuous at `(t₀,u₀)`, then along the line of slope `c`,
`s ↦ K s (u₀ + c (s - t₀))` has derivative `A + c B` at `t₀`. -/
theorem planar_chain_rule (K A B : ℝ → ℝ → ℝ) (t₀ u₀ c r : ℝ) (hr : 0 < r)
    (hA : ∀ t u, |t - t₀| < r → |u - u₀| < r → HasDerivAt (fun τ => K τ u) (A t u) t)
    (hB : ∀ t u, |t - t₀| < r → |u - u₀| < r → HasDerivAt (fun υ => K t υ) (B t u) u)
    (hAc : ContinuousAt (fun p : ℝ × ℝ => A p.1 p.2) (t₀, u₀))
    (hBc : ContinuousAt (fun p : ℝ × ℝ => B p.1 p.2) (t₀, u₀)) :
    HasDerivAt (fun s => K s (u₀ + c * (s - t₀))) (A t₀ u₀ + c * B t₀ u₀) t₀ := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hc1 : 0 < 1 + |c| := by positivity
  obtain ⟨ε', hε', hε'eq⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' * (1 + |c|) = ε :=
    ⟨ε / (1 + |c|), div_pos hε hc1, by field_simp⟩
  obtain ⟨δ₁, hδ₁, hAδ⟩ := Metric.continuousAt_iff.mp hAc ε' hε'
  obtain ⟨δ₂, hδ₂, hBδ⟩ := Metric.continuousAt_iff.mp hBc ε' hε'
  obtain ⟨δ, hδ, hδ1, hδ2, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ ∧ δ ≤ r :=
    ⟨min (min δ₁ δ₂) r, lt_min (lt_min hδ₁ hδ₂) hr,
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _), min_le_right _ _⟩
  have hAb : ∀ t u, |t - t₀| < δ → |u - u₀| < δ → |A t u - A t₀ u₀| < ε' := by
    intro t u ht hu
    have hd : dist ((t, u) : ℝ × ℝ) (t₀, u₀) < δ₁ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [Real.dist_eq] using lt_of_lt_of_le ht hδ1,
        by simpa [Real.dist_eq] using lt_of_lt_of_le hu hδ1⟩
    simpa [Real.dist_eq] using hAδ hd
  have hBb : ∀ t u, |t - t₀| < δ → |u - u₀| < δ → |B t u - B t₀ u₀| < ε' := by
    intro t u ht hu
    have hd : dist ((t, u) : ℝ × ℝ) (t₀, u₀) < δ₂ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [Real.dist_eq] using lt_of_lt_of_le ht hδ2,
        by simpa [Real.dist_eq] using lt_of_lt_of_le hu hδ2⟩
    simpa [Real.dist_eq] using hBδ hd
  have hn1 : Metric.ball t₀ δ ∈ 𝓝 t₀ := Metric.ball_mem_nhds t₀ hδ
  have hn2 : ∀ᶠ s in 𝓝 t₀, |c| * |s - t₀| < δ := by
    have hcont : Continuous fun s : ℝ => |c| * |s - t₀| :=
      continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))
    exact hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hδ)
  filter_upwards [hn1, hn2] with s hs hs2
  have hs' : |s - t₀| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hs
  have hsr : |s - t₀| < r := lt_of_lt_of_le hs' hδr
  -- the time leg at height `u₀`
  have hleg1 : |(K s u₀ - A t₀ u₀ * s) - (K t₀ u₀ - A t₀ u₀ * t₀)| ≤ ε' * |s - t₀| := by
    have h := mvt_bound (fun τ => K τ u₀ - A t₀ u₀ * τ) (fun τ => A τ u₀ - A t₀ u₀ * 1)
      t₀ s ε'
      (fun τ hτ => by
        have hτ' : |τ - t₀| ≤ |s - t₀| := Set.abs_sub_left_of_mem_uIcc hτ
        have hτδ : |τ - t₀| < δ := lt_of_le_of_lt hτ' hs'
        have hd := hA τ u₀ (lt_of_lt_of_le hτδ hδr) (by simpa using hr)
        exact hd.sub ((hasDerivAt_id τ).const_mul (A t₀ u₀)))
      (fun τ hτ => by
        have hτ' : |τ - t₀| ≤ |s - t₀| := Set.abs_sub_left_of_mem_uIcc hτ
        have hτδ : |τ - t₀| < δ := lt_of_le_of_lt hτ' hs'
        have h2 := hAb τ u₀ hτδ (by simpa using hδ)
        simpa using h2.le)
    exact h
  -- the space leg at time `s`
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u₀ + c * (s - t₀) := ⟨_, rfl⟩
  have hvu : |v - u₀| = |c| * |s - t₀| := by
    rw [hv]
    simp [abs_mul]
  have hleg2 : |(K s v - B t₀ u₀ * v) - (K s u₀ - B t₀ u₀ * u₀)| ≤ ε' * (|c| * |s - t₀|) := by
    have h := mvt_bound (fun υ => K s υ - B t₀ u₀ * υ) (fun υ => B s υ - B t₀ u₀ * 1)
      u₀ v ε'
      (fun υ hυ => by
        have hυ' : |υ - u₀| ≤ |v - u₀| := Set.abs_sub_left_of_mem_uIcc hυ
        have hυδ : |υ - u₀| < δ := by rw [hvu] at hυ'; exact lt_of_le_of_lt hυ' hs2
        have hd := hB s υ hsr (lt_of_lt_of_le hυδ hδr)
        exact hd.sub ((hasDerivAt_id υ).const_mul (B t₀ u₀)))
      (fun υ hυ => by
        have hυ' : |υ - u₀| ≤ |v - u₀| := Set.abs_sub_left_of_mem_uIcc hυ
        have hυδ : |υ - u₀| < δ := by rw [hvu] at hυ'; exact lt_of_le_of_lt hυ' hs2
        have h2 := hBb s υ hs' hυδ
        simpa using h2.le)
    have h' : |(K s v - B t₀ u₀ * v) - (K s u₀ - B t₀ u₀ * u₀)| ≤ ε' * |v - u₀| := h
    rw [hvu] at h'
    exact h'
  show ‖K s (u₀ + c * (s - t₀)) - K t₀ (u₀ + c * (t₀ - t₀)) -
      (s - t₀) • (A t₀ u₀ + c * B t₀ u₀)‖ ≤ ε * ‖s - t₀‖
  have key : K s (u₀ + c * (s - t₀)) - K t₀ (u₀ + c * (t₀ - t₀)) -
      (s - t₀) • (A t₀ u₀ + c * B t₀ u₀) =
      ((K s v - B t₀ u₀ * v) - (K s u₀ - B t₀ u₀ * u₀)) +
        ((K s u₀ - A t₀ u₀ * s) - (K t₀ u₀ - A t₀ u₀ * t₀)) := by
    have hcv : K s (u₀ + c * (s - t₀)) = K s v := by rw [hv]
    rw [hcv]
    simp only [sub_self, mul_zero, add_zero, smul_eq_mul, hv]
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, key]
  calc |((K s v - B t₀ u₀ * v) - (K s u₀ - B t₀ u₀ * u₀)) +
        ((K s u₀ - A t₀ u₀ * s) - (K t₀ u₀ - A t₀ u₀ * t₀))|
      ≤ |(K s v - B t₀ u₀ * v) - (K s u₀ - B t₀ u₀ * u₀)| +
        |(K s u₀ - A t₀ u₀ * s) - (K t₀ u₀ - A t₀ u₀ * t₀)| := by
        first | exact abs_add _ _ | exact abs_add_le _ _
    _ ≤ ε' * (|c| * |s - t₀|) + ε' * |s - t₀| := add_le_add hleg2 hleg1
    _ = ε * |s - t₀| := by rw [← hε'eq]; ring

/-! ### Jets: zero extension and entries -/

section JetEntries

variable {d n : ℕ} {Ω : Set (Space d)}

theorem zeroExtend_apply_mem (f : C(Q Ω, Mat n)) (q : Q Ω) : zeroExtend f q.val = f q := by
  unfold zeroExtend
  rw [dif_pos q.property]

theorem continuous_matEntry (i i' : Fin n) : Continuous (fun M : Mat n => M i i') := by
  first
    | exact continuous_id.matrix_elem i i'
    | exact (continuous_apply i').comp (continuous_apply i)

theorem continuousOn_zeroExtend (f : C(Q Ω, Mat n)) : ContinuousOn (zeroExtend f) (domain Ω) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (domain Ω).domRestrict (zeroExtend f) = f := by
    funext q
    exact zeroExtend_apply_mem f q
  rw [h]
  exact f.continuous

theorem continuousOn_zeroExtend_entry (f : C(Q Ω, Mat n)) (i i' : Fin n) :
    ContinuousOn (fun p => zeroExtend f p i i') (domain Ω) :=
  (continuous_matEntry i i').comp_continuousOn (continuousOn_zeroExtend f)

theorem continuousAt_zeroExtend_entry (f : C(Q Ω, Mat n)) (i i' : Fin n) {p : Ambient d}
    (hp : p ∈ interior (domain Ω)) : ContinuousAt (fun x => zeroExtend f x i i') p :=
  (continuousOn_zeroExtend_entry f i i').continuousAt (mem_interior_iff_mem_nhds.mp hp)

/-- Evaluation of one matrix entry as a linear functional. -/
def entryLinear (m : ℕ) (i i' : Fin m) : Mat m →ₗ[ℝ] ℝ where
  toFun M := M i i'
  map_add' := by
    intro M N
    first | rfl | simp
  map_smul' := by
    intro c M
    first | rfl | simp

/-- Evaluation of one matrix entry as a continuous linear functional. -/
def entryCLM (m : ℕ) (i i' : Fin m) : Mat m →L[ℝ] ℝ :=
  (entryLinear m i i').toContinuousLinearMap

theorem hasDerivAt_matEntry {f : ℝ → Mat n} {f' : Mat n} {x : ℝ} (h : HasDerivAt f f' x)
    (i i' : Fin n) : HasDerivAt (fun s => f s i i') (f' i i') x := by
  have h2 := (entryCLM n i i').hasFDerivAt.comp_hasDerivAt x h
  first
    | exact h2
    | simpa [entryCLM, entryLinear] using h2

/-- The point `(t, y₀ + u eⱼ)` of the ambient space. -/
def axisPt (y₀ : Space d) (j : Fin d) (t u : ℝ) : Ambient d :=
  (t, y₀ + u • EuclideanSpace.single j (1 : ℝ))

theorem continuous_axisPt (y₀ : Space d) (j : Fin d) :
    Continuous (fun p : ℝ × ℝ => axisPt y₀ j p.1 p.2) := by
  unfold axisPt
  exact continuous_fst.prodMk (continuous_const.add (continuous_snd.smul continuous_const))

/-- **Chain rule for an arbitrary closed-`C¹` jet along `s ↦ (s, y₀ + (u₀ + c (s - t₀)) eⱼ)`.**
All hypotheses are the original ones: derivative certificates only at interior points,
along the coordinate lines. -/
theorem jet_hasDerivAt_axis (φ : ClosedC1Jet Ω n) (i i' : Fin n) (y₀ : Space d) (j : Fin d)
    (t₀ u₀ c : ℝ) (hp : axisPt y₀ j t₀ u₀ ∈ interior (domain Ω)) :
    HasDerivAt (fun s => zeroExtend φ.value (axisPt y₀ j s (u₀ + c * (s - t₀))) i i')
      (zeroExtend φ.dt (axisPt y₀ j t₀ u₀) i i' +
        c * zeroExtend (φ.dx j) (axisPt y₀ j t₀ u₀) i i') t₀ := by
  have hPc := continuous_axisPt y₀ j
  -- a box around `(t₀,u₀)` mapped into the interior
  have hmem : (fun p : ℝ × ℝ => axisPt y₀ j p.1 p.2) ⁻¹' interior (domain Ω) ∈ 𝓝 (t₀, u₀) :=
    hPc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have hbox : ∀ t u, |t - t₀| < r → |u - u₀| < r → axisPt y₀ j t u ∈ interior (domain Ω) := by
    intro t u ht hu
    have hin : ((t, u) : ℝ × ℝ) ∈ Metric.ball (t₀, u₀) r := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [Real.dist_eq] using ht, by simpa [Real.dist_eq] using hu⟩
    exact hball hin
  have hA : ∀ t u, |t - t₀| < r → |u - u₀| < r →
      HasDerivAt (fun τ => zeroExtend φ.value (axisPt y₀ j τ u) i i')
        (zeroExtend φ.dt (axisPt y₀ j t u) i i') t := by
    intro t u ht hu
    have hP := hbox t u ht hu
    obtain ⟨p, hpv⟩ : ∃ p : Q Ω, p.val = axisPt y₀ j t u := ⟨⟨_, interior_subset hP⟩, rfl⟩
    have hpint : p.val ∈ interior (domain Ω) := by rw [hpv]; exact hP
    have h0 := hasDerivAt_matEntry (φ.time_deriv p hpint) i i'
    have h1 : HasDerivAt (fun s => zeroExtend φ.value (timeLine p.val s) i i') (φ.dt p i i')
        (t - t) := by simpa using h0
    have h2 := h1.comp_sub_const t t
    have hder : zeroExtend φ.dt (axisPt y₀ j t u) = φ.dt p := by
      rw [← hpv]
      exact zeroExtend_apply_mem φ.dt p
    rw [hder]
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have hst : timeLine p.val (x - t) = axisPt y₀ j x u := by
      rw [hpv]
      refine Prod.ext ?_ rfl
      show t + (x - t) = x
      ring
    show zeroExtend φ.value (axisPt y₀ j x u) i i' =
      zeroExtend φ.value (timeLine p.val (x - t)) i i'
    rw [hst]
  have hB : ∀ t u, |t - t₀| < r → |u - u₀| < r →
      HasDerivAt (fun υ => zeroExtend φ.value (axisPt y₀ j t υ) i i')
        (zeroExtend (φ.dx j) (axisPt y₀ j t u) i i') u := by
    intro t u ht hu
    have hP := hbox t u ht hu
    obtain ⟨p, hpv⟩ : ∃ p : Q Ω, p.val = axisPt y₀ j t u := ⟨⟨_, interior_subset hP⟩, rfl⟩
    have hpint : p.val ∈ interior (domain Ω) := by rw [hpv]; exact hP
    have h0 := hasDerivAt_matEntry (φ.space_deriv p j hpint) i i'
    have h1 : HasDerivAt (fun s => zeroExtend φ.value (spaceLine p.val j s) i i')
        (φ.dx j p i i') (u - u) := by simpa using h0
    have h2 := h1.comp_sub_const u u
    have hder : zeroExtend (φ.dx j) (axisPt y₀ j t u) = φ.dx j p := by
      rw [← hpv]
      exact zeroExtend_apply_mem (φ.dx j) p
    rw [hder]
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have hsp : spaceLine p.val j (x - u) = axisPt y₀ j t x := by
      rw [hpv]
      refine Prod.ext rfl ?_
      show y₀ + u • EuclideanSpace.single j (1 : ℝ) + (x - u) • EuclideanSpace.single j (1 : ℝ) =
        y₀ + x • EuclideanSpace.single j (1 : ℝ)
      module
    show zeroExtend φ.value (axisPt y₀ j t x) i i' =
      zeroExtend φ.value (spaceLine p.val j (x - u)) i i'
    rw [hsp]
  have hAc : ContinuousAt (fun p : ℝ × ℝ => zeroExtend φ.dt (axisPt y₀ j p.1 p.2) i i')
      (t₀, u₀) :=
    ContinuousAt.comp (g := fun p : Ambient d => zeroExtend φ.dt p i i')
      (f := fun p : ℝ × ℝ => axisPt y₀ j p.1 p.2)
      (continuousAt_zeroExtend_entry φ.dt i i' hp) hPc.continuousAt
  have hBc : ContinuousAt (fun p : ℝ × ℝ => zeroExtend (φ.dx j) (axisPt y₀ j p.1 p.2) i i')
      (t₀, u₀) :=
    ContinuousAt.comp (g := fun p : Ambient d => zeroExtend (φ.dx j) p i i')
      (f := fun p : ℝ × ℝ => axisPt y₀ j p.1 p.2)
      (continuousAt_zeroExtend_entry (φ.dx j) i i' hp) hPc.continuousAt
  exact planar_chain_rule (fun t u => zeroExtend φ.value (axisPt y₀ j t u) i i')
    (fun t u => zeroExtend φ.dt (axisPt y₀ j t u) i i')
    (fun t u => zeroExtend (φ.dx j) (axisPt y₀ j t u) i i') t₀ u₀ c r hr hA hB hAc hBc

/-! ### The fundamental-theorem identity along an axis curve -/

/-- **FTC along an axis-aligned curve with a weight.**  For a curve in the closed domain that is
interior for `0 < s < 1`, and a `C¹` weight `g`,
`∫₀¹ (g' φ + g (∂ₜφ + c ∂ⱼφ)) ds = g(1) φ(γ 1) - g(0) φ(γ 0)`, entrywise, for every
closed-`C¹` jet `φ`. -/
theorem curve_ftc (φ : ClosedC1Jet Ω n) (i i' : Fin n) (y₀ : Space d) (j : Fin d) (c : ℝ)
    (hmem : ∀ s ∈ Icc (0 : ℝ) 1, axisPt y₀ j s (c * s) ∈ domain Ω)
    (hint : ∀ s ∈ Ioo (0 : ℝ) 1, axisPt y₀ j s (c * s) ∈ interior (domain Ω))
    (g g' : ℝ → ℝ) (hg : ∀ s, HasDerivAt g (g' s) s) (hgc : Continuous g)
    (hg'c : Continuous g') :
    ∫ s in (0 : ℝ)..1,
        (g' s * zeroExtend φ.value (axisPt y₀ j s (c * s)) i i' +
          g s * (zeroExtend φ.dt (axisPt y₀ j s (c * s)) i i' +
            c * zeroExtend (φ.dx j) (axisPt y₀ j s (c * s)) i i')) =
      g 1 * zeroExtend φ.value (axisPt y₀ j 1 (c * 1)) i i' -
        g 0 * zeroExtend φ.value (axisPt y₀ j 0 (c * 0)) i i' := by
  have hcurve : Continuous (fun s : ℝ => axisPt y₀ j s (c * s)) := by
    unfold axisPt
    exact continuous_id.prodMk (continuous_const.add ((continuous_const.mul continuous_id).smul
      continuous_const))
  have hmaps : MapsTo (fun s : ℝ => axisPt y₀ j s (c * s)) (Icc (0 : ℝ) 1) (domain Ω) :=
    fun s hs => hmem s hs
  have hEv : ContinuousOn (fun s : ℝ => zeroExtend φ.value (axisPt y₀ j s (c * s)) i i')
      (Icc (0 : ℝ) 1) :=
    (continuousOn_zeroExtend_entry φ.value i i').comp hcurve.continuousOn hmaps
  have hDt : ContinuousOn (fun s : ℝ => zeroExtend φ.dt (axisPt y₀ j s (c * s)) i i')
      (Icc (0 : ℝ) 1) :=
    (continuousOn_zeroExtend_entry φ.dt i i').comp hcurve.continuousOn hmaps
  have hDx : ContinuousOn (fun s : ℝ => zeroExtend (φ.dx j) (axisPt y₀ j s (c * s)) i i')
      (Icc (0 : ℝ) 1) :=
    (continuousOn_zeroExtend_entry (φ.dx j) i i').comp hcurve.continuousOn hmaps
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s => g s * zeroExtend φ.value (axisPt y₀ j s (c * s)) i i')
        (g' s * zeroExtend φ.value (axisPt y₀ j s (c * s)) i i' +
          g s * (zeroExtend φ.dt (axisPt y₀ j s (c * s)) i i' +
            c * zeroExtend (φ.dx j) (axisPt y₀ j s (c * s)) i i')) s := by
    intro s₀ hs₀
    have h := jet_hasDerivAt_axis φ i i' y₀ j s₀ (c * s₀) c (hint s₀ hs₀)
    have h' : HasDerivAt (fun s => zeroExtend φ.value (axisPt y₀ j s (c * s)) i i')
        (zeroExtend φ.dt (axisPt y₀ j s₀ (c * s₀)) i i' +
          c * zeroExtend (φ.dx j) (axisPt y₀ j s₀ (c * s₀)) i i') s₀ := by
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      have hc : c * s₀ + c * (s - s₀) = c * s := by ring
      show zeroExtend φ.value (axisPt y₀ j s (c * s)) i i' =
        zeroExtend φ.value (axisPt y₀ j s (c * s₀ + c * (s - s₀))) i i'
      rw [hc]
    exact (hg s₀).mul h'
  have hcontF : ContinuousOn
      (fun s => g s * zeroExtend φ.value (axisPt y₀ j s (c * s)) i i') (Icc (0 : ℝ) 1) :=
    hgc.continuousOn.mul hEv
  have hcontD : ContinuousOn
      (fun s => g' s * zeroExtend φ.value (axisPt y₀ j s (c * s)) i i' +
        g s * (zeroExtend φ.dt (axisPt y₀ j s (c * s)) i i' +
          c * zeroExtend (φ.dx j) (axisPt y₀ j s (c * s)) i i')) (Icc (0 : ℝ) 1) :=
    (hg'c.continuousOn.mul hEv).add (hgc.continuousOn.mul (hDt.add (continuousOn_const.mul hDx)))
  have hintg : IntervalIntegrable
      (fun s => g' s * zeroExtend φ.value (axisPt y₀ j s (c * s)) i i' +
        g s * (zeroExtend φ.dt (axisPt y₀ j s (c * s)) i i' +
          c * zeroExtend (φ.dx j) (axisPt y₀ j s (c * s)) i i')) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hcontD
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcontF hderiv hintg

end JetEntries

end LiZouTransport.Examples

end
