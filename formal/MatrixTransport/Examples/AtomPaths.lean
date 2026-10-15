import MatrixTransport.Examples.ChainRule

/-!
# Signed Radon paths of moving and static atoms

`AxisCurve Ω` is an affine curve in the closed domain that lies in its interior
for interior times. `TAtom Ω` carries a time-dependent mass, with flux equal to
mass times velocity and reaction equal to the mass derivative. `TwoAtom Ω`
combines two such atoms using a continuous separating function.

The signed-coordinate pairing is the sum of the two curve integrals. For every
native closed-domain C¹ jet, the continuity equation follows from the curve FTC.
The resulting paths satisfy `Good` for the prescribed Dirac endpoints, and their
original integrated support action has an explicit upper bound.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Matrix BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace LiZouTransport.Examples

open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain

/-! ### Elementary lemmas -/

section Elementary

/-- Clamp to `[0,1]`, giving total continuous maps from `ℝ`. -/
def clamp01 (s : ℝ) : ℝ := max 0 (min s 1)

theorem clamp01_mem (s : ℝ) : clamp01 s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clamp01_of_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : clamp01 s = s := by
  unfold clamp01
  rw [min_eq_left hs.2, max_eq_right hs.1]

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

theorem setIntegral_Icc_eq_intervalIntegral (f : ℝ → ℝ) :
    ∫ s in Icc (0 : ℝ) 1, f s = ∫ s in (0 : ℝ)..1, f s := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem sum_coord_one {d : ℕ} (F : Coord 1 d → ℝ) :
    ∑ c, F c = F (Sum.inl (0, 0)) + (∑ l, F (Sum.inr (Sum.inl (0, l)))) +
      F (Sum.inr (Sum.inr (0, 0))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, sum_fin_one]
  ring

end Elementary

/-! ### Pairing with `withDensityᵥ` of a finite measure -/

section Pairing

variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]

theorem coordinatePair_withDensityᵥ (ν : Measure α) [IsFiniteMeasure ν] (W : ι → α → ℝ)
    (hWM : ∀ c, Measurable (W c)) (hWB : ∀ c, ∃ C : ℝ, ∀ x, |W c x| ≤ C)
    (a : α → ι → ℝ) (haM : ∀ c, Measurable fun x => a x c)
    (haB : ∀ c, ∃ C : ℝ, ∀ x, |a x c| ≤ C) :
    Duality.coordinatePair (fun _ ↦ 1) (fun c => ν.withDensityᵥ (W c)) a =
      ∫ x, ∑ c, a x c * W c x ∂ν := by
  have hint : ∀ c, Integrable (W c) ν := by
    intro c
    obtain ⟨C, hC⟩ := hWB c
    exact Integrable.mono' (integrable_const C) (hWM c).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hint2 : ∀ c, Integrable (fun x => a x c * W c x) ν := by
    intro c
    obtain ⟨C₁, hC₁⟩ := haB c
    obtain ⟨C₂, hC₂⟩ := hWB c
    refine Integrable.mono' (integrable_const (C₁ * C₂))
      ((haM c).mul (hWM c)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC₁ x) (hC₂ x) (abs_nonneg _) ((abs_nonneg _).trans (hC₁ x))
  have hterm : ∀ c, (1 : ℝ) * MatrixTransport.signedPair (ν.withDensityᵥ (W c))
      (fun x => a x c) = ∫ x, a x c * W c x ∂ν := by
    intro c
    rw [one_mul]
    exact MatrixTransport.signedPair_withDensityᵥ ν (hWM c) (hint c) (haM c) (haB c)
  unfold Duality.coordinatePair
  show (∑ c, (1 : ℝ) * MatrixTransport.signedPair (ν.withDensityᵥ (W c)) (fun x => a x c)) = _
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  exact (integral_finsetSum Finset.univ (fun c _ => hint2 c)).symm

end Pairing

/-! ### Axis curves, atoms, two-atom paths -/

section Atoms

variable {d : ℕ} {Ω : Set (Space d)}

/-- An axis-aligned affine curve in the closed domain, interior for `0 < s < 1`. -/
structure AxisCurve (Ω : Set (Space d)) where
  y₀ : Space d
  j : Fin d
  c : ℝ
  mem : ∀ s ∈ Icc (0 : ℝ) 1, axisPt y₀ j s (c * s) ∈ domain Ω
  interior_mem : ∀ s ∈ Ioo (0 : ℝ) 1, axisPt y₀ j s (c * s) ∈ interior (domain Ω)

/-- The curve as a total map `ℝ → Q Ω` (clamped to `[0,1]`). -/
def AxisCurve.pt (γ : AxisCurve Ω) (s : ℝ) : Q Ω :=
  ⟨axisPt γ.y₀ γ.j (clamp01 s) (γ.c * clamp01 s), γ.mem _ (clamp01_mem s)⟩

theorem AxisCurve.continuous_pt (γ : AxisCurve Ω) : Continuous γ.pt := by
  unfold AxisCurve.pt
  refine Continuous.subtype_mk ?_ (fun s => γ.mem _ (clamp01_mem s))
  unfold axisPt
  exact continuous_clamp01.prodMk (continuous_const.add
    ((continuous_const.mul continuous_clamp01).smul continuous_const))

theorem AxisCurve.pt_val (γ : AxisCurve Ω) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (γ.pt s).val = axisPt γ.y₀ γ.j s (γ.c * s) := by
  unfold AxisCurve.pt
  simp [clamp01_of_mem hs]

/-- A curve carrying mass `g(s)`, flux `g(s) c eⱼ` and reaction `g'(s)`. -/
structure TAtom (Ω : Set (Space d)) where
  cur : AxisCurve Ω
  g : ℝ → ℝ
  g' : ℝ → ℝ
  hg : ∀ s, HasDerivAt g (g' s) s
  hgc : Continuous g
  hg'c : Continuous g'

/-- Coordinate weights of an atom at time `s`. -/
def TAtom.weight (X : TAtom Ω) (s : ℝ) : Coord 1 d → ℝ
  | Sum.inl _ => X.g s
  | Sum.inr (Sum.inl (_, l)) => if l = X.cur.j then X.g s * X.cur.c else 0
  | Sum.inr (Sum.inr _) => X.g' s

theorem TAtom.continuous_weight (X : TAtom Ω) (c : Coord 1 d) :
    Continuous fun s => X.weight s c := by
  rcases c with ⟨i, j⟩ | ⟨i, l⟩ | ⟨i, j⟩
  · exact X.hgc
  · by_cases h : l = X.cur.j
    · have : (fun s => X.weight s (Sum.inr (Sum.inl (i, l)))) = fun s => X.g s * X.cur.c := by
        funext s
        simp [TAtom.weight, h]
      rw [this]
      exact X.hgc.mul continuous_const
    · have : (fun s => X.weight s (Sum.inr (Sum.inl (i, l)))) = fun _ => (0 : ℝ) := by
        funext s
        simp [TAtom.weight, h]
      rw [this]
      exact continuous_const
  · exact X.hg'c

/-- Two atoms with a continuous separating functional on space. -/
structure TwoAtom (Ω : Set (Space d)) where
  A : TAtom Ω
  B : TAtom Ω
  ψ : Space d → ℝ
  ψ_cont : Continuous ψ
  ψ_A : ∀ s ∈ Icc (0 : ℝ) 1, ψ (axisPt A.cur.y₀ A.cur.j s (A.cur.c * s)).2 = 1
  ψ_B : ∀ s ∈ Icc (0 : ℝ) 1, ψ (axisPt B.cur.y₀ B.cur.j s (B.cur.c * s)).2 = 0

/-- Coordinate densities of the two-atom path. -/
def TwoAtom.dens (T : TwoAtom Ω) (c : Coord 1 d) (q : Q Ω) : ℝ :=
  T.ψ q.val.2 * T.A.weight q.val.1 c + (1 - T.ψ q.val.2) * T.B.weight q.val.1 c

/-- The finite positive reference: pushforwards of Lebesgue measure on `[0,1]`. -/
def TwoAtom.nu (T : TwoAtom Ω) : Measure (Q Ω) :=
  Measure.map T.A.cur.pt (volume.restrict (Icc (0 : ℝ) 1)) +
    Measure.map T.B.cur.pt (volume.restrict (Icc (0 : ℝ) 1))

instance TwoAtom.nu_finite (T : TwoAtom Ω) : IsFiniteMeasure T.nu := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
    first
      | infer_instance
      | exact ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  unfold TwoAtom.nu
  infer_instance

/-- The path: signed Radon measures with the stated densities against `ν`. -/
def TwoAtom.path (T : TwoAtom Ω) : Limit.Path Ω 1 d :=
  fun c => T.nu.withDensityᵥ (T.dens c)

theorem TwoAtom.continuous_dens (T : TwoAtom Ω) (c : Coord 1 d) : Continuous (T.dens c) := by
  unfold TwoAtom.dens
  have hψ : Continuous fun q : Q Ω => T.ψ q.val.2 :=
    T.ψ_cont.comp (continuous_snd.comp continuous_subtype_val)
  have hA : Continuous fun q : Q Ω => T.A.weight q.val.1 c :=
    (T.A.continuous_weight c).comp (continuous_fst.comp continuous_subtype_val)
  have hB : Continuous fun q : Q Ω => T.B.weight q.val.1 c :=
    (T.B.continuous_weight c).comp (continuous_fst.comp continuous_subtype_val)
  exact (hψ.mul hA).add ((continuous_const.sub hψ).mul hB)

theorem TwoAtom.dens_A (T : TwoAtom Ω) (c : Coord 1 d) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    T.dens c (T.A.cur.pt s) = T.A.weight s c := by
  have hv := T.A.cur.pt_val hs
  have h1 : (T.A.cur.pt s).val.1 = s := by simp [hv, axisPt]
  have h2 : T.ψ (T.A.cur.pt s).val.2 = 1 := by
    simpa [hv, axisPt] using T.ψ_A s hs
  unfold TwoAtom.dens
  rw [h1, h2]
  ring

theorem TwoAtom.dens_B (T : TwoAtom Ω) (c : Coord 1 d) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    T.dens c (T.B.cur.pt s) = T.B.weight s c := by
  have hv := T.B.cur.pt_val hs
  have h1 : (T.B.cur.pt s).val.1 = s := by simp [hv, axisPt]
  have h2 : T.ψ (T.B.cur.pt s).val.2 = 0 := by
    simpa [hv, axisPt] using T.ψ_B s hs
  unfold TwoAtom.dens
  rw [h1, h2]
  ring

variable [Fact (IsCompact Ω)]

theorem TwoAtom.integral_nu (T : TwoAtom Ω) (F : C(Q Ω, ℝ)) :
    ∫ x, F x ∂T.nu = (∫ s in Icc (0 : ℝ) 1, F (T.A.cur.pt s)) +
      ∫ s in Icc (0 : ℝ) 1, F (T.B.cur.pt s) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
    first
      | infer_instance
      | exact ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  unfold TwoAtom.nu
  rw [integral_add_measure (continuousTest_integrable F _) (continuousTest_integrable F _),
    integral_map T.A.cur.continuous_pt.measurable.aemeasurable F.continuous.aestronglyMeasurable,
    integral_map T.B.cur.continuous_pt.measurable.aemeasurable F.continuous.aestronglyMeasurable]

/-- The signed pairing of the path with a continuous field is the sum of two curve integrals. -/
theorem TwoAtom.coordinatePair_path (T : TwoAtom Ω) (a : C(Q Ω, Coord 1 d → ℝ)) :
    Duality.coordinatePair (fun _ ↦ 1) T.path a =
      (∫ s in (0 : ℝ)..1, ∑ c, a (T.A.cur.pt s) c * T.A.weight s c) +
        ∫ s in (0 : ℝ)..1, ∑ c, a (T.B.cur.pt s) c * T.B.weight s c := by
  have hdensB : ∀ c, ∃ C : ℝ, ∀ x, |T.dens c x| ≤ C := fun c =>
    exists_abs_bound_of_continuous (T.dens c) (T.continuous_dens c)
  have hpair := coordinatePair_withDensityᵥ T.nu T.dens
    (fun c => (T.continuous_dens c).measurable) hdensB a
    (fun c => (Duality.coordinateTest a c).continuous.measurable)
    (fun c => Duality.continuousField_coordinate_bounded a c)
  unfold TwoAtom.path
  rw [hpair]
  obtain ⟨F, hFdef⟩ : ∃ F : C(Q Ω, ℝ), ∀ x, F x = ∑ c, a x c * T.dens c x :=
    ⟨⟨fun x => ∑ c, a x c * T.dens c x,
      continuous_finsetSum _ fun c _ =>
        ((continuous_apply c).comp a.continuous).mul (T.continuous_dens c)⟩, fun x => rfl⟩
  have hF := T.integral_nu F
  have hFA : ∫ s in Icc (0 : ℝ) 1, F (T.A.cur.pt s) =
      ∫ s in Icc (0 : ℝ) 1, ∑ c, a (T.A.cur.pt s) c * T.A.weight s c := by
    refine integral_congr_ae ((ae_restrict_mem measurableSet_Icc).mono fun s hs => ?_)
    dsimp only
    rw [hFdef]
    exact Finset.sum_congr rfl fun c _ => by rw [T.dens_A c hs]
  have hFB : ∫ s in Icc (0 : ℝ) 1, F (T.B.cur.pt s) =
      ∫ s in Icc (0 : ℝ) 1, ∑ c, a (T.B.cur.pt s) c * T.B.weight s c := by
    refine integral_congr_ae ((ae_restrict_mem measurableSet_Icc).mono fun s hs => ?_)
    dsimp only
    rw [hFdef]
    exact Finset.sum_congr rfl fun c _ => by rw [T.dens_B c hs]
  have hmain : ∫ x, ∑ c, a x c * T.dens c x ∂T.nu = ∫ x, F x ∂T.nu :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => (hFdef x).symm)
  rw [hmain, hF, hFA, hFB, setIntegral_Icc_eq_intervalIntegral,
    setIntegral_Icc_eq_intervalIntegral]

/-! ### The continuity equation for every jet -/

/-- The integrand of the original CE pairing along an atom, in jet form. -/
theorem TAtom.integrand_eq (X : TAtom Ω) (φ : ClosedC1Jet Ω 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∑ c, testField (gradOp d) φ (X.cur.pt s) c * X.weight s c =
      X.g' s * zeroExtend (n := 1) φ.value (axisPt X.cur.y₀ X.cur.j s (X.cur.c * s)) 0 0 +
        X.g s * (zeroExtend (n := 1) φ.dt (axisPt X.cur.y₀ X.cur.j s (X.cur.c * s)) 0 0 +
          X.cur.c * zeroExtend (n := 1) (φ.dx X.cur.j) (axisPt X.cur.y₀ X.cur.j s (X.cur.c * s)) 0 0) := by
  have hv := X.cur.pt_val hs
  have e1 : zeroExtend (n := 1) φ.value (axisPt X.cur.y₀ X.cur.j s (X.cur.c * s)) = φ.value (X.cur.pt s) := by
    rw [← hv]; exact zeroExtend_apply_mem _ _
  have e2 : zeroExtend (n := 1) φ.dt (axisPt X.cur.y₀ X.cur.j s (X.cur.c * s)) = φ.dt (X.cur.pt s) := by
    rw [← hv]; exact zeroExtend_apply_mem _ _
  have e3 : zeroExtend (n := 1) (φ.dx X.cur.j) (axisPt X.cur.y₀ X.cur.j s (X.cur.c * s)) =
      φ.dx X.cur.j (X.cur.pt s) := by
    rw [← hv]; exact zeroExtend_apply_mem _ _
  rw [e1, e2, e3, sum_coord_one]
  have hflux : ∀ l, testField (gradOp d) φ (X.cur.pt s) (Sum.inr (Sum.inl (0, l))) =
      φ.dx l (X.cur.pt s) 0 0 := by
    intro l
    exact gradOp_apply φ (X.cur.pt s) l
  have hsum : ∑ l, testField (gradOp d) φ (X.cur.pt s) (Sum.inr (Sum.inl (0, l))) *
      X.weight s (Sum.inr (Sum.inl (0, l))) =
      φ.dx X.cur.j (X.cur.pt s) 0 0 * (X.g s * X.cur.c) := by
    simp only [hflux, TAtom.weight]
    simp [mul_ite, Finset.sum_ite_eq']
  have hm : testField (gradOp d) φ (X.cur.pt s) (Sum.inl (0, 0)) = φ.dt (X.cur.pt s) 0 0 := rfl
  have hr : testField (gradOp d) φ (X.cur.pt s) (Sum.inr (Sum.inr (0, 0))) =
      φ.value (X.cur.pt s) 0 0 := rfl
  rw [hsum, hm, hr]
  simp only [TAtom.weight]
  ring

theorem TAtom.curve_integral (X : TAtom Ω) (φ : ClosedC1Jet Ω 1) :
    ∫ s in (0 : ℝ)..1, ∑ c, testField (gradOp d) φ (X.cur.pt s) c * X.weight s c =
      X.g 1 * zeroExtend (n := 1) φ.value (axisPt X.cur.y₀ X.cur.j 1 (X.cur.c * 1)) 0 0 -
        X.g 0 * zeroExtend (n := 1) φ.value (axisPt X.cur.y₀ X.cur.j 0 (X.cur.c * 0)) 0 0 := by
  have hcongr : ∫ s in (0 : ℝ)..1, ∑ c, testField (gradOp d) φ (X.cur.pt s) c * X.weight s c =
      ∫ s in (0 : ℝ)..1,
        (X.g' s * zeroExtend (n := 1) φ.value (axisPt X.cur.y₀ X.cur.j s (X.cur.c * s)) 0 0 +
          X.g s * (zeroExtend (n := 1) φ.dt (axisPt X.cur.y₀ X.cur.j s (X.cur.c * s)) 0 0 +
            X.cur.c * zeroExtend (n := 1) (φ.dx X.cur.j) (axisPt X.cur.y₀ X.cur.j s (X.cur.c * s)) 0 0)) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hs
    exact X.integrand_eq φ hs
  rw [hcongr]
  exact curve_ftc φ 0 0 X.cur.y₀ X.cur.j X.cur.c X.cur.mem X.cur.interior_mem X.g X.g' X.hg
    X.hgc X.hg'c

/-- **The original continuity equation, for every closed-`C¹` jet, along a two-atom path.** -/
theorem TwoAtom.coordinatePair_CE (T : TwoAtom Ω) (φ : ClosedC1Jet Ω 1) :
    Duality.coordinatePair (fun _ ↦ 1) T.path (testField (gradOp d) φ) =
      (T.A.g 1 * zeroExtend (n := 1) φ.value (axisPt T.A.cur.y₀ T.A.cur.j 1 (T.A.cur.c * 1)) 0 0 -
        T.A.g 0 * zeroExtend (n := 1) φ.value (axisPt T.A.cur.y₀ T.A.cur.j 0 (T.A.cur.c * 0)) 0 0) +
      (T.B.g 1 * zeroExtend (n := 1) φ.value (axisPt T.B.cur.y₀ T.B.cur.j 1 (T.B.cur.c * 1)) 0 0 -
        T.B.g 0 * zeroExtend (n := 1) φ.value (axisPt T.B.cur.y₀ T.B.cur.j 0 (T.B.cur.c * 0)) 0 0) := by
  rw [T.coordinatePair_path, T.A.curve_integral φ, T.B.curve_integral φ]

/-! ### The scalar gradient problem with Dirac endpoints -/

/-- The original problem (operator `∇`, PSD Radon endpoints) with the given endpoints. -/
def gradProblem (g0 g1 : Fin 1 × Fin 1 → SignedMeasure ↥Ω)
    (h0 : EndpointPositiveSemidefinite g0) (h1 : EndpointPositiveSemidefinite g1) :
    Limit.Problem Ω 1 d :=
  ⟨gradOp d, g0, g1, h0, h1⟩

/-- Unit Dirac endpoints `δ_{a₀} → δ_{b₀}`. -/
def diracGradProblem (a₀ b₀ : ↥Ω) : Limit.Problem Ω 1 d :=
  gradProblem (fun _ => diracAt a₀ 1) (fun _ => diracAt b₀ 1)
    (diracAt_posSemidef a₀ zero_le_one) (diracAt_posSemidef b₀ zero_le_one)

theorem massSymmetric_fin_one (μ : Limit.Path Ω 1 d) : MassSymmetric μ := by
  intro i j
  rw [Subsingleton.elim i j]

/-- A two-atom path is `Good` for Dirac endpoints once its two endpoint identities hold. -/
theorem TwoAtom.good_dirac (T : TwoAtom Ω) (a₀ b₀ : ↥Ω)
    (h0 : ∀ φ : ClosedC1Jet Ω 1,
      T.A.g 0 * zeroExtend (n := 1) φ.value (axisPt T.A.cur.y₀ T.A.cur.j 0 (T.A.cur.c * 0)) 0 0 +
        T.B.g 0 * zeroExtend (n := 1) φ.value (axisPt T.B.cur.y₀ T.B.cur.j 0 (T.B.cur.c * 0)) 0 0 =
        φ.value (timeBoundary 0 ⟨le_rfl, zero_le_one⟩ a₀) 0 0)
    (h1 : ∀ φ : ClosedC1Jet Ω 1,
      T.A.g 1 * zeroExtend (n := 1) φ.value (axisPt T.A.cur.y₀ T.A.cur.j 1 (T.A.cur.c * 1)) 0 0 +
        T.B.g 1 * zeroExtend (n := 1) φ.value (axisPt T.B.cur.y₀ T.B.cur.j 1 (T.B.cur.c * 1)) 0 0 =
        φ.value (timeBoundary 1 ⟨zero_le_one, le_rfl⟩ b₀) 0 0) :
    Limit.Good (diracGradProblem a₀ b₀) T.path := by
  refine And.intro (massSymmetric_fin_one _) ?_
  intro φ
  change Duality.coordinatePair (fun _ ↦ 1) T.path (testField (gradOp d) φ) =
    endpointPair (fun _ : Fin 1 × Fin 1 => diracAt b₀ 1) φ 1 ⟨zero_le_one, le_rfl⟩ -
      endpointPair (fun _ : Fin 1 × Fin 1 => diracAt a₀ 1) φ 0 ⟨le_rfl, zero_le_one⟩
  rw [T.coordinatePair_CE]
  erw [endpointPair_diracAt, endpointPair_diracAt]
  have e0 := h0 φ
  have e1 := h1 φ
  linarith

/-! ### The integrated action bound -/

theorem TAtom.integrand_le (X : TAtom Ω) (L : Matrix (Fin d) (Fin d) ℝ) (b : ℝ → ℝ)
    (hX : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin d → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * L l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * X.g s + (∑ l, f l * (if l = X.cur.j then X.g s * X.cur.c else 0)) + r * X.g' s ≤ b s)
    (x : Coord 1 d → ℝ) (hx : x ∈ dualSet L (1 : Matrix (Fin 1) (Fin 1) ℝ)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∑ c, x c * X.weight s c ≤ b s := by
  have h := dualSet_bound_gradOp L x hx
  have key := hX s hs (mass x 0 0) (reaction x 0 0) (fun l => flux x 0 l) h
  rw [sum_coord_one]
  first
    | exact key
    | simpa [TAtom.weight, mass, flux, reaction] using key

/-- **Upper bound for the integrated support action of a two-atom path**, from a pointwise
bound valid for every dual-set value (completing the square), via the proved representation
`action = continuousDual`. -/
theorem TwoAtom.action_le (T : TwoAtom Ω) (L : Matrix (Fin d) (Fin d) ℝ) (bA bB : ℝ → ℝ)
    (hbA : Continuous bA) (hbB : Continuous bB)
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin d → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * L l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * T.A.g s + (∑ l, f l * (if l = T.A.cur.j then T.A.g s * T.A.cur.c else 0)) +
          r * T.A.g' s ≤ bA s)
    (hB : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin d → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * L l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * T.B.g s + (∑ l, f l * (if l = T.B.cur.j then T.B.g s * T.B.cur.c else 0)) +
          r * T.B.g' s ≤ bB s) :
    action L (1 : Matrix (Fin 1) (Fin 1) ℝ) T.path ≤
      ENNReal.ofReal ((∫ s in (0 : ℝ)..1, bA s) + ∫ s in (0 : ℝ)..1, bB s) := by
  refine action_le_of_pairing_le L 1 T.path _ (fun a ha => ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  rw [T.coordinatePair_path]
  have hcA : Continuous fun s => ∑ c, a (T.A.cur.pt s) c * T.A.weight s c :=
    continuous_finsetSum _ fun c _ =>
      (((continuous_apply c).comp (a.continuous.comp T.A.cur.continuous_pt))).mul
        (T.A.continuous_weight c)
  have hcB : Continuous fun s => ∑ c, a (T.B.cur.pt s) c * T.B.weight s c :=
    continuous_finsetSum _ fun c _ =>
      (((continuous_apply c).comp (a.continuous.comp T.B.cur.continuous_pt))).mul
        (T.B.continuous_weight c)
  have h1 := intervalIntegral.integral_mono_on (μ := volume) zero_le_one (hcA.intervalIntegrable _ _)
    (hbA.intervalIntegrable _ _)
    (fun s hs => T.A.integrand_le L bA hA (a (T.A.cur.pt s)) (ha _) hs)
  have h2 := intervalIntegral.integral_mono_on (μ := volume) zero_le_one (hcB.intervalIntegrable _ _)
    (hbB.intervalIntegrable _ _)
    (fun s hs => T.B.integrand_le L bB hB (a (T.B.cur.pt s)) (ha _) hs)
  exact add_le_add h1 h2

theorem zeroExtend_timeBoundary (f : C(Q Ω, Mat 1)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (x : ↥Ω) : zeroExtend f (t, x.val) = f (timeBoundary t ht x) :=
  zeroExtend_apply_mem f (timeBoundary t ht x)

/-- **All-competitor lower certificate for a scalar test with Dirac endpoints.**
For a scalar closed-`C¹` test `F` (with the original interior coordinate-line derivative
certificates) satisfying the pointwise Hamilton–Jacobi inequality
`∂ₜF + ½ |Lᵀ ∇F|² + ½ F² ≤ 0` on the whole closed domain, every `Good` competitor of the problem
`δ_{a₀} → δ_{b₀}` has action at least `F(1,b₀) - F(0,a₀)`. -/
theorem diracGradProblem_lower_bound (a₀ b₀ : ↥Ω) (L : Matrix (Fin d) (Fin d) ℝ)
    (F Ft : Ambient d → ℝ) (Fx : Fin d → Ambient d → ℝ)
    (hF : ContinuousOn F (domain Ω)) (hFt : ContinuousOn Ft (domain Ω))
    (hFx : ∀ j, ContinuousOn (Fx j) (domain Ω))
    (hdt : ∀ p : Q Ω, p.val ∈ interior (domain Ω) →
      HasDerivAt (fun s ↦ F (timeLine p.val s)) (Ft p.val) 0)
    (hdx : ∀ (p : Q Ω) (j : Fin d), p.val ∈ interior (domain Ω) →
      HasDerivAt (fun s ↦ F (spaceLine p.val j s)) (Fx j p.val) 0)
    (hHJ : ∀ q : Q Ω, Ft q.val + (1 / 2 : ℝ) * ∑ l, (∑ l', Fx l' q.val * L l' l) ^ 2 +
      (1 / 2 : ℝ) * (F q.val) ^ 2 ≤ 0) :
    ENNReal.ofReal (F (1, b₀.val) - F (0, a₀.val)) ≤
      Limit.minimumValue (diracGradProblem a₀ b₀) L 1 := by
  have hmem : ∀ q : Q Ω, testField (diracGradProblem a₀ b₀).operator
      (scalarJet F Ft Fx hF hFt hFx hdt hdx) q ∈ dualSet L (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    intro q
    apply testField_mem_dualSet_gradOp
    simp only [scalarJet_dt_apply, scalarJet_dx_apply, scalarJet_value_apply]
    exact hHJ q
  have h := ofReal_endpoint_le_minimumValue (diracGradProblem a₀ b₀) L 1
    (scalarJet F Ft Fx hF hFt hFx hdt hdx) hmem
  change ENNReal.ofReal
    (endpointPair (fun _ : Fin 1 × Fin 1 => diracAt b₀ 1) (scalarJet F Ft Fx hF hFt hFx hdt hdx)
        1 ⟨zero_le_one, le_rfl⟩ -
      endpointPair (fun _ : Fin 1 × Fin 1 => diracAt a₀ 1)
        (scalarJet F Ft Fx hF hFt hFx hdt hdx) 0 ⟨le_rfl, zero_le_one⟩) ≤ _ at h
  erw [endpointPair_diracAt, endpointPair_diracAt] at h
  simp only [scalarJet_value_apply, mul_one] at h
  exact h

end Atoms

end LiZouTransport.Examples

end
