import MatrixTransport.Paper.ExampleBridges

/-! Exact costs of the existing stationary annihilation and creation paths. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace LiZouTransport.ExampleBridges
open MatrixTransport.ReactionZero MatrixTransport.ReactionZero.ClosedDomain
open MatrixTransport.ReactionZero.Limit MatrixTransport.EntrywiseBures
open MatrixTransport.TransportInfinity LiZouTransport.Examples

theorem action_eq_of_flux_measures_zero {X : Type*} [MeasurableSpace X] {n k : ℕ}
    (L L' : Matrix (Fin k) (Fin k) ℝ) (H : RMat n)
    (μ : Coord n k → SignedMeasure X)
    (hμ : ∀ i l, μ (Sum.inr (Sum.inl (i, l))) = 0) : action L H μ = action L' H μ := by
  unfold action
  apply lintegral_congr
  intro x
  have hd : dropFlux (density μ x) = density μ x := by
    funext c
    rcases c with ⟨i, j⟩ | ⟨i, l⟩ | ⟨i, j⟩
    · rfl
    · simp only [dropFlux, fluxScale, pack, zero_smul, Matrix.zero_apply]
      exact (rnDeriv_zero_of_eq_zero μ _ (hμ i l) x).symm
    · rfl
  rw [← hd]
  exact cost_dropFlux_eq L L' H _

theorem static_flux_measures_zero :
    ∀ i l, rotStaticTwo.path (Sum.inr (Sum.inl (i, l))) = 0 := by
  intro i l
  have he : rotStaticTwo.dens (Sum.inr (Sum.inl (i, l))) = fun _ ↦ (0 : ℝ) := by
    funext q
    simp [TwoAtom.dens, rotStaticTwo, TAtom.weight, annihAtom, createAtom, staticCurveAt]
  change rotStaticTwo.nu.withDensityᵥ _ = 0
  rw [he]
  exact withDensityᵥ_zero

theorem rotStatic_action_eq (L : Matrix (Fin 2) (Fin 2) ℝ) :
    action L (1 : RMat 1) rotStaticTwo.path = ENNReal.ofReal 4 := by
  apply le_antisymm (rotStatic_action_le L)
  let ε : ℝ := 1 / 25
  let θ := Real.sqrt ε
  have hε : 0 < ε := by norm_num [ε]
  have hS : Real.pi * ε ≤ Real.sin θ :=
    pi_mul_le_sin_sqrt ε hε (by simp [ε])
  have hmin := minimumValue_le_of_good rotProblem (rotWeight θ ε) (1 : RMat 1)
    rotStaticTwo.path rotStatic_good
  rw [rot_value_eq θ ε hε hS] at hmin
  have he := action_eq_of_flux_measures_zero L (rotWeight θ ε) (1 : RMat 1)
    rotStaticTwo.path static_flux_measures_zero
  rwa [← he] at hmin

def zeroLike (X : TAtom disk2) : TAtom disk2 where
  cur := X.cur
  g := fun _ ↦ 0
  g' := fun _ ↦ 0
  hg := fun s ↦ hasDerivAt_const s 0
  hgc := continuous_const
  hg'c := continuous_const

def annihTwo : TwoAtom disk2 where
  A := annihAtom
  B := zeroLike createAtom
  ψ := rotStaticTwo.ψ
  ψ_cont := rotStaticTwo.ψ_cont
  ψ_A := rotStaticTwo.ψ_A
  ψ_B := rotStaticTwo.ψ_B

def createTwo : TwoAtom disk2 where
  A := zeroLike annihAtom
  B := createAtom
  ψ := rotStaticTwo.ψ
  ψ_cont := rotStaticTwo.ψ_cont
  ψ_A := rotStaticTwo.ψ_A
  ψ_B := rotStaticTwo.ψ_B

theorem endpoint_zero_positive :
    EndpointPositiveSemidefinite (fun _ : Fin 1 × Fin 1 ↦ (0 : SignedMeasure ↥disk2)) := by
  intro s hs
  change (0 : RMat 1).PosSemidef
  exact Matrix.PosSemidef.zero

def annihProblem : Problem disk2 1 2 :=
  gradProblem (fun _ ↦ diracAt rotA 1) (fun _ ↦ 0)
    (diracAt_posSemidef rotA zero_le_one) endpoint_zero_positive

def createProblem : Problem disk2 1 2 :=
  gradProblem (fun _ ↦ 0) (fun _ ↦ diracAt rotB 1)
    endpoint_zero_positive (diracAt_posSemidef rotB zero_le_one)

theorem staticAxis_rotA (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    axisPt (pt2 (-1 / 2) 0) 0 s (0 * s) = (timeBoundary s hs rotA).val := by
  apply Prod.ext
  · rfl
  · change pt2 (-1 / 2) 0 + (0 * s) • EuclideanSpace.single (0 : Fin 2) 1 =
      pt2 (-1 / 2) 0
    simp

theorem staticAxis_rotB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    axisPt (pt2 (1 / 2) 0) 0 s (0 * s) = (timeBoundary s hs rotB).val := by
  apply Prod.ext
  · rfl
  · change pt2 (1 / 2) 0 + (0 * s) • EuclideanSpace.single (0 : Fin 2) 1 = pt2 (1 / 2) 0
    simp

theorem annihTwo_good : Good annihProblem annihTwo.path := by
  refine ⟨massSymmetric_fin_one _, ?_⟩
  intro φ
  change Duality.coordinatePair (fun _ ↦ 1) annihTwo.path (testField (gradOp 2) φ) =
    endpointPair (fun _ ↦ (0 : SignedMeasure ↥disk2)) φ 1 ⟨zero_le_one, le_rfl⟩ -
      endpointPair (fun _ ↦ diracAt rotA 1) φ 0 ⟨le_rfl, zero_le_one⟩
  rw [annihTwo.coordinatePair_CE]
  erw [endpointPair_diracAt rotA 1 φ 0 ⟨le_rfl, zero_le_one⟩]
  have hz : endpointPair (fun _ ↦ (0 : SignedMeasure ↥disk2)) φ 1
      ⟨zero_le_one, le_rfl⟩ = 0 := by simp [endpointPair, signedPair_zeroMeasure]
  rw [hz]
  simp only [annihTwo, zeroLike, annihAtom, createAtom, staticCurveAt]
  norm_num
  have hp := staticAxis_rotA 0 ⟨le_rfl, zero_le_one⟩
  norm_num only [mul_zero] at hp
  rw [hp, zeroExtend_apply_mem]

theorem createTwo_good : Good createProblem createTwo.path := by
  refine ⟨massSymmetric_fin_one _, ?_⟩
  intro φ
  change Duality.coordinatePair (fun _ ↦ 1) createTwo.path (testField (gradOp 2) φ) =
    endpointPair (fun _ ↦ diracAt rotB 1) φ 1 ⟨zero_le_one, le_rfl⟩ -
      endpointPair (fun _ ↦ (0 : SignedMeasure ↥disk2)) φ 0 ⟨le_rfl, zero_le_one⟩
  rw [createTwo.coordinatePair_CE]
  erw [endpointPair_diracAt rotB 1 φ 1 ⟨zero_le_one, le_rfl⟩]
  have hz : endpointPair (fun _ ↦ (0 : SignedMeasure ↥disk2)) φ 0
      ⟨le_rfl, zero_le_one⟩ = 0 := by simp [endpointPair, signedPair_zeroMeasure]
  rw [hz]
  simp only [createTwo, zeroLike, annihAtom, createAtom, staticCurveAt]
  norm_num
  have hp := staticAxis_rotB 1 ⟨zero_le_one, le_rfl⟩
  norm_num only [zero_mul] at hp
  rw [hp, zeroExtend_apply_mem]

theorem annihTwo_action_le (L : Matrix (Fin 2) (Fin 2) ℝ) :
    action L (1 : RMat 1) annihTwo.path ≤ ENNReal.ofReal 2 := by
  have hz : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin 2 → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * L l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * annihTwo.B.g s + (∑ l, f l * (if l = annihTwo.B.cur.j then
          annihTwo.B.g s * annihTwo.B.cur.c else 0)) + r * annihTwo.B.g' s ≤ 0 := by
    intros
    simp [annihTwo, zeroLike]
  have h := annihTwo.action_le L (fun _ ↦ 2) (fun _ ↦ 0)
    continuous_const continuous_const (staticA_bound L) hz
  simpa using h

theorem createTwo_action_le (L : Matrix (Fin 2) (Fin 2) ℝ) :
    action L (1 : RMat 1) createTwo.path ≤ ENNReal.ofReal 2 := by
  have hz : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (m r : ℝ) (f : Fin 2 → ℝ),
      m + (1 / 2 : ℝ) * ∑ l, (∑ l', f l' * L l' l) ^ 2 + (1 / 2 : ℝ) * r ^ 2 ≤ 0 →
        m * createTwo.A.g s + (∑ l, f l * (if l = createTwo.A.cur.j then
          createTwo.A.g s * createTwo.A.cur.c else 0)) + r * createTwo.A.g' s ≤ 0 := by
    intros
    simp [createTwo, zeroLike]
  have h := createTwo.action_le L (fun _ ↦ 0) (fun _ ↦ 2)
    continuous_const continuous_const hz (staticB_bound L)
  simpa using h

theorem buresValue_one_zero (R : PSDSqrt 1) :
    buresValue R (1 : RMat 1) (1 : RMat 1) 0 = 2 ∧
      buresValue R (1 : RMat 1) 0 (1 : RMat 1) = 2 := by
  have hs0 : R.sqrt (0 : RMat 1) = 0 :=
    R.eq_sqrt_of_mul_self _ _ Matrix.PosSemidef.zero Matrix.PosSemidef.zero (by simp)
  simp [buresValue, buresSq, hs0, Matrix.trace, Matrix.diag]

theorem annihAtom_action_eq_two (L : Matrix (Fin 2) (Fin 2) ℝ) :
    action L (1 : RMat 1) annihTwo.path = ENNReal.ofReal 2 := by
  apply le_antisymm (annihTwo_action_le L)
  have h := buresValue_le_action (canonicalPSDSqrt 1) annihProblem
    (by intro A hA; rfl) (by simp) (by simp : IsUnit (1 : RMat 1).det)
    L annihTwo.path annihTwo_good
  have ht0 : totalMatrix annihProblem.initial = (1 : RMat 1) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [totalMatrix, annihProblem, gradProblem, diracAt_univ, Matrix.one_apply]
  have ht1 : totalMatrix annihProblem.terminal = (0 : RMat 1) := by
    ext i j
    simp [totalMatrix, annihProblem, gradProblem]
  rw [ht0, ht1, (buresValue_one_zero (canonicalPSDSqrt 1)).1] at h
  exact h

theorem createAtom_action_eq_two (L : Matrix (Fin 2) (Fin 2) ℝ) :
    action L (1 : RMat 1) createTwo.path = ENNReal.ofReal 2 := by
  apply le_antisymm (createTwo_action_le L)
  have h := buresValue_le_action (canonicalPSDSqrt 1) createProblem
    (by intro A hA; rfl) (by simp) (by simp : IsUnit (1 : RMat 1).det)
    L createTwo.path createTwo_good
  have ht0 : totalMatrix createProblem.initial = (0 : RMat 1) := by
    ext i j
    simp [totalMatrix, createProblem, gradProblem]
  have ht1 : totalMatrix createProblem.terminal = (1 : RMat 1) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [totalMatrix, createProblem, gradProblem, diracAt_univ, Matrix.one_apply]
  rw [ht0, ht1, (buresValue_one_zero (canonicalPSDSqrt 1)).2] at h
  exact h

theorem zeroLike_weight (X : TAtom disk2) (s : ℝ) (c : Coord 1 2) :
    (zeroLike X).weight s c = 0 := by
  rcases c with ⟨i, j⟩ | ⟨i, l⟩ | ⟨i, j⟩ <;> simp [TAtom.weight, zeroLike]

/-- The exact original two-atom measure is the sum of the two stationary component paths. -/
theorem rotStatic_path_eq_sum : rotStaticTwo.path = annihTwo.path + createTwo.path := by
  funext c
  have hνa : annihTwo.nu = rotStaticTwo.nu := rfl
  have hνb : createTwo.nu = rotStaticTwo.nu := rfl
  have hd : rotStaticTwo.dens c = annihTwo.dens c + createTwo.dens c := by
    funext q
    change rotStaticTwo.ψ q.val.2 * annihAtom.weight q.val.1 c +
      (1 - rotStaticTwo.ψ q.val.2) * createAtom.weight q.val.1 c =
      (rotStaticTwo.ψ q.val.2 * annihAtom.weight q.val.1 c +
        (1 - rotStaticTwo.ψ q.val.2) * (zeroLike createAtom).weight q.val.1 c) +
      (rotStaticTwo.ψ q.val.2 * (zeroLike annihAtom).weight q.val.1 c +
        (1 - rotStaticTwo.ψ q.val.2) * createAtom.weight q.val.1 c)
    simp only [zeroLike_weight, mul_zero, add_zero, zero_add]
  change rotStaticTwo.nu.withDensityᵥ (rotStaticTwo.dens c) =
    annihTwo.nu.withDensityᵥ (annihTwo.dens c) + createTwo.nu.withDensityᵥ (createTwo.dens c)
  rw [hνa, hνb, hd]
  exact withDensityᵥ_add'
    ((annihTwo.continuous_dens c).continuous_integrable)
    ((createTwo.continuous_dens c).continuous_integrable)

end LiZouTransport.ExampleBridges

#print axioms LiZouTransport.ExampleBridges.action_eq_of_flux_measures_zero
#print axioms LiZouTransport.ExampleBridges.static_flux_measures_zero
#print axioms LiZouTransport.ExampleBridges.rotStatic_action_eq
#print axioms LiZouTransport.ExampleBridges.endpoint_zero_positive
#print axioms LiZouTransport.ExampleBridges.staticAxis_rotA
#print axioms LiZouTransport.ExampleBridges.staticAxis_rotB
#print axioms LiZouTransport.ExampleBridges.annihTwo_good
#print axioms LiZouTransport.ExampleBridges.createTwo_good
#print axioms LiZouTransport.ExampleBridges.annihTwo_action_le
#print axioms LiZouTransport.ExampleBridges.createTwo_action_le
#print axioms LiZouTransport.ExampleBridges.buresValue_one_zero
#print axioms LiZouTransport.ExampleBridges.annihAtom_action_eq_two
#print axioms LiZouTransport.ExampleBridges.createAtom_action_eq_two
#print axioms LiZouTransport.ExampleBridges.zeroLike_weight
#print axioms LiZouTransport.ExampleBridges.rotStatic_path_eq_sum
