import MatrixTransport.Paper.RotationFilters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Analytic reaction reference curves in the numerical figure

These are real positive-parameter limits of the original rotating-reaction minima;
recorded solver evaluations are not used in any proof.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators Matrix

namespace LiZouTransport.AnalyticFigureReferences
open MatrixTransport.ReactionZero.ClosedDomain MatrixTransport.EntrywiseBures
open MatrixTransport.ReactionZero.Limit MatrixTransport.Paper.RotatingReaction
open LiZouTransport.RotationFilters

/-- The nontrivial positive-real parameter filter for the plotted reaction curves. -/
abbrev positiveZero : Filter ℝ := 𝓝[>] (0 : ℝ)

/-- These analytic reference limits are taken along a nonempty positive-real approach. -/
theorem positiveZero_neBot : NeBot positiveZero := by infer_instance

theorem positiveZero_positive : ∀ᶠ ε : ℝ in positiveZero, 0 < ε := self_mem_nhdsWithin

theorem positiveZero_tendsto : Tendsto (fun ε : ℝ ↦ ε) positiveZero (𝓝 0) :=
  nhdsWithin_le_nhds

theorem power_angle_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε : ℝ ↦ ε ^ r) positiveZero (𝓝 0) :=
  positiveZero_tendsto.rpow_const_nhds_zero hr

theorem power_div_sqrt (ε r : ℝ) (hε : 0 < ε) :
    ε ^ r / Real.sqrt ε = ε ^ (r - 1 / 2) := by
  rw [Real.sqrt_eq_rpow,Real.rpow_sub hε]

theorem subcritical_ratio :
    Tendsto (fun ε : ℝ ↦ ε ^ (3 / 4 : ℝ) / Real.sqrt ε) positiveZero (𝓝 0) := by
  have h := power_angle_tendsto (by norm_num : (0 : ℝ) < 1 / 4)
  apply h.congr'
  filter_upwards [positiveZero_positive] with ε hε
  rw [power_div_sqrt ε (3 / 4) hε]
  norm_num

theorem critical_ratio :
    Tendsto (fun ε : ℝ ↦ ε ^ (1 / 2 : ℝ) / Real.sqrt ε) positiveZero (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [positiveZero_positive] with ε hε
  rw [power_div_sqrt ε (1 / 2) hε]
  norm_num

theorem supercritical_ratio :
    Tendsto (fun ε : ℝ ↦ ε ^ (1 / 4 : ℝ) / Real.sqrt ε) positiveZero atTop := by
  have h := _root_.tendsto_rpow_neg_nhdsGT_zero (by norm_num : (-1 / 4 : ℝ) < 0)
  apply h.congr'
  filter_upwards [positiveZero_positive] with ε hε
  rw [power_div_sqrt ε (1 / 4) hε]
  norm_num

theorem supercritical_abs_ratio :
    Tendsto (fun ε : ℝ ↦ |ε ^ (1 / 4 : ℝ)| / Real.sqrt ε) positiveZero atTop := by
  apply supercritical_ratio.congr'
  filter_upwards [positiveZero_positive] with ε hε
  rw [abs_of_pos (Real.rpow_pos_of_pos hε _)]

/-- The explicit real curve realizing a plotted angle scale. -/
def powerCurve (r : ℝ) (ε : ℝ) : ℝ × ℝ := (ε,ε ^ r)

theorem powerCurve_joint {r : ℝ} (hr : 0 < r) :
    Tendsto (powerCurve r) positiveZero rotFilter :=
  tendsto_id.prodMk (power_angle_tendsto hr)

theorem powerCurve_angleFilter {r : ℝ} {s : Filter ℝ} (hr : 0 < r)
    (hRatio : Tendsto (fun ε : ℝ ↦ ε ^ r / Real.sqrt ε) positiveZero s) :
    Tendsto (powerCurve r) positiveZero (ratioFilter (fun p ↦ p.2 / Real.sqrt p.1) s) := by
  apply tendsto_inf.2
  constructor
  · exact powerCurve_joint hr
  · apply tendsto_comap_iff.2
    simpa only [Function.comp_def,powerCurve] using hRatio

/-- The subcritical joint filter is realized by a nonempty positive-real approach. -/
theorem subcritical_joint_neBot :
    NeBot (ratioFilter (fun p ↦ p.2 / Real.sqrt p.1) (𝓝 0)) :=
  (powerCurve_angleFilter (by norm_num : (0 : ℝ) < 3 / 4) subcritical_ratio).neBot

theorem critical_joint_neBot :
    NeBot (ratioFilter (fun p ↦ p.2 / Real.sqrt p.1) (𝓝 1)) :=
  (powerCurve_angleFilter (by norm_num : (0 : ℝ) < 1 / 2) critical_ratio).neBot

theorem supercritical_joint_neBot :
    NeBot (ratioFilter (fun p ↦ |p.2| / Real.sqrt p.1) atTop) := by
  have h : Tendsto (powerCurve (1 / 4)) positiveZero
      (ratioFilter (fun p ↦ |p.2| / Real.sqrt p.1) atTop) := by
    apply tendsto_inf.2
    constructor
    · exact powerCurve_joint (by norm_num)
    · apply tendsto_comap_iff.2
      simpa only [Function.comp_def,powerCurve] using supercritical_abs_ratio
  exact h.neBot

variable {d k : ℕ} {Ω : Set (Space d)} [Fact (IsCompact Ω)]
variable (hΩ : Ω ⊆ closure (interior Ω)) (D : AdjointOperator d 2 k)
variable (hD0 : ∀ A : MatrixTransport.Paper.RotatingReaction.Mat,
  A.IsHermitian → D.D0 A = 0)
variable (μ : Measure ↥Ω) [IsFiniteMeasure μ] (hμ : μ univ = 1)
variable (L : Matrix (Fin k) (Fin k) ℝ)
include hΩ hD0 hμ

/-- The plotted exponent 3/4 gives the subcritical native limit. -/
theorem subcritical_native :
    Tendsto (fun ε : ℝ ↦ nativeValue D μ L ε (ε ^ (3 / 4 : ℝ))) positiveZero
      (𝓝 (ENNReal.ofReal targetValue)) := by
  have h := nativeValue_angle_finite hΩ D hD0 μ hμ L positiveZero_positive
    positiveZero_tendsto (power_angle_tendsto (by norm_num : (0 : ℝ) < 3 / 4))
    subcritical_ratio
  simpa only [zero_pow (by norm_num : (4 : ℕ) ≠ 0),zero_div,add_zero] using h

/-- The plotted exponent 1/2 gives the precise critical constant Vstar+1/2. -/
theorem critical_native :
    Tendsto (fun ε : ℝ ↦ nativeValue D μ L ε (ε ^ (1 / 2 : ℝ))) positiveZero
      (𝓝 (ENNReal.ofReal (targetValue + 1 / 2))) := by
  have h := nativeValue_angle_finite hΩ D hD0 μ hμ L positiveZero_positive
    positiveZero_tendsto (power_angle_tendsto (by norm_num : (0 : ℝ) < 1 / 2))
    critical_ratio
  simpa only [one_pow] using h

/-- The plotted exponent 1/4 gives divergence of the original minimum. -/
theorem supercritical_native :
    Tendsto (fun ε : ℝ ↦ nativeValue D μ L ε (ε ^ (1 / 4 : ℝ))) positiveZero (𝓝 ⊤) :=
  nativeValue_angle_top hΩ D hD0 μ hμ L positiveZero_positive
    positiveZero_tendsto (power_angle_tendsto (by norm_num : (0 : ℝ) < 1 / 4))
    supercritical_abs_ratio

/-- The supercritical plotted branch has the stated exact angle asymptotic. -/
theorem supercritical_native_asymptotic :
    Tendsto (fun ε : ℝ ↦ (nativeValue D μ L ε (ε ^ (1 / 4 : ℝ))).toReal /
      ((ε ^ (1 / 4 : ℝ)) ^ 4 / (2 * ε ^ 2))) positiveZero (𝓝 1) :=
  nativeValue_angle_asymptotic hΩ D hD0 μ hμ L positiveZero_positive
    positiveZero_tendsto (power_angle_tendsto (by norm_num : (0 : ℝ) < 1 / 4))
    supercritical_abs_ratio

#print axioms subcritical_joint_neBot
#print axioms critical_joint_neBot
#print axioms supercritical_joint_neBot
#print axioms subcritical_ratio
#print axioms critical_ratio
#print axioms supercritical_ratio
#print axioms subcritical_native
#print axioms critical_native
#print axioms supercritical_native
#print axioms supercritical_native_asymptotic
end LiZouTransport.AnalyticFigureReferences
