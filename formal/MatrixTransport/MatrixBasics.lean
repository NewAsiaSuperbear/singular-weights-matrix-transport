import Mathlib

open Matrix
open scoped BigOperators

noncomputable section

namespace MatrixTransport

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Flux (r : ℕ) := Matrix (Fin 2) (Fin r) ℝ

def frob {m n : Type*} [Fintype m] [Fintype n] (X Y : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

def E : Mat2 := Matrix.diagonal (fun i => if i = 1 then 1 else 0)

def density (u : ℝ) : Mat2 := Matrix.diagonal (fun i => if i = 1 then 1 + u else 1)

def LoewnerLE (X Y : Mat2) : Prop := Matrix.PosSemidef (Y - X)

def LocalDualConstraint {r : ℕ} (A : Mat2) (B : Flux r) (C : Mat2) : Prop :=
  Matrix.PosSemidef
    (-(A + (1 / 2 : ℝ) • (B * Matrix.transpose B) + (1 / 2 : ℝ) • (C * Matrix.transpose C)))

/-! ### Diagonal positivity helper -/

theorem psd_diag2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Matrix.PosSemidef (Matrix.diagonal (fun i : Fin 2 => if i = 1 then b else a)) := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases h : i = 1
  · simp [h, hb]
  · simp [h, ha]

/-! ### Group 1: E and density -/

theorem E_apply (i j : Fin 2) : E i j = if i = j then (if i = 1 then 1 else 0) else 0 := by
  simp [E, Matrix.diagonal_apply]

theorem E_one_one : E 1 1 = 1 := by simp [E]
theorem E_zero_zero : E 0 0 = 0 := by simp [E, Matrix.diagonal_apply]
theorem E_zero_one : E 0 1 = 0 := by simp [E, Matrix.diagonal_apply]
theorem E_one_zero : E 1 0 = 0 := by simp [E, Matrix.diagonal_apply]

theorem density_apply (u : ℝ) (i j : Fin 2) :
    density u i j = if i = j then (if i = 1 then 1 + u else 1) else 0 := by
  simp [density, Matrix.diagonal_apply]

theorem density_one_one (u : ℝ) : density u 1 1 = 1 + u := by simp [density]
theorem density_zero_zero (u : ℝ) : density u 0 0 = 1 := by simp [density, Matrix.diagonal_apply]
theorem density_zero_one (u : ℝ) : density u 0 1 = 0 := by simp [density, Matrix.diagonal_apply]
theorem density_one_zero (u : ℝ) : density u 1 0 = 0 := by simp [density, Matrix.diagonal_apply]

theorem E_mul_E : E * E = E := by
  unfold E
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = 1 <;> simp [h]

theorem E_transpose : Matrix.transpose E = E := by
  simp [E]

theorem E_posSemidef : Matrix.PosSemidef E := by
  unfold E
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases h : i = 1 <;> simp [h]

theorem frob_E_E : frob E E = 1 := by
  simp only [frob, Fin.sum_univ_two, E_zero_zero, E_zero_one, E_one_zero, E_one_one]
  norm_num

theorem density_eq (u : ℝ) : density u = (1 : Mat2) + u • E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [density, E, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff]

theorem density_isHermitian (u : ℝ) : Matrix.IsHermitian (density u) := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, density, Matrix.diagonal_apply, Fin.ext_iff]

/-! ### Group 2: Loewner bounds on density -/

theorem loewner_density_lower (u : ℝ) (hu : |u| ≤ 1 / 2) :
    LoewnerLE ((1 / 2 : ℝ) • (1 : Mat2)) (density u) := by
  have h := abs_le.mp hu
  unfold LoewnerLE
  have key : density u - (1 / 2 : ℝ) • (1 : Mat2) =
      Matrix.diagonal (fun i : Fin 2 => if i = 1 then (1 / 2 + u) else (1 / 2 : ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [density, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff] <;> ring
  rw [key]
  exact psd_diag2 (1 / 2) (1 / 2 + u) (by norm_num) (by linarith [h.1])

theorem loewner_density_upper (u : ℝ) (hu : |u| ≤ 1 / 2) :
    LoewnerLE (density u) ((3 / 2 : ℝ) • (1 : Mat2)) := by
  have h := abs_le.mp hu
  unfold LoewnerLE
  have key : (3 / 2 : ℝ) • (1 : Mat2) - density u =
      Matrix.diagonal (fun i : Fin 2 => if i = 1 then (1 / 2 - u) else (1 / 2 : ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [density, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff] <;> ring
  rw [key]
  exact psd_diag2 (1 / 2) (1 / 2 - u) (by norm_num) (by linarith [h.2])

/-! ### Group 3: local dual certificate -/

theorem local_cert_aux {r : ℕ} (a p : ℝ) (h : p * p / 2 ≤ a) :
    LocalDualConstraint ((-a) • E) (0 : Flux r) (p • E) := by
  unfold LocalDualConstraint
  have hd : Matrix.PosSemidef
      (Matrix.diagonal (fun i : Fin 2 => if i = 1 then a - p * p / 2 else (0 : ℝ))) :=
    psd_diag2 0 (a - p * p / 2) (le_refl 0) (by linarith)
  convert hd using 1
  have hC : (p • E) * Matrix.transpose (p • E) = (p * p) • E := by
    simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, E_mul_E, E_transpose,
      smul_smul]
  rw [hC]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.diagonal_apply, Fin.ext_iff] <;> ring

theorem local_cert_scalar (s c t : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 8) (hc : |c| ≤ 1)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (s * c - s ^ 2 * t) * (s * c - s ^ 2 * t) / 2 ≤ s ^ 2 := by
  have hc' := abs_le.mp hc
  have h1 : 0 ≤ s * (c + 1) := mul_nonneg hs0 (by linarith [hc'.1])
  have h2 : 0 ≤ s * (1 - c) := mul_nonneg hs0 (by linarith [hc'.2])
  have h3 : 0 ≤ s ^ 2 * t := mul_nonneg (sq_nonneg s) ht0
  have h4 : 0 ≤ s ^ 2 * (1 - t) := mul_nonneg (sq_nonneg s) (by linarith)
  have h5 : s * s ≤ s * (1 / 8) := mul_le_mul_of_nonneg_left hs hs0
  have hp : |s * c - s ^ 2 * t| ≤ 9 / 8 * s := by
    rw [abs_le]
    constructor <;> nlinarith
  have hm : |s * c - s ^ 2 * t| * |s * c - s ^ 2 * t| ≤ (9 / 8 * s) * (9 / 8 * s) :=
    mul_le_mul hp hp (abs_nonneg _) (by positivity)
  have he := abs_mul_abs_self (s * c - s ^ 2 * t)
  nlinarith [sq_nonneg s]

theorem local_dual_certificate {r : ℕ} (s c t : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 8)
    (hc : |c| ≤ 1) (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    LocalDualConstraint ((-(s ^ 2)) • E) (0 : Flux r) ((s * c - s ^ 2 * t) • E) :=
  local_cert_aux (s ^ 2) (s * c - s ^ 2 * t) (local_cert_scalar s c t hs0 hs hc ht0 ht)

end MatrixTransport

end


namespace MatrixTransport

noncomputable def singleFlux {r : ℕ} (j0 : Fin r) (v : ℝ) : Flux r :=
  fun i j => if i = 1 ∧ j = j0 then v else 0

theorem frob_density_diag (u : ℝ) (A : Mat2) :
    frob (density u) A = A 0 0 + (1 + u) * A 1 1 := by
  simp only [frob, Fin.sum_univ_two, density_zero_zero, density_zero_one, density_one_zero,
    density_one_one]
  ring

theorem frob_singleFlux {r : ℕ} (j0 : Fin r) (v : ℝ) (B : Flux r) :
    frob (singleFlux j0 v) B = v * B 1 j0 := by
  unfold frob singleFlux
  rw [Fin.sum_univ_two]
  simp

theorem local_diag_bound {r : ℕ} (A : Mat2) (B : Flux r) (C : Mat2)
    (h : LocalDualConstraint A B C) (i : Fin 2) :
    A i i + (1 / 2) * (∑ j, B i j * B i j) + (1 / 2) * (∑ j, C i j * C i j) ≤ 0 := by
  unfold LocalDualConstraint at h
  have h0 := Matrix.PosSemidef.diag_nonneg h (i := i)
  simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.transpose_apply, smul_eq_mul] at h0
  linarith

theorem single_flux_upper {r : ℕ} (j0 : Fin r) (u v : ℝ) (A : Mat2) (B : Flux r) (C : Mat2)
    (hu : |u| ≤ 1 / 2) (hd : LocalDualConstraint A B C) :
    frob (density u) A + frob (singleFlux j0 v) B ≤ v ^ 2 := by
  have h0 := local_diag_bound A B C hd 0
  have h1 := local_diag_bound A B C hd 1
  have hb0 : 0 ≤ ∑ j, B 0 j * B 0 j := Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
  have hb1 : 0 ≤ ∑ j, B 1 j * B 1 j := Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
  have hc0 : 0 ≤ ∑ j, C 0 j * C 0 j := Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
  have hc1 : 0 ≤ ∑ j, C 1 j * C 1 j := Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
  have hle : B 1 j0 * B 1 j0 ≤ ∑ j, B 1 j * B 1 j :=
    Finset.single_le_sum (f := fun j => B 1 j * B 1 j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ j0)
  rw [frob_density_diag, frob_singleFlux]
  have hu' := abs_le.mp hu
  have ha1 : A 1 1 ≤ 0 := by linarith
  have hprod : 0 ≤ (1 / 2 + u) * (-(A 1 1)) :=
    mul_nonneg (by linarith [hu'.1]) (by linarith)
  have hsq : 0 ≤ (B 1 j0 / 2 - v) * (B 1 j0 / 2 - v) := mul_self_nonneg _
  nlinarith [h0, h1, hb0, hb1, hc0, hc1, hle, hprod, hsq]

end MatrixTransport
