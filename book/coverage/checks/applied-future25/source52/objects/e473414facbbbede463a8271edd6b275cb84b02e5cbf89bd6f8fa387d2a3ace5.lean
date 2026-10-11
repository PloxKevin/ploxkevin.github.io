import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesEllipsoidRow

variable {n : Type*} [Fintype n] [DecidableEq n]

def actualRowEnergy (storage : Matrix n n ℝ) (row : n → ℝ) : ℝ :=
  row ⬝ᵥ (storage⁻¹ *ᵥ row)

theorem actual_inverse_metric_vector_cancels_positive_storage
    (storage : Matrix n n ℝ) (hs : storage.PosDef) (row : n → ℝ) :
    storage *ᵥ (storage⁻¹ *ᵥ row) = row := by
  let := hs.isUnit.invertible
  rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]

theorem actual_positive_storage_row_energy_is_nonnegative
    (storage : Matrix n n ℝ) (hs : storage.PosDef) (row : n → ℝ) :
    0 ≤ actualRowEnergy storage row := by
  simpa only [actualRowEnergy,star_trivial] using hs.inv.posSemidef.dotProduct_mulVec_nonneg row

theorem actual_nonzero_row_has_positive_inverse_metric_energy
    (storage : Matrix n n ℝ) (hs : storage.PosDef) (row : n → ℝ) (hr : row ≠ 0) :
    0 < actualRowEnergy storage row := by
  simpa only [actualRowEnergy,star_trivial] using hs.inv.dotProduct_mulVec_pos hr

theorem actual_inverse_metric_row_quadratic_and_pairing
    (storage : Matrix n n ℝ) (hs : storage.PosDef) (row vector : n → ℝ) :
    (storage⁻¹ *ᵥ row) ⬝ᵥ (storage *ᵥ (storage⁻¹ *ᵥ row)) = actualRowEnergy storage row ∧
    (storage⁻¹ *ᵥ row) ⬝ᵥ (storage *ᵥ vector) = row ⬝ᵥ vector := by
  constructor
  · rw [actual_inverse_metric_vector_cancels_positive_storage storage hs row,
      actualRowEnergy,dotProduct_comm]
  · have h := hs.isHermitian.star_dotProduct_mulVec_comm (storage⁻¹ *ᵥ row) vector
    simp only [star_trivial,actual_inverse_metric_vector_cancels_positive_storage storage hs row] at h
    exact h.trans (dotProduct_comm _ _)

theorem actual_positive_metric_cauchy_schwarz_bounds_every_row
    (storage : Matrix n n ℝ) (hs : storage.PosDef) (row vector : n → ℝ) :
    (row ⬝ᵥ vector)^2 ≤ actualRowEnergy storage row * (vector ⬝ᵥ (storage *ᵥ vector)) := by
  have h := hs.star_dotProduct_mulVec_mul_le (storage⁻¹ *ᵥ row) vector
  simp only [star_trivial] at h
  rw [(actual_inverse_metric_row_quadratic_and_pairing storage hs row vector).1,
    (actual_inverse_metric_row_quadratic_and_pairing storage hs row vector).2] at h
  simpa only [pow_two] using h

def actualRowAttainer (storage : Matrix n n ℝ) (row : n → ℝ) : n → ℝ :=
  (1 / Real.sqrt (actualRowEnergy storage row)) • (storage⁻¹ *ᵥ row)

theorem actual_nonzero_row_attainer_has_energy_one_and_attains_the_support
    (storage : Matrix n n ℝ) (hs : storage.PosDef) (row : n → ℝ) (hr : row ≠ 0) :
    actualRowAttainer storage row ⬝ᵥ (storage *ᵥ actualRowAttainer storage row) = 1 ∧
    row ⬝ᵥ actualRowAttainer storage row = Real.sqrt (actualRowEnergy storage row) := by
  have hk := actual_nonzero_row_has_positive_inverse_metric_energy storage hs row hr
  have hn : Real.sqrt (actualRowEnergy storage row) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
  have hsq := Real.sq_sqrt hk.le
  constructor
  · rw [actualRowAttainer,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]
    rw [(actual_inverse_metric_row_quadratic_and_pairing storage hs row row).1]
    simp only [smul_eq_mul]
    field_simp
    nlinarith
  · rw [actualRowAttainer,dotProduct_smul]
    change (1/Real.sqrt (actualRowEnergy storage row))*actualRowEnergy storage row = _
    field_simp
    nlinarith

theorem actual_row_interval_containment_iff_the_exact_inverse_metric_bound
    (storage : Matrix n n ℝ) (hs : storage.PosDef) (row : n → ℝ)
    (radius : ℝ) (hr : 0 ≤ radius) :
    (∀ vector : n → ℝ, vector ⬝ᵥ (storage *ᵥ vector) ≤ 1 → |row ⬝ᵥ vector| ≤ radius) ↔
      actualRowEnergy storage row ≤ radius^2 := by
  constructor
  · intro h
    by_cases hzero : row = 0
    · simp [actualRowEnergy,hzero,sq_nonneg]
    · obtain ⟨he,ha⟩ := actual_nonzero_row_attainer_has_energy_one_and_attains_the_support storage hs row hzero
      have hb := h (actualRowAttainer storage row) he.le
      rw [ha,abs_of_nonneg (Real.sqrt_nonneg _)] at hb
      nlinarith [Real.sqrt_nonneg (actualRowEnergy storage row),
        Real.sq_sqrt (actual_positive_storage_row_energy_is_nonnegative storage hs row)]
  · intro hk vector hv
    have hcs := actual_positive_metric_cauchy_schwarz_bounds_every_row storage hs row vector
    have he := actual_positive_storage_row_energy_is_nonnegative storage hs row
    have hb := mul_le_mul_of_nonneg_left hv he
    have ha := sq_abs (row ⬝ᵥ vector)
    nlinarith [abs_nonneg (row ⬝ᵥ vector)]

def actualRowMatrix (row : n → ℝ) : Matrix (Fin 1) n ℝ := fun _ index => row index
def actualRadiusSquareMatrix (radius : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => radius^2
def actualRowContainmentBlock (storage : Matrix n n ℝ) (row : n → ℝ) (radius : ℝ) :
    Matrix (Fin 1 ⊕ n) (Fin 1 ⊕ n) ℝ :=
  Matrix.fromBlocks (actualRadiusSquareMatrix radius) (actualRowMatrix row)
    (actualRowMatrix row).transpose storage

theorem actual_row_containment_schur_matrix_has_the_literal_inverse_metric_remainder
    (storage : Matrix n n ℝ) (row : n → ℝ) (radius : ℝ) :
    (actualRadiusSquareMatrix radius) - actualRowMatrix row * storage⁻¹ * (actualRowMatrix row).transpose =
      Matrix.diagonal (fun _ : Fin 1 => radius^2-actualRowEnergy storage row) := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.diagonal_apply,actualRowMatrix,actualRowEnergy,Matrix.mul_apply,
    Matrix.transpose_apply,Matrix.mulVec,dotProduct,Finset.sum_mul,actualRadiusSquareMatrix]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum,mul_assoc]

theorem actual_row_interval_containment_iff_the_true_source_schur_lmi
    (storage : Matrix n n ℝ) (hs : storage.PosDef) (row : n → ℝ)
    (radius : ℝ) (hr : 0 ≤ radius) :
    (∀ vector : n → ℝ, vector ⬝ᵥ (storage *ᵥ vector) ≤ 1 → |row ⬝ᵥ vector| ≤ radius) ↔
      (actualRowContainmentBlock storage row radius).PosSemidef := by
  let := hs.isUnit.invertible
  rw [actual_row_interval_containment_iff_the_exact_inverse_metric_bound storage hs row radius hr]
  have h := hs.fromBlocks₂₂ (actualRadiusSquareMatrix radius) (actualRowMatrix row)
  simp only [conjTranspose_eq_transpose_of_trivial] at h
  rw [actual_row_containment_schur_matrix_has_the_literal_inverse_metric_remainder,
    Matrix.posSemidef_diagonal_iff] at h
  change actualRowEnergy storage row ≤ radius^2 ↔ _
  rw [actualRowContainmentBlock,h]
  constructor
  · intro hb index; linarith
  · intro hb; have he := hb 0; linarith

theorem actual_smaller_row_interval_bound_implies_the_larger_bound
    (storage : Matrix n n ℝ) (row : n → ℝ) (small large : ℝ) (h : small ≤ large)
    (hc : ∀ vector : n → ℝ, vector ⬝ᵥ (storage *ᵥ vector) ≤ 1 → |row ⬝ᵥ vector| ≤ small) :
    ∀ vector : n → ℝ, vector ⬝ᵥ (storage *ᵥ vector) ≤ 1 → |row ⬝ᵥ vector| ≤ large :=
  fun vector hv => (hc vector hv).trans h

end SafeLearning.CompleteModulesEllipsoidRow
