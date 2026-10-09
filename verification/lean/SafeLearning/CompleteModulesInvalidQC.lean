import SafeLearning.CompleteModulesDiagonalQC

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesInvalidQC

open CompleteModulesLipSDP CompleteModulesLipSDPNetwork CompleteModulesDiagonalQC

def coupledMultiplier : Matrix (Fin 2) (Fin 2) ℝ := !![1,-1;-1,1]
def reluVector (input : Fin 2 → ℝ) : Fin 2 → ℝ := fun k => max (input k) 0
def coupledIncrementQC (first second : Fin 2 → ℝ) : ℝ :=
  2*((reluVector first-reluVector second) ⬝ᵥ
    (coupledMultiplier *ᵥ (first-second-(reluVector first-reluVector second))))

theorem coupled_multiplier_is_positive_semidefinite : coupledMultiplier.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [coupledMultiplier,Matrix.conjTranspose_apply]
  · intro vector
    simp only [star_trivial]
    have he : vector ⬝ᵥ (coupledMultiplier *ᵥ vector)=(vector 0-vector 1)^2 := by
      simp [coupledMultiplier,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      ring
    rw [he]
    exact sq_nonneg _

theorem coupled_multiplier_exact_eigenvalues (value : ℝ) :
    Matrix.det (coupledMultiplier-value • (1 : Matrix (Fin 2) (Fin 2) ℝ))=0 ↔
      value=0 ∨ value=2 := by
  have he : Matrix.det (coupledMultiplier-value • (1 : Matrix (Fin 2) (Fin 2) ℝ))=
      value*(value-2) := by
    simp [coupledMultiplier,Matrix.det_fin_two,Matrix.sub_apply,Matrix.smul_apply]
    ring
  rw [he,mul_eq_zero,sub_eq_zero]

theorem actual_book_coupled_relu_failure :
    coupledIncrementQC (![2,-2] : Fin 2 → ℝ) (![1,-3] : Fin 2 → ℝ) = -2 := by
  norm_num [coupledIncrementQC,reluVector,coupledMultiplier,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_paper_coupled_relu_failure :
    coupledIncrementQC (![0,1] : Fin 2 → ℝ) (![-3/2,0] : Fin 2 → ℝ) = -3 := by
  norm_num [coupledIncrementQC,reluVector,coupledMultiplier,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem positive_semidefiniteness_does_not_make_coupled_qc_valid :
    coupledMultiplier.PosSemidef ∧
      ¬ ∀ first second : Fin 2 → ℝ, 0 ≤ coupledIncrementQC first second := by
  refine ⟨coupled_multiplier_is_positive_semidefinite,?_⟩
  intro h
  have hc := h (![2,-2] : Fin 2 → ℝ) (![1,-3] : Fin 2 → ℝ)
  rw [actual_book_coupled_relu_failure] at hc
  norm_num at hc

theorem scalar_qc_practice_values :
    scalarQC 0 1 2 1=2 ∧ scalarQC 0 1 2 3= -6 ∧ scalarQC 0 1 2 (-1)= -6 := by
  norm_num [scalarQC]

theorem scalar_practice_admissible_pairs :
    (∃ slope : ℝ, 0 ≤ slope ∧ slope ≤ 1 ∧ (1:ℝ)=slope*2) ∧
    ¬ (∃ slope : ℝ, 0 ≤ slope ∧ slope ≤ 1 ∧ (3:ℝ)=slope*2) ∧
    ¬ (∃ slope : ℝ, 0 ≤ slope ∧ slope ≤ 1 ∧ (-1:ℝ)=slope*2) := by
  constructor
  · exact ⟨1/2,by norm_num,by norm_num,by norm_num⟩
  constructor <;> rintro ⟨slope,hl,hu,he⟩ <;> linarith

theorem diagonal_practice_sum_is_nine :
    diagonalQC 0 1 (![3,2] : Fin 2 → ℝ) ![2,-2] ![1,-1/2]=9 := by
  norm_num [diagonalQC,scalarQC,Fin.sum_univ_two]

theorem negative_weight_invalidates_positive_scalar_qc :
    0 ≤ scalarQC 0 1 2 1 ∧ (-1:ℝ)*scalarQC 0 1 2 1 < 0 := by
  norm_num [scalarQC]

def discontinuousSectorActivation (value : ℝ) : ℝ := if value < 1 then 0 else value

theorem actual_slope_restriction_implies_sector (activation : ℝ → ℝ) (alpha beta : ℝ)
    (hactivation : slopeRestricted activation alpha beta) (horigin : activation 0=0) :
    ∀ input : ℝ, 0 ≤ scalarQC alpha beta input (activation input) := by
  intro input
  simpa [scalarQC,horigin] using
    scalar_slope_quadratic_constraint activation alpha beta hactivation input 0

theorem discontinuous_activation_obeys_sector :
    discontinuousSectorActivation 0=0 ∧
      ∀ input : ℝ, 0 ≤ scalarQC 0 1 input (discontinuousSectorActivation input) := by
  constructor
  · norm_num [discontinuousSectorActivation]
  · intro input
    unfold discontinuousSectorActivation
    split_ifs <;> simp [scalarQC] <;> nlinarith

theorem actual_sector_bound_does_not_imply_slope_restriction :
    ¬ slopeRestricted discontinuousSectorActivation 0 1 := by
  intro h
  obtain ⟨slope,hl,hu,he⟩ := h 1 (9/10)
  norm_num [discontinuousSectorActivation] at he
  linarith

end SafeLearning.CompleteModulesInvalidQC
