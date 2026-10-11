import SafeLearning.CompleteModulesDesignEasyMatrices
import SafeLearning.CompleteModulesLipSDP

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesDesignCoupledDirections
open CompleteModulesDesignEasyMatrices

def sourceFirst : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![4,1/4]
def sourceLast : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1/4,4]
def sourceStorage : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1/16,16]

theorem actual_source_ordinary_norm_product_and_composite_norm :
    ‖sourceFirst‖=4 ∧ ‖sourceLast‖=4 ∧ ‖sourceFirst‖*‖sourceLast‖=16 ∧
      sourceLast*sourceFirst=1 ∧ ‖sourceLast*sourceFirst‖=1 := by
  have h0 : ‖sourceFirst‖=4 := by
    simpa [sourceFirst] using actual_positive_diagonal_operator_norm_is_the_largest_entry
      4 (1/4) (by norm_num) (by norm_num)
  have h1 : ‖sourceLast‖=4 := by
    simpa [sourceLast] using actual_positive_diagonal_operator_norm_is_the_largest_entry
      (1/4) 4 (by norm_num) (by norm_num)
  have hp : sourceLast*sourceFirst=1 := by
    ext i j;fin_cases i <;>fin_cases j <;>norm_num [sourceFirst,sourceLast,
      Matrix.mul_apply,Fin.sum_univ_two,diagonal_apply,Matrix.one_apply]
  exact ⟨h0,h1,by rw [h0,h1];norm_num,hp,by rw [hp];simp⟩

theorem actual_source_weighted_certificates_and_positive_storage :
    sourceStorage.PosDef ∧ sourceFirstᵀ*sourceStorage*sourceFirst=1 ∧
      sourceLastᵀ*sourceLast=sourceStorage ∧
      ((1:Matrix (Fin 2) (Fin 2) ℝ)-sourceFirstᵀ*sourceStorage*sourceFirst).PosSemidef ∧
      (sourceStorage-sourceLastᵀ*sourceLast).PosSemidef := by
  have h0 : sourceFirstᵀ*sourceStorage*sourceFirst=1 := by
    ext i j;fin_cases i <;>fin_cases j <;>norm_num [sourceFirst,sourceStorage,
      Matrix.mul_apply,Fin.sum_univ_two,diagonal_apply,Matrix.one_apply]
  have h1 : sourceLastᵀ*sourceLast=sourceStorage := by
    ext i j;fin_cases i <;>fin_cases j <;>norm_num [sourceLast,sourceStorage,
      Matrix.mul_apply,Fin.sum_univ_two,diagonal_apply]
  refine ⟨?_,h0,h1,?_,?_⟩
  · rw [sourceStorage,Matrix.posDef_diagonal_iff]
    intro i;fin_cases i <;>norm_num
  · rw [h0,sub_self];exact Matrix.PosSemidef.zero
  · rw [h1,sub_self];exact Matrix.PosSemidef.zero

theorem actual_source_all_input_weighted_and_output_energies_match (input : Fin 2 → ℝ) :
    (sourceFirst *ᵥ input) ⬝ᵥ (sourceStorage *ᵥ (sourceFirst *ᵥ input))=
      ‖WithLp.toLp 2 input‖^2 ∧
      ‖WithLp.toLp 2 (sourceLast *ᵥ (sourceFirst *ᵥ input))‖=
        ‖WithLp.toLp 2 input‖ := by
  constructor
  · rw [EuclideanSpace.real_norm_sq_eq]
    simp [sourceFirst,sourceStorage,Matrix.mulVec_diagonal,dotProduct,Fin.sum_univ_two]
    ring
  · rw [Matrix.mulVec_mulVec,actual_source_ordinary_norm_product_and_composite_norm.2.2.2.1,
      Matrix.one_mulVec]

theorem actual_identity_activation_has_the_source_unit_interval_slopes :
    CompleteModulesLipSDP.slopeRestricted (fun x : ℝ=>x) 0 1 := by
  intro x y
  exact ⟨1,by norm_num,le_rfl,by ring⟩

theorem actual_source_weights_are_excluded_by_separate_unit_norm_constraints :
    ¬(‖sourceFirst‖≤1) ∧ ¬(‖sourceLast‖≤1) := by
  rw [actual_source_ordinary_norm_product_and_composite_norm.1,
    actual_source_ordinary_norm_product_and_composite_norm.2.1]
  norm_num

end SafeLearning.CompleteModulesDesignCoupledDirections
