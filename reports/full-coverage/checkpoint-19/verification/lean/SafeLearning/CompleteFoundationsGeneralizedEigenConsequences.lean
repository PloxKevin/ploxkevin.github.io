import SafeLearning.CompleteFoundationsGeneralizedEigen

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SafeLearning.CompleteFoundationsGeneralizedEigenConsequences
open Matrix Set
open scoped BigOperators
open CompleteFoundationsGeneralizedEigen

theorem actual_source_metric_is_positive_definite : sourceM.PosDef := by
  have he : sourceM = Matrix.diagonal (![1,2] : Fin 2 → ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [sourceM,Matrix.diagonal_apply]
  rw [he,Matrix.posDef_diagonal_iff]
  intro i; fin_cases i <;> norm_num

theorem actual_source_positive_inverse_square_root :
    normalization.PosDef ∧ normalization * normalization = sourceM⁻¹ := by
  have he : normalization = Matrix.diagonal (![1,1/Real.sqrt 2] : Fin 2 → ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [normalization,Matrix.diagonal_apply]
  constructor
  · rw [he,Matrix.posDef_diagonal_iff]
    intro i; fin_cases i
    · norm_num
    · simp only [Matrix.cons_val_one]
      exact div_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  · rw [actual_source_normalization_square_and_inverse.1,actual_source_inverse]

theorem actual_source_inverse_metric_reward_direction :
    sourceM⁻¹ * sourceW.transpose = !![1;1/2] := by
  rw [actual_source_inverse]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [inverseM,sourceW,Matrix.transpose_apply,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_source_weighted_matrix_input_and_output (x : Fin 2 → ℝ) :
    x ⬝ᵥ (sourceM *ᵥ x) = (x 0)^2+2*(x 1)^2 ∧
    (sourceW *ᵥ x) ⬝ᵥ (sourceW *ᵥ x) = (x 0+x 1)^2 ∧
    sourceRayleigh x = ((sourceW *ᵥ x) ⬝ᵥ (sourceW *ᵥ x))/(x ⬝ᵥ (sourceM *ᵥ x)) := by
  have hm : x ⬝ᵥ (sourceM *ᵥ x) = (x 0)^2+2*(x 1)^2 := by
    simp [sourceM,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]; ring
  have hw : (sourceW *ᵥ x) ⬝ᵥ (sourceW *ᵥ x) = (x 0+x 1)^2 := by
    simp [sourceW,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]; ring
  exact ⟨hm,hw,by rw [hm,hw]; rfl⟩

theorem actual_source_largest_real_eigenvalue :
    IsGreatest {lambda : ℝ | sourceA.charpoly.eval lambda = 0} (3/2) := by
  refine ⟨(actual_source_all_real_characteristic_roots _).mpr (Or.inr rfl),?_⟩
  intro lambda hl
  rcases (actual_source_all_real_characteristic_roots lambda).mp hl with rfl | rfl <;> norm_num

theorem actual_source_gain_coefficient_iff (gainSquared : ℝ) :
    (∀ x : Fin 2 → ℝ,(sourceW *ᵥ x) ⬝ᵥ (sourceW *ᵥ x) ≤
      gainSquared*(x ⬝ᵥ (sourceM *ᵥ x))) ↔ 3/2 ≤ gainSquared := by
  constructor
  · intro h
    have hp := h (![1,1/2] : Fin 2 → ℝ)
    rw [(actual_source_weighted_matrix_input_and_output _).1,
      (actual_source_weighted_matrix_input_and_output _).2.1] at hp
    norm_num at hp
    linarith
  · intro hg x
    rw [(actual_source_weighted_matrix_input_and_output _).1,
      (actual_source_weighted_matrix_input_and_output _).2.1]
    have hsharp := actual_source_rayleigh_is_greatest_and_sharp_layer_gain.2.1 x
    exact hsharp.trans (mul_le_mul_of_nonneg_right hg (by positivity))

theorem actual_source_least_squared_matrix_gain_and_inverse_certificate :
    IsLeast {gainSquared : ℝ | 0 ≤ gainSquared ∧
      ∀ x : Fin 2 → ℝ,(sourceW *ᵥ x) ⬝ᵥ (sourceW *ᵥ x) ≤
        gainSquared*(x ⬝ᵥ (sourceM *ᵥ x))} (3/2) ∧
    (1/(2/3) : ℝ) = 3/2 := by
  refine ⟨⟨⟨by norm_num,(actual_source_gain_coefficient_iff _).mpr le_rfl⟩,?_⟩,by norm_num⟩
  intro coefficient hc
  exact (actual_source_gain_coefficient_iff coefficient).mp hc.2

end SafeLearning.CompleteFoundationsGeneralizedEigenConsequences
