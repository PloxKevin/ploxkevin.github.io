import SafeLearning.CompleteChowLP21

noncomputable section
namespace SafeLearning.CompleteChowTransience21
open Matrix SafeLearning.CompleteChowLP21

theorem actual_mixed_fundamental_is_a_left_inverse (p : ℝ) :
    (1-fastTransition p)*mixedFundamental p=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mixedFundamental,fastTransition,pow_two,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply,Matrix.sub_apply] <;> ring

theorem actual_mixed_fundamental_is_a_right_inverse (p : ℝ) :
    mixedFundamental p*(1-fastTransition p)=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mixedFundamental,fastTransition,pow_two,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply,Matrix.sub_apply] <;> ring

theorem actual_every_mixed_transient_matrix_has_a_true_inverse (p : ℝ) :
    IsUnit (1-fastTransition p) := by
  exact ⟨⟨1-fastTransition p,mixedFundamental p,
    actual_mixed_fundamental_is_a_left_inverse p,
    actual_mixed_fundamental_is_a_right_inverse p⟩,rfl⟩

theorem actual_every_full_bellman_solution_is_the_fundamental_cost_vector
    (p : ℝ) (cost value : Fin 3 → ℝ)
    (he : value=cost+(fastTransition p).mulVec value) :
    (mixedFundamental p).mulVec cost=value := by
  have hc : (1-fastTransition p).mulVec value=cost := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec]
    exact sub_eq_iff_eq_add.mpr he
  rw [←hc,Matrix.mulVec_mulVec,
    actual_mixed_fundamental_is_a_right_inverse,Matrix.one_mulVec]

end SafeLearning.CompleteChowTransience21
