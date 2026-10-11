import SafeLearning.CompleteModulesSingularSchurPractice

set_option autoImplicit false
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesSingularSchurWitness
open CompleteModulesSingularSchurPractice

def actualOppositeSignWitness (a b : ℝ) : ℝ := -(|a|+1)/(2*b)

theorem actual_source_off_diagonal_witness_has_opposite_sign_and_sufficient_magnitude
    (a b : ℝ) (hb : b≠0) :
    b*actualOppositeSignWitness a b<0 ∧
    |a|/(2*|b|) < |actualOppositeSignWitness a b| := by
  have he : b*actualOppositeSignWitness a b=-(|a|+1)/2 := by
    unfold actualOppositeSignWitness
    field_simp <;> ring
  refine ⟨by rw [he];linarith [abs_nonneg a],?_⟩
  unfold actualOppositeSignWitness
  rw [abs_div,abs_neg,abs_of_pos (show 0 < |a|+1 by linarith [abs_nonneg a]),abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (div_lt_div_iff_of_pos_right (mul_pos (by norm_num) (abs_pos.mpr hb))).mpr
    (by linarith)

theorem actual_source_opposite_sign_large_witness_has_a_negative_true_matrix_quadratic
    (a b : ℝ) (hb : b≠0) :
    (![1,actualOppositeSignWitness a b] : Fin 2→ℝ) ⬝ᵥ
      (actualSingularCornerMatrix a b *ᵥ ![1,actualOppositeSignWitness a b])=
      a-|a|-1 ∧ a-|a|-1<0 := by
  refine ⟨?_,by linarith [le_abs_self a]⟩
  rw [actual_singular_corner_test_at_one_and_arbitrary_t]
  unfold actualOppositeSignWitness
  field_simp
  ring

end SafeLearning.CompleteModulesSingularSchurWitness
