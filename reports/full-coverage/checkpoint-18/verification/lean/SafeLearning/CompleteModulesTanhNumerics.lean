import SafeLearning.CompleteModulesTanhChords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace SafeLearning.CompleteModulesTanhNumerics
open CompleteModulesTanhChords

theorem actual_tanh_is_the_exponential_square_ratio (x : ℝ) :
    Real.tanh x = ((Real.exp x)^2-1)/((Real.exp x)^2+1) := by
  rw [Real.tanh_eq,Real.exp_neg]
  have hn := Real.exp_ne_zero x
  have hp : (Real.exp x)^2+1 ≠ 0 := by positivity
  field_simp <;> ring

theorem actual_tanh_one_rigorous_rational_enclosure :
    (0.7615941559:ℝ) < Real.tanh 1 ∧ Real.tanh 1 < 0.7615941561 := by
  have hl := Real.exp_one_gt_d9
  have hu := Real.exp_one_lt_d9
  have hn := Real.exp_pos 1
  have hsqL : (7.389056097:ℝ) < (Real.exp 1)^2 := by nlinarith
  have hsqU : (Real.exp 1)^2 < (7.389056100:ℝ) := by nlinarith
  rw [actual_tanh_is_the_exponential_square_ratio]
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < (Real.exp 1)^2+1)).mpr
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0 < (Real.exp 1)^2+1)).mpr
    nlinarith

theorem actual_source_tanh_increment_numerical_values_and_rounding :
    (1:ℝ)-(-1)=2 ∧ Real.tanh 1-Real.tanh (-1)=2*Real.tanh 1 ∧
    |(Real.tanh 1-Real.tanh (-1))-1.5232| < 0.00005 ∧
    |2*2*(Real.tanh 1-Real.tanh (-1))-6.093| < 0.0005 ∧
    |2*(Real.tanh 1-Real.tanh (-1))^2-4.640| < 0.0005 := by
  have hl := actual_tanh_one_rigorous_rational_enclosure.1
  have hu := actual_tanh_one_rigorous_rational_enclosure.2
  have he : Real.tanh 1-Real.tanh (-1)=2*Real.tanh 1 := by
    rw [Real.tanh_neg]; ring
  refine ⟨by norm_num,he,?_,?_,?_⟩
  · rw [he]; apply abs_lt.mpr; constructor <;> linarith
  · rw [he]; apply abs_lt.mpr; constructor <;> linarith
  · rw [he]; apply abs_lt.mpr; constructor <;> nlinarith

theorem actual_source_tanh_qc_literal_value_rounding_and_positivity :
    |(2*2*(Real.tanh 1-Real.tanh (-1))-
      2*(Real.tanh 1-Real.tanh (-1))^2)-1.453| < 0.0005 ∧
    0 ≤ 2*2*(Real.tanh 1-Real.tanh (-1))-
      2*(Real.tanh 1-Real.tanh (-1))^2 := by
  have hl := actual_tanh_one_rigorous_rational_enclosure.1
  have hu := actual_tanh_one_rigorous_rational_enclosure.2
  have he : Real.tanh 1-Real.tanh (-1)=2*Real.tanh 1 := by
    rw [Real.tanh_neg]; ring
  constructor
  · rw [he]; apply abs_lt.mpr; constructor <;> nlinarith
  · have h := actual_source_incremental_tanh_qc_is_nonnegative 1 (-1)
    rw [actual_source_incremental_tanh_qc_has_the_literal_matrix_identity] at h
    norm_num only at h ⊢
    exact h

theorem actual_source_local_origin_and_derivative_bounds_at_one_rounding :
    |Real.tanh 1-0.762| < 0.0005 ∧
    |(1-(Real.tanh 1)^2)-0.420| < 0.0005 ∧
    1-(Real.tanh 1)^2 ≤ Real.tanh 1 := by
  have hl := actual_tanh_one_rigorous_rational_enclosure.1
  have hu := actual_tanh_one_rigorous_rational_enclosure.2
  refine ⟨?_,?_,?_⟩
  · apply abs_lt.mpr; constructor <;> linarith
  · apply abs_lt.mpr; constructor <;> nlinarith
  · simpa using actual_origin_secant_lower_sector_is_at_least_the_local_derivative_bound 1 (by norm_num)

end SafeLearning.CompleteModulesTanhNumerics
