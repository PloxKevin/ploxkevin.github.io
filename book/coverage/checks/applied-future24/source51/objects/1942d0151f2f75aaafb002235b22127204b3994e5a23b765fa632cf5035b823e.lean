import SafeLearning.CompleteAppliedDiscountedHorizons

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedDiscountHorizonConsequences
open SafeLearning.CompleteAppliedDiscountedHorizons

theorem actual_positive_time_constant_is_uniquely_determined
    (tau : ℝ) (ht : 0<tau) :
    Real.exp (-(1/10)/tau)=discount ↔ tau=timeConstant := by
  have hd : 0<Real.log (20/19:ℝ) := Real.log_pos (by norm_num)
  have hi : Real.log discount= -Real.log (20/19) := by
    rw [discount,show (19/20:ℝ)=(20/19)⁻¹ by norm_num,Real.log_inv]
  constructor
  · intro h
    have he := congrArg Real.log h
    rw [Real.log_exp,hi] at he
    have hm : (1/10:ℝ)=Real.log (20/19)*tau := by
      have hx := (div_eq_iff (ne_of_gt ht)).mp he
      linarith
    unfold timeConstant
    exact (eq_div_iff (ne_of_gt hd)).mpr (by linarith)
  · intro h
    subst tau
    simpa using actual_continuous_time_weight_matches_every_sampled_step 1

theorem actual_first_strict_one_percent_horizon_is_also_ninety (T : ℕ) :
    discount^T<1/100 ↔ 90≤T := by
  constructor
  · intro h
    exact (actual_first_integer_one_percent_horizon_is_ninety T).mp h.le
  · intro h
    exact (pow_le_pow_of_le_one (by norm_num [discount] : (0:ℝ)≤discount)
      (by norm_num [discount] : discount≤1) h).trans_lt
      actual_discount_powers_eighty_nine_and_ninety_have_rigorous_rounding.2.1

theorem actual_source_log_displays_are_rounded_values :
    |Real.log 100-46052/10000|<1/20000 ∧
      |Real.log (20/19)-5129/100000|<1/200000 ∧
      Real.log 100≠46052/10000 ∧ Real.log (20/19)≠5129/100000 := by
  obtain ⟨hl,hu,h100l,h100u⟩ := actual_discount_log_enclosure_and_log_hundred_enclosure
  refine ⟨?_,?_,?_,?_⟩
  · rw [abs_lt]
    constructor <;> linarith
  · rw [abs_lt]
    constructor <;> linarith
  · intro h
    linarith
  · intro h
    linarith

theorem actual_true_threshold_and_time_constant_are_not_the_source_decimal_identities :
    Real.log 100/Real.log (20/19)≠898/10 ∧ timeConstant≠195/100 ∧
      discount^89≠104/10000 ∧ discount^90≠99/10000 ∧
      40*discount^90≠40/100 ∧ (99/10000:ℝ)*40=396/1000 := by
  obtain ⟨hl,hu,h100l,h100u⟩ := actual_discount_log_enclosure_and_log_hundred_enclosure
  have hd : 0<Real.log (20/19:ℝ) := by linarith
  refine ⟨?_,?_,by norm_num [discount],by norm_num [discount],
    by norm_num [discount],by norm_num⟩
  · intro h
    have he := (div_eq_iff (ne_of_gt hd)).mp h
    linarith
  · intro h
    unfold timeConstant at h
    have he := (div_eq_iff (ne_of_gt hd)).mp h
    linarith

theorem actual_one_percent_threshold_is_about_four_point_six_time_constants :
    |Real.log 100-46/10|<1/20 := by
  obtain ⟨_,_,hl,hu⟩ := actual_discount_log_enclosure_and_log_hundred_enclosure
  rw [abs_lt]
  constructor <;> linarith

end SafeLearning.CompleteAppliedDiscountHorizonConsequences
