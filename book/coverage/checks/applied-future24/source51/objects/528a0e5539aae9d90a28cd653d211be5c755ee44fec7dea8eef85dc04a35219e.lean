import SafeLearning.CompleteAppliedMonteCarloEstimate
import SafeLearning.CompleteAppliedValidationNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
noncomputable section
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedMonteCarloEstimate
open SafeLearning.CompleteAppliedZeroConfidence
namespace SafeLearning.CompleteAppliedMonteCarloNumbers

theorem actual_standard_error_has_a_certified_decimal_enclosure :
    (451/25000:ℝ)<plugInStandardError (7/100) 200 ∧
    plugInStandardError (7/100) 200<(361/20000:ℝ) := by
  have he : plugInStandardError (7/100) 200=Real.sqrt (651/2000000) := by
    norm_num [plugInStandardError]
  rw [he]
  have hs : (Real.sqrt (651/2000000))^2=(651/2000000:ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (651/2000000)
  constructor <;> nlinarith

theorem actual_standard_error_rounds_to_point_zero_one_eight_zero_but_is_not_equal_to_it :
    |plugInStandardError (7/100) 200-(9/500:ℝ)|≤1/20000 ∧
    (9/500:ℝ)<plugInStandardError (7/100) 200 := by
  obtain ⟨hl,hu⟩ := actual_standard_error_has_a_certified_decimal_enclosure
  constructor
  · rw [abs_le];constructor <;> linarith
  · linarith

theorem actual_normal_approximation_interval_endpoints_have_the_literal_nearest_three_displays :
    |(7/100-(49/25)*plugInStandardError (7/100) 200)-(35/1000:ℝ)|≤1/2000 ∧
    |(7/100+(49/25)*plugInStandardError (7/100) 200)-(105/1000:ℝ)|≤1/2000 ∧
    (7/100-(49/25)*plugInStandardError (7/100) 200)<(35/1000:ℝ) ∧
    (105/1000:ℝ)<7/100+(49/25)*plugInStandardError (7/100) 200 := by
  obtain ⟨hl,hu⟩ := actual_standard_error_has_a_certified_decimal_enclosure
  refine ⟨?_,?_,?_,?_⟩
  · rw [abs_le];constructor <;> linarith
  · rw [abs_le];constructor <;> linarith
  · linarith
  · linarith

theorem actual_rounded_standard_error_input_has_distinct_exact_interval_endpoints :
    (7/100-(49/25)*(9/500):ℝ)=217/6250 ∧
    (7/100+(49/25)*(9/500):ℝ)=658/6250 ∧
    (217/6250:ℝ)≠35/1000 ∧ (658/6250:ℝ)≠105/1000 ∧
    |(217/6250:ℝ)-35/1000|≤1/2000 ∧
    |(658/6250:ℝ)-105/1000|≤1/2000 := by norm_num

theorem actual_two_hundred_clean_limit_has_the_certified_strict_enclosure :
    (297/20000:ℝ)<zeroUpperLimit 200 (1/20) ∧
    zeroUpperLimit 200 (1/20)<(149/10000:ℝ) := by
  constructor
  · have hbad : ¬(1-(297/20000:ℝ))^200≤(1/20:ℝ) := by norm_num
    exact not_le.mp (fun h => hbad ((zero_probability_inversion 200 (by norm_num)
      (1/20) _ (by norm_num) (by norm_num)).mpr h))
  · exact (zero_probability_strict_inversion 200 (by norm_num) (1/20) _
      (by norm_num) (by norm_num)).mp (by norm_num)

theorem actual_two_hundred_clean_limit_rounds_to_point_zero_one_four_nine_and_is_below_one_point_five_percent :
    |zeroUpperLimit 200 (1/20)-(149/10000:ℝ)|≤1/20000 ∧
    zeroUpperLimit 200 (1/20)≠(149/10000:ℝ) ∧
    zeroUpperLimit 200 (1/20)<(3/200:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_two_hundred_clean_limit_has_the_certified_strict_enclosure
  refine ⟨?_,ne_of_lt hu,?_⟩
  · rw [abs_le];constructor <;> linarith
  · linarith

theorem actual_log_twenty_is_a_certified_approximation_to_three :
    |Real.log 20-(3:ℝ)|<1/100 ∧ Real.log 20<(3:ℝ) := by
  obtain ⟨hl,hu⟩ := SafeLearning.CompleteAppliedValidationNumbers.log20_enclosure
  constructor
  · rw [abs_lt];constructor <;> linarith
  · linarith

theorem actual_clean_episode_reporting_implies_the_population_is_below_one_point_five_percent_with_repeated_confidence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 200 → Ω → ℝ) (p : unitInterval) (hInd : iIndepFun X μ)
    (hm : ∀ i,Measurable (X i))
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    19/20≤μ.real {omega | (∀ i,X i omega=0) → (p:ℝ)<3/200} := by
  apply (actual_two_hundred_episode_zero_only_reporting_has_repeated_ninety_five_percent_confidence
    μ X p hInd hm hLaw).trans
  refine measureReal_mono ?_ (by finiteness)
  intro omega hconfidence hclean
  have he : zeroOnlyUpperReport 200 X (1/20) omega=zeroUpperLimit 200 (1/20) := by
    simp only [zeroOnlyUpperReport,ite_eq_left hclean]
  change (p:ℝ)≤zeroOnlyUpperReport 200 X (1/20) omega at hconfidence
  rw [he] at hconfidence
  exact hconfidence.trans_lt
    actual_two_hundred_clean_limit_rounds_to_point_zero_one_four_nine_and_is_below_one_point_five_percent.2.2

end SafeLearning.CompleteAppliedMonteCarloNumbers
