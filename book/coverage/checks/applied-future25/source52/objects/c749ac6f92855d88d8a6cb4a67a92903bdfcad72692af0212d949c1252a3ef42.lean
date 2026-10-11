import SafeLearning.CompleteAppliedInformationExamples
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedInformationPrecision
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedInformationExamples SafeLearning.CompleteAppliedInformation
open SafeLearning.CompleteAppliedValidationNumbers
open scoped ENNReal

theorem actual_source_six_log_summand_roundings :
    |(3/5:ℝ)*Real.log (3/2)-2433/10000|<1/20000 ∧
    |(3/10:ℝ)*Real.log (3/4)+863/10000|<1/20000 ∧
    |(1/10:ℝ)*Real.log (1/2)+693/10000|<1/20000 ∧
    |(2/5:ℝ)*Real.log (2/3)+1622/10000|<1/20000 ∧
    |(2/5:ℝ)*Real.log (4/3)-1151/10000|<1/20000 ∧
    |(1/5:ℝ)*Real.log 2-1386/10000|<1/20000 := by
  norm_num [Real.log_div,Real.log_four_eq]
  have h2l:=Real.log_two_gt_d9
  have h2u:=Real.log_two_lt_d9
  have h3l:=Real.log_three_gt_d9
  have h3u:=Real.log_three_lt_d9
  repeat' constructor
  all_goals rw [abs_lt]; constructor <;> linarith

theorem actual_source_KL_decimals_are_strict_approximations :
    (klDiv pLaw.toMeasure qLaw.toMeasure).toReal<(877/10000:ℝ) ∧
    (915/10000:ℝ)<(klDiv qLaw.toMeasure pLaw.toMeasure).toReal ∧
    (164/1000:ℝ)<(klDiv excludedLaw.toMeasure pLaw.toMeasure).toReal := by
  rw [actual_source_directional_log_forms.1,actual_source_directional_log_forms.2,
    actual_reverse_excluded_law_KL.1]
  have h6:Real.log (6:ℝ)=Real.log 2+Real.log 3 := by
    rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  have h20:Real.log (20:ℝ)=2*Real.log 2+Real.log 5 := by
    rw [show (20:ℝ)=4*5 by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_four_eq]
  norm_num [Real.log_div] at *
  rw [h6]
  obtain ⟨h20l,h20u⟩:=log20_enclosure
  have h2l:=Real.log_two_gt_d9
  have h2u:=Real.log_two_lt_d9
  have h3l:=Real.log_three_gt_d9
  have h3u:=Real.log_three_lt_d9
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem actual_source_rounded_input_square_root_approximations :
    |Real.sqrt ((877/10000:ℝ)/2)-209/1000|<1/2000 ∧
    |Real.sqrt ((915/10000:ℝ)/2)-214/1000|<1/2000 ∧
    (209/1000:ℝ)<Real.sqrt ((877/10000:ℝ)/2) ∧
    Real.sqrt ((915/10000:ℝ)/2)<(214/1000:ℝ) ∧
    (1/5:ℝ)≤Real.sqrt ((877/10000:ℝ)/2) ∧
    (1/5:ℝ)≤Real.sqrt ((915/10000:ℝ)/2) := by
  have hf:=Real.sq_sqrt (by norm_num : 0≤(877/10000:ℝ)/2)
  have hr:=Real.sq_sqrt (by norm_num : 0≤(915/10000:ℝ)/2)
  have hfn:=Real.sqrt_nonneg ((877/10000:ℝ)/2)
  have hrn:=Real.sqrt_nonneg ((915/10000:ℝ)/2)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [abs_lt];constructor <;> nlinarith
  · rw [abs_lt];constructor <;> nlinarith
  all_goals nlinarith

theorem actual_source_pinsker_small_positive_gaps :
    0≤Real.sqrt ((klDiv pLaw.toMeasure qLaw.toMeasure).toReal/2)-totalVariation pLaw qLaw ∧
    Real.sqrt ((klDiv pLaw.toMeasure qLaw.toMeasure).toReal/2)-totalVariation pLaw qLaw<3/200 ∧
    0≤Real.sqrt ((klDiv qLaw.toMeasure pLaw.toMeasure).toReal/2)-totalVariation pLaw qLaw ∧
    Real.sqrt ((klDiv qLaw.toMeasure pLaw.toMeasure).toReal/2)-totalVariation pLaw qLaw<3/200 := by
  have htv:=actual_source_total_variation
  have hp:=actual_source_pinsker_both_directions
  have hr:=actual_source_sqrt_KL_rounding
  rw [SafeLearning.CompleteAppliedFiniteVariation.actual_finite_tv_symmetric qLaw pLaw] at hp
  obtain ⟨hfl,hfu⟩:=abs_lt.mp hr.1
  obtain ⟨hrl,hru⟩:=abs_lt.mp hr.2
  rw [htv] at *
  refine ⟨by linarith [hp.1],by linarith,by linarith [hp.2],by linarith⟩

end SafeLearning.CompleteAppliedInformationPrecision
