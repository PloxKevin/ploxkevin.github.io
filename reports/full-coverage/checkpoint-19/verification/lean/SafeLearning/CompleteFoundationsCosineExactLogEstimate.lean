import SafeLearning.CompleteFoundationsCosineLogarithms
import SafeLearning.CompleteFoundationsCosineErrorBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
noncomputable section
namespace SafeLearning.CompleteFoundationsCosineExactLogEstimate
open SafeLearning.CompleteFoundationsCosineContraction
open SafeLearning.CompleteFoundationsCosineNumerics
open SafeLearning.CompleteFoundationsCosineErrorBounds
open SafeLearning.CompleteFoundationsCosineLogarithms

theorem actual_numerator_lower_log_certificate : (1488014000/100000000:ℝ)<Real.log (2899770:ℝ) := by
  apply actual_log_lower_from_negative_exponential_series (2899770) (1488014000/100000000:ℝ) (394550258040/1000000000000)
    (by norm_num) (by norm_num) (by norm_num)
  · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
  · norm_num

theorem actual_numerator_upper_log_certificate : Real.log (2899771:ℝ)<(1488015000/100000000:ℝ) := by
  apply actual_log_upper_from_negative_exponential_series (2899771) (1488015000/100000000:ℝ) (394550011449/1000000000000)
    (by norm_num) (by norm_num)
  · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
  · norm_num

theorem actual_denominator_lower_log_certificate : (17260374/100000000:ℝ)<Real.log (10000000000/8414709849:ℝ) := by
  apply actual_log_lower_from_negative_exponential_series (10000000000/8414709849) (17260374/100000000:ℝ) (989270245174/1000000000000)
    (by norm_num) (by norm_num) (by norm_num)
  · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
  · norm_num

theorem actual_denominator_upper_log_certificate : Real.log (10000000000/8414709847:ℝ)<(17260376/100000000:ℝ) := by
  apply actual_log_upper_from_negative_exponential_series (10000000000/8414709847) (17260376/100000000:ℝ) (989270243940/1000000000000)
    (by norm_num) (by norm_num)
  · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
  · norm_num

def actualNumerator : ℝ := apriori 0*1000000

theorem actual_unrounded_apriori_log_argument_enclosures :
    (2899770:ℝ)<actualNumerator ∧ actualNumerator<2899771 ∧
      (10000000000/8414709849:ℝ)<1/Real.sin 1 ∧
      1/Real.sin 1<10000000000/8414709847 := by
  have h := actual_apriori_rational_sandwich 0
  norm_num [lowerApriori,upperApriori] at h
  have hs := actual_sine_one_and_cosine_one_certified_enclosures
  have hp := actual_sine_one_strict_contraction_range.1
  constructor
  · unfold actualNumerator
    linarith [h.1]
  constructor
  · unfold actualNumerator
    linarith [h.2]
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2.1]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

def actualLogThreshold : ℝ := Real.log actualNumerator/Real.log (1/Real.sin 1)

theorem actual_unrounded_logarithmic_threshold_rounds_to_eighty_six_point_two :
    |actualLogThreshold-(862/10:ℝ)|<1/20 := by
  have ha := actual_unrounded_apriori_log_argument_enclosures
  have hnlo := (actual_numerator_lower_log_certificate.trans_le
    (Real.log_le_log (by norm_num) ha.1.le))
  have hnhi := (Real.log_le_log (by linarith [ha.1] : 0<actualNumerator) ha.2.1.le).trans_lt
    actual_numerator_upper_log_certificate
  have hdlo := (actual_denominator_lower_log_certificate.trans_le
    (Real.log_le_log (by norm_num) ha.2.2.1.le))
  have hdhi := (Real.log_le_log (one_div_pos.mpr actual_sine_one_strict_contraction_range.1 : 0<1/Real.sin 1) ha.2.2.2.le).trans_lt
    actual_denominator_upper_log_certificate
  have hdpos : 0<Real.log (1/Real.sin 1) := by linarith [hdlo]
  unfold actualLogThreshold
  rw [abs_lt]
  constructor
  · have h : (8615/100:ℝ)<Real.log actualNumerator/Real.log (1/Real.sin 1) := by
      apply (lt_div_iff₀ hdpos).mpr
      nlinarith [hnlo,hdhi]
    linarith
  · have h : Real.log actualNumerator/Real.log (1/Real.sin 1)<(8625/100:ℝ) := by
      apply (div_lt_iff₀ hdpos).mpr
      nlinarith [hnhi,hdlo]
    linarith

theorem actual_threshold_is_the_literal_exact_formula :
    actualLogThreshold=Real.log ((1-Real.cos 1)/((1-Real.sin 1)*(1/1000000)))/
      Real.log (1/Real.sin 1) := by
  unfold actualLogThreshold
  congr 2
  unfold actualNumerator apriori
  simp only [pow_zero,mul_one,div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

end SafeLearning.CompleteFoundationsCosineExactLogEstimate
