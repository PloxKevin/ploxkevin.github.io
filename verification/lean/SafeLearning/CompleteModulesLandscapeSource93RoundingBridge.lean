import SafeLearning.CompleteModulesGaussianTailRounding
import SafeLearning.CompleteModulesLandscapeSource91ARPartII

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SafeLearning.CompleteModulesLandscapeSource93RoundingBridge
open CompleteModulesGaussianTailRounding CompleteModulesGaussianErfcTail
open CompleteModulesLandscapeARGaussianAlgebra CompleteModulesLandscapeARViolationCounts
open CompleteModulesLandscapeARPathFluctuation CompleteModulesLandscapeSource91ARPartII

/-! The same rounding model applied to the printed marginal sum. The sums
themselves are real sums of rounded terms; the counterexample uses T=1, so it
requires no further model of summation error. Parameters satisfy 0<k<2 and
sigma>0. No claim about the fixed parameter example in part (iii) is made. -/

def cdfCount (k goal sigma : ℝ) (T : ℕ) : ℝ :=
  ∑ t : Fin T, cdfSubtraction
    ((1-trueMean k goal (t.val+1))/Real.sqrt (trueVariance k sigma (t.val+1)))

def directCount (k goal sigma : ℝ) (T : ℕ) : ℝ :=
  ∑ t : Fin T, directTail
    ((1-trueMean k goal (t.val+1))/Real.sqrt (trueVariance k sigma (t.val+1)))

theorem actual_one_step_parameters_have_the_prescribed_standardized_threshold (z : ℝ) :
    trueMean (1/2) (2*(1-z)) 1 = 1-z ∧ trueVariance (1/2) 1 1 = 1 ∧
      (1-trueMean (1/2) (2*(1-z)) 1)/Real.sqrt (trueVariance (1/2) 1 1) = z := by
  norm_num [trueMean, trueVariance]
  constructor <;> ring

theorem actual_one_step_expected_count_is_the_true_gaussian_tail (z : ℝ) :
    (∫ w, infiniteViolationCount (1/2) (2*(1-z)) 1 1 w ∂infiniteNoiseLaw) = upperTail z := by
  rw [actual_one_to_T_infinite_count_expectation_is_the_printed_piecewise_tail_sum]
  simp only [Fin.sum_univ_one, Fin.val_zero, zero_add, exactTail, one_ne_zero, ite_false]
  rw [(actual_one_step_parameters_have_the_prescribed_standardized_threshold z).2.2]
  exact (actual_standard_gaussian_upper_tail_is_the_cdf_complement_and_density_integral z).1.symm

theorem actual_one_step_rounded_count_formulas_use_that_same_threshold (z : ℝ) :
    cdfCount (1/2) (2*(1-z)) 1 1 = cdfSubtraction z ∧
      directCount (1/2) (2*(1-z)) 1 1 = directTail z := by
  simp only [cdfCount, directCount, Fin.sum_univ_one, Fin.val_zero, zero_add]
  rw [(actual_one_step_parameters_have_the_prescribed_standardized_threshold z).2.2]
  exact ⟨rfl, rfl⟩

theorem actual_source_expected_count_can_be_positive_while_its_cdf_evaluation_is_zero :
    ∃ goal : ℝ,
      (∫ w, infiniteViolationCount (1/2) goal 1 1 w ∂infiniteNoiseLaw) = (2:ℝ)^(-60:ℤ) ∧
      0 < (∫ w, infiniteViolationCount (1/2) goal 1 1 w ∂infiniteNoiseLaw) ∧
      cdfCount (1/2) goal 1 1 = 0 ∧ directCount (1/2) goal 1 1 = (2:ℝ)^(-60:ℤ) := by
  rcases actual_direct_tail_can_retain_a_positive_value_lost_by_cdf_subtraction with
    ⟨z, _, htail, _, hzero, hdirect, _⟩
  refine ⟨2*(1-z), ?_, ?_, ?_, ?_⟩
  · rw [actual_one_step_expected_count_is_the_true_gaussian_tail, htail]
  · rw [actual_one_step_expected_count_is_the_true_gaussian_tail, htail]
    positivity
  · rw [(actual_one_step_rounded_count_formulas_use_that_same_threshold z).1, hzero]
  · rw [(actual_one_step_rounded_count_formulas_use_that_same_threshold z).2, hdirect]

end SafeLearning.CompleteModulesLandscapeSource93RoundingBridge
