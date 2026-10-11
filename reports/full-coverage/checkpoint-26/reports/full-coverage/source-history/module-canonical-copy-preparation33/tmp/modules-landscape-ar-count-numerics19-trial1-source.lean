import SafeLearning.CompleteModulesLandscapeARTailTable
import SafeLearning.CompleteModulesLandscapeARViolationCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeARCountNumerics
open CompleteAppliedGaussianCDF CompleteAppliedGaussianTailIntegral
open CompleteModulesGaussianTailNumericalBounds CompleteModulesLandscapeARTailTable
open CompleteModulesLandscapeARViolationCounts CompleteModulesLandscapeARGaussianLaw

def exactExpected : ℝ := ∑t : Fin 40, literalTail (t.val+1)

theorem actual_first_state_has_exact_mean_point_four_standard_deviation_point_one_and_threshold_six :
    literalTail 1 = 1-standardCDF 6 := by
  have hs : Real.sqrt (1/100:ℝ) = 1/10 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/100)
    have hn := Real.sqrt_nonneg (1/100:ℝ)
    nlinarith
  norm_num [literalTail,numeratorQ,varianceQ]
  rw [hs]
  norm_num

theorem actual_first_gaussian_tail_is_strictly_positive_and_rounds_to_four_decimal_zero :
    0 < literalTail 1 ∧ literalTail 1 < 1/20000 := by
  rw [actual_first_state_has_exact_mean_point_four_standard_deviation_point_one_and_threshold_six]
  have hp : 0 < (gaussianReal 0 1).real (Ioi (6:ℝ)) := by
    have hz : (gaussianReal 0 1) (Ioi (6:ℝ)) ≠ 0 := by
      intro hzero
      have hv := gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:NNReal) ≠ 0) hzero
      simp only [Real.volume_Ioi] at hv
      exact ENNReal.top_ne_zero hv
    exact ENNReal.toReal_pos hz (measure_ne_top _ _)
  have he := measureReal_compl (μ := gaussianReal 0 1) (s := Iic (6:ℝ)) measurableSet_Iic
  have hU : (gaussianReal 0 1).real univ = 1 := by simp
  rw [compl_Iic,hU] at he
  change (gaussianReal 0 1).real (Ioi (6:ℝ)) = 1-standardCDF 6 at he
  have hfour : 1-standardCDF 4 < 1/20000 := by
    apply (actual_rational_polynomial_bounds_control_the_true_gaussian_upper_tail
      4 0 (1/20000) (by norm_num) ?_ ?_ ?_).2 <;>
      norm_num [actualTailPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  exact ⟨by rwa [he] at hp,
    (actual_gaussian_upper_tail_is_antitone (by norm_num : (4:ℝ) ≤ 6)).trans_lt hfour⟩

theorem actual_transient_lower_and_upper_rational_probability_sums_are_exact :
    (∑t : Fin 39, probLower t) = (29683/20000:ℚ) ∧
    (∑t : Fin 39, probUpper t) = (296861/200000:ℚ) := by
  decide +kernel

theorem actual_expected_forty_step_count_has_a_true_enclosure_and_three_decimal_rounding :
    (29683/20000:ℝ) < exactExpected ∧ exactExpected < 296871/200000 ∧
      |exactExpected-(1484/1000:ℝ)| < 1/2000 ∧ exactExpected ≠ (1484/1000:ℝ) := by
  have hp1 := actual_first_gaussian_tail_is_strictly_positive_and_rounds_to_four_decimal_zero
  have hsL : (∑t : Fin 39, (probLower t:ℝ)) < ∑t : Fin 39, literalTail (t.val+2) := by
    apply Finset.sum_lt_sum
    · intro t _;exact (actual_each_transient_gaussian_tail_has_the_verified_rational_interval t).1.le
    · exact ⟨0,Finset.mem_univ _,(actual_each_transient_gaussian_tail_has_the_verified_rational_interval 0).1⟩
  have hsU : (∑t : Fin 39, literalTail (t.val+2)) < ∑t : Fin 39, (probUpper t:ℝ) := by
    apply Finset.sum_lt_sum
    · intro t _;exact (actual_each_transient_gaussian_tail_has_the_verified_rational_interval t).2.le
    · exact ⟨0,Finset.mem_univ _,(actual_each_transient_gaussian_tail_has_the_verified_rational_interval 0).2⟩
  have hcL := congrArg (fun q : ℚ => (q:ℝ)) actual_transient_lower_and_upper_rational_probability_sums_are_exact.1
  have hcU := congrArg (fun q : ℚ => (q:ℝ)) actual_transient_lower_and_upper_rational_probability_sums_are_exact.2
  push_cast at hcL hcU
  norm_num only at hcL hcU
  rw [hcL] at hsL
  rw [hcU] at hsU
  have hE : exactExpected = literalTail 1 + ∑t : Fin 39, literalTail (t.val+2) := by
    unfold exactExpected
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,zero_add,Fin.val_succ]
    congr 1
  have hL : (29683/20000:ℝ) < exactExpected := by rw [hE]; linarith
  have hU : exactExpected < (296871/200000:ℝ) := by rw [hE]; linarith
  refine ⟨hL,hU,?_,?_⟩
  · rw [abs_lt]
    constructor <;> linarith
  · linarith

theorem actual_source_integral_count_is_exactly_the_verified_forty_step_tail_sum :
    (∫w, violationCount (1/2) (4/5) (1/10) w ∂noiseLaw 40) = exactExpected := by
  rw [actual_source_expected_violation_count_is_the_one_to_T_sum_of_true_tails]
  unfold exactExpected
  apply Finset.sum_congr rfl
  intro t _
  simp only [exactTail,show (1/10:ℝ) ≠ 0 by norm_num,if_false,literalTail]
  have h := actual_literal_parameters_have_the_true_derived_rational_mean_and_variance (t.val+1)
  rw [h.1,h.2]

theorem actual_three_source_transient_probabilities_have_four_decimal_roundings :
    |literalTail 3-(44/10000:ℝ)| < 1/20000 ∧
    |literalTail 5-(256/10000:ℝ)| < 1/20000 ∧
    |literalTail 10-(410/10000:ℝ)| < 1/20000 ∧
    literalTail 3 ≠ (44/10000:ℝ) ∧ literalTail 5 ≠ (256/10000:ℝ) ∧ literalTail 10 ≠ (410/10000:ℝ) := by
  have h3 := actual_each_transient_gaussian_tail_has_the_verified_rational_interval (1:Fin 39)
  have h5 := actual_each_transient_gaussian_tail_has_the_verified_rational_interval (3:Fin 39)
  have h10 := actual_each_transient_gaussian_tail_has_the_verified_rational_interval (8:Fin 39)
  norm_num [probLower,probUpper] at h3 h5 h10
  rw [abs_lt,abs_lt,abs_lt]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor
  · linarith
  constructor <;> linarith

theorem actual_markov_bound_is_vacuous_because_the_true_expectation_exceeds_one :
    1 < exactExpected ∧
    (noiseLaw 40).real {w | ∃t : Fin 40, 1 < stateAt (1/2) (4/5) (1/10) t w} ≤ exactExpected ∧
    (noiseLaw 40).real {w | ∃t : Fin 40, 1 < stateAt (1/2) (4/5) (1/10) t w} ≤ 1 := by
  have hL := actual_expected_forty_step_count_has_a_true_enclosure_and_three_decimal_rounding.1
  refine ⟨by linarith, ?_, ?_⟩
  · rw [←actual_source_integral_count_is_exactly_the_verified_forty_step_tail_sum]
    exact actual_joint_violation_probability_is_bounded_by_the_true_expected_count (1/2) (4/5) (1/10) 40
  · have h := measureReal_mono (μ := noiseLaw 40)
      (subset_univ {w | ∃t : Fin 40, 1 < stateAt (1/2) (4/5) (1/10) t w})
    simpa using h

end SafeLearning.CompleteModulesLandscapeARCountNumerics
