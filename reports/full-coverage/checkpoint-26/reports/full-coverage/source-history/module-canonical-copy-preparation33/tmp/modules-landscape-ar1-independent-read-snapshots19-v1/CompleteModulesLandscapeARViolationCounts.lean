import SafeLearning.CompleteModulesLandscapeARGaussianLaw
import SafeLearning.CompleteModulesLandscapeGaussianTailCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SafeLearning.CompleteModulesLandscapeARViolationCounts
open CompleteModulesLandscapeARGaussianAlgebra CompleteModulesLandscapeARGaussianLaw
open CompleteModulesLandscapeGaussianTailCounts CompleteModulesLandscapeFiniteCounts
open CompleteAppliedGaussianCDF

def oneBasedTime {T : ℕ} (t : Fin T) : Fin (T+1) := ⟨t.val+1, by omega⟩
def stateAt {T : ℕ} (k goal sigma : ℝ) (t : Fin T) (w : Fin T → ℝ) : ℝ :=
  vectorTrajectory k goal sigma T w (oneBasedTime t)
def stateSD (k sigma : ℝ) (t : ℕ) : NNReal := NNReal.sqrt (trueVariance k sigma t).toNNReal
def violationCount {T : ℕ} (k goal sigma : ℝ) (w : Fin T → ℝ) : ℝ :=
  ∑t : Fin T, stepCost {w | 1 < stateAt k goal sigma t w} w
def exactTail (k goal sigma : ℝ) (t : ℕ) : ℝ :=
  if sigma = 0 then (if 1 < trueMean k goal t then 1 else 0)
  else 1-standardCDF ((1-trueMean k goal t)/Real.sqrt (trueVariance k sigma t))

theorem actual_one_based_state_is_measurable (k goal sigma : ℝ) (T : ℕ) (t : Fin T) :
    Measurable (stateAt k goal sigma t) :=
  (measurable_pi_apply (oneBasedTime t)).comp
    (actual_finite_trajectory_is_measurable k goal sigma T)

theorem actual_one_based_state_has_the_true_derived_gaussian_law
    (k goal sigma : ℝ) (T : ℕ) (t : Fin T) :
    HasLaw (stateAt k goal sigma t)
      (gaussianReal (trueMean k goal (t.val+1)) ((stateSD k sigma (t.val+1))^2)) (noiseLaw T) := by
  refine ⟨(actual_one_based_state_is_measurable k goal sigma T t).aemeasurable, ?_⟩
  rw [stateSD, NNReal.sq_sqrt]
  exact actual_every_state_has_the_true_scalar_gaussian_marginal k goal sigma T (oneBasedTime t)

theorem actual_positive_time_and_nonzero_noise_make_the_standardizing_denominator_nonzero
    (k sigma : ℝ) (t : ℕ) (ht : 0 < t) (hsigma : sigma ≠ 0) :
    stateSD k sigma t ≠ 0 ∧ 0 < Real.sqrt (trueVariance k sigma t) := by
  have hv := actual_positive_time_and_nonzero_noise_have_strictly_positive_variance k sigma t ht hsigma
  have hn : 0 < (trueVariance k sigma t).toNNReal := by
    rw [← NNReal.coe_pos, Real.coe_toNNReal _ hv.le]
    exact hv
  exact ⟨ne_of_gt (NNReal.sqrt_pos_of_pos hn), Real.sqrt_pos_of_pos hv⟩

theorem actual_each_one_based_violation_probability_is_the_printed_piecewise_tail
    (k goal sigma : ℝ) (T : ℕ) (t : Fin T) :
    (noiseLaw T).real {w | 1 < stateAt k goal sigma t w} = exactTail k goal sigma (t.val+1) := by
  have hl := actual_one_based_state_has_the_true_derived_gaussian_law k goal sigma T t
  by_cases hsigma : sigma = 0
  · subst sigma
    have he : stateSD k 0 (t.val+1) = 0 := by simp [stateSD, trueVariance]
    rw [he, zero_pow (by decide : (2:ℕ) ≠ 0)] at hl
    simpa [exactTail] using actual_zero_variance_gaussian_tail_is_the_deterministic_strict_indicator
      (noiseLaw T) (stateAt k goal 0 t) (trueMean k goal (t.val+1)) 1 hl
  · have hn := (actual_positive_time_and_nonzero_noise_make_the_standardizing_denominator_nonzero
      k sigma (t.val+1) (by omega) hsigma).1
    have h := actual_gaussian_upper_tail_is_the_standard_cdf_complement
      (noiseLaw T) (stateAt k goal sigma t) (trueMean k goal (t.val+1)) 1
      (stateSD k sigma (t.val+1)) hn hl
    rw [exactTail, if_neg hsigma, Real.sqrt]
    exact h

theorem actual_source_expected_violation_count_is_the_one_to_T_sum_of_true_tails
    (k goal sigma : ℝ) (T : ℕ) :
    (∫w, violationCount k goal sigma w ∂noiseLaw T) =
      ∑t : Fin T, exactTail k goal sigma (t.val+1) := by
  unfold violationCount
  rw [integral_finsetSum Finset.univ (μ := noiseLaw T)
    (f := fun t w => stepCost {w | 1 < stateAt k goal sigma t w} w)
    (fun t _ => (integrable_const (1:ℝ)).indicator
      (measurableSet_Ioi.preimage (actual_one_based_state_is_measurable k goal sigma T t)))]
  apply Finset.sum_congr rfl
  intro t _
  rw [show (∫w, stepCost {w | 1 < stateAt k goal sigma t w} w ∂noiseLaw T) =
      (noiseLaw T).real {w | 1 < stateAt k goal sigma t w} from
    integral_indicator_one (measurableSet_Ioi.preimage (actual_one_based_state_is_measurable k goal sigma T t))]
  exact actual_each_one_based_violation_probability_is_the_printed_piecewise_tail k goal sigma T t

theorem actual_joint_violation_probability_is_bounded_by_the_true_expected_count
    (k goal sigma : ℝ) (T : ℕ) :
    (noiseLaw T).real {w | ∃t : Fin T, 1 < stateAt k goal sigma t w} ≤
      ∫w, violationCount k goal sigma w ∂noiseLaw T := by
  rw [actual_source_expected_violation_count_is_the_one_to_T_sum_of_true_tails]
  have he : {w | ∃t : Fin T, 1 < stateAt k goal sigma t w} =
      ⋃t : Fin T, {w | 1 < stateAt k goal sigma t w} := by ext w; simp
  rw [he]
  calc
    _ ≤ ∑t : Fin T, (noiseLaw T).real {w | 1 < stateAt k goal sigma t w} :=
      measureReal_iUnion_fintype_le _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      exact actual_each_one_based_violation_probability_is_the_printed_piecewise_tail k goal sigma T t

theorem actual_nondegenerate_noise_makes_every_positive_time_violation_probability_positive
    (k goal sigma : ℝ) (T : ℕ) (t : Fin T) (hsigma : sigma ≠ 0) :
    0 < (noiseLaw T).real {w | 1 < stateAt k goal sigma t w} := by
  have hl := actual_one_based_state_has_the_true_derived_gaussian_law k goal sigma T t
  rw [hl.measureReal_eq (p := fun x : ℝ => 1 < x) measurableSet_Ioi]
  exact actual_nondegenerate_gaussian_upper_tail_is_strictly_positive _ _ _
    (pow_ne_zero 2 (actual_positive_time_and_nonzero_noise_make_the_standardizing_denominator_nonzero
      k sigma (t.val+1) (by omega) hsigma).1)

theorem actual_zero_noise_is_deterministic_and_equality_at_the_boundary_is_safe
    (k goal : ℝ) (T : ℕ) (t : Fin T) :
    (noiseLaw T).real {w | 1 < stateAt k goal 0 t w} =
      (if 1 < trueMean k goal (t.val+1) then 1 else 0) ∧
    (trueMean k goal (t.val+1) = 1 → (noiseLaw T).real {w | 1 < stateAt k goal 0 t w} = 0) := by
  have h := actual_each_one_based_violation_probability_is_the_printed_piecewise_tail k goal 0 T t
  simp only [exactTail, if_pos rfl] at h
  refine ⟨h, ?_⟩
  intro he
  simpa [he] using h

theorem actual_initial_state_never_violates_and_zero_horizon_has_zero_count
    (k goal sigma : ℝ) :
    (∀T (w : Fin T → ℝ), trajectory k goal sigma w 0 ≤ 1) ∧
      (∫w, violationCount k goal sigma w ∂noiseLaw 0) = 0 := by
  constructor
  · intro T w; norm_num [trajectory]
  · simp [violationCount]

end SafeLearning.CompleteModulesLandscapeARViolationCounts
