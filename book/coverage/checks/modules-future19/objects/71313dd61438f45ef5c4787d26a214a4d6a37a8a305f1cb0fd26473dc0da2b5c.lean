import SafeLearning.CompleteModulesLandscapeARGaussianAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeARMomentConsequences
open CompleteModulesLandscapeARGaussianAlgebra

theorem actual_source_variance_step_is_the_previous_sum_plus_a_nonnegative_term
    (k sigma : ℝ) (t : ℕ) :
    trueVariance k sigma (t+1) = trueVariance k sigma t + sigma^2*(1-k)^(2*t) := by
  simp only [trueVariance, Finset.sum_range_succ, mul_add]

theorem actual_variance_grows_nondecreasingly_at_every_gain_and_noise_scale
    (k sigma : ℝ) : Monotone (trueVariance k sigma) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [actual_source_variance_step_is_the_previous_sum_plus_a_nonnegative_term]
  have hn : 0 ≤ sigma^2*(1-k)^(2*t) := by positivity
  linarith

theorem actual_variance_growth_is_strict_when_noise_and_multiplier_are_nonzero
    (k sigma : ℝ) (hsigma : sigma ≠ 0) (hk : k ≠ 1) :
    StrictMono (trueVariance k sigma) := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [actual_source_variance_step_is_the_previous_sum_plus_a_nonnegative_term]
  have ha : 1-k ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  have hp : 0 < sigma^2*(1-k)^(2*t) :=
    mul_pos (sq_pos_of_ne_zero hsigma) (pow_pos (sq_pos_of_ne_zero ha) t) |>.of_eq (by rw [pow_mul])
  linarith

theorem actual_gain_one_variance_is_constant_after_the_first_fresh_noise
    (sigma : ℝ) (t : ℕ) : trueVariance 1 sigma (t+1) = sigma^2 := by
  simp [trueVariance, Finset.sum_range_succ]

theorem actual_zero_noise_has_zero_variance_and_literal_centered_error_recursion
    {T : ℕ} (k goal sigma : ℝ) (w : Fin T → ℝ) :
    (∀t : ℕ, trueVariance k 0 t = 0) ∧
    (trajectory k goal sigma w 0-goal = -goal) ∧
    (∀t (ht : t<T), trajectory k goal sigma w (t+1)-goal =
      (1-k)*(trajectory k goal sigma w t-goal)+sigma*w ⟨t,ht⟩) := by
  refine ⟨fun t => by simp [trueVariance], by simp [trajectory], ?_⟩
  intro t ht
  rw [(actual_trajectory_satisfies_the_literal_initial_condition_and_source_recursion k goal sigma w).2 t ht]
  ring

end SafeLearning.CompleteModulesLandscapeARMomentConsequences
