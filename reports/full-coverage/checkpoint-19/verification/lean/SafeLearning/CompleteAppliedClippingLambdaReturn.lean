import SafeLearning.CompleteAppliedClippingGAE

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SafeLearning.CompleteAppliedClippingLambdaReturn
open SafeLearning.CompleteAppliedClippingGAE

def actualLambdaReturn (reward value : ℕ → ℝ) (discount mixing : ℝ) : ℕ → ℕ → ℝ
  | 0, time => value time
  | remaining + 1, time =>
      reward time + discount * ((1 - mixing) * value (time + 1) +
        mixing * actualLambdaReturn reward value discount mixing remaining (time + 1))

theorem actual_finite_lambda_return_minus_value_is_actual_gae
    (reward value : ℕ → ℝ) (discount mixing : ℝ) (remaining time : ℕ) :
    actualLambdaReturn reward value discount mixing remaining time - value time =
      actualGAE (actualTD reward value discount) (discount * mixing) remaining time := by
  induction remaining generalizing time with
  | zero => simp [actualLambdaReturn, actualGAE]
  | succ remaining ih =>
    rw [actualLambdaReturn, actualGAE, ← ih]
    unfold actualTD
    ring

theorem actual_lambda_one_return_is_full_reward_sum_and_terminal_bootstrap
    (reward value : ℕ → ℝ) (discount : ℝ) (remaining time : ℕ) :
    actualLambdaReturn reward value discount 1 remaining time =
      (∑ offset ∈ Finset.range remaining, discount ^ offset * reward (time + offset)) +
        discount ^ remaining * value (time + remaining) := by
  have h := actual_finite_lambda_return_minus_value_is_actual_gae
    reward value discount 1 remaining time
  simp only [mul_one] at h
  rw [actual_lambda_one_gae_is_the_true_return_minus_value_with_terminal_value] at h
  linarith

theorem actual_source_td_half_return_from_the_genuine_return_recursion :
    actualLambdaReturn sourceReward sourceValue (9 / 10) (1 / 2) 3 0 = 1269 / 2000 ∧
      actualLambdaReturn sourceReward sourceValue (9 / 10) (1 / 2) 3 0 = 0.6345 ∧
      actualLambdaReturn sourceReward sourceValue (9 / 10) (1 / 2) 3 0 - sourceValue 0 =
        269 / 2000 := by
  norm_num [actualLambdaReturn, sourceReward, sourceValue]

end SafeLearning.CompleteAppliedClippingLambdaReturn
