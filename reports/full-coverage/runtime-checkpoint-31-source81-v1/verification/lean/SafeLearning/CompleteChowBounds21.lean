import SafeLearning.CompleteChowLP21

noncomputable section
namespace SafeLearning.CompleteChowBounds21
open SafeLearning.CompleteChowLP21

theorem actual_positive_nonterminal_marginals_at_arbitrarily_late_times
    (p : ℝ) (hp : 0 ≤ p) (T : ℕ) :
    ∃ n : ℕ, T < n ∧ 0 < (fastTransition p^n) 0 1 := by
  refine ⟨2*T+1,by omega,?_⟩
  rw [actual_mixed_odd_powers]
  change 0 < (1/20:ℝ)^T * (1/5+2/5*p)
  exact mul_pos (pow_pos (by norm_num) _) (by linarith)

theorem actual_exact_visit_value_slack_and_duration_roundings :
    |(20/19:ℝ)-1.0526|<0.00005 ∧
    |(2/19:ℝ)-0.1053|<0.00005 ∧
    |(28/95:ℝ)-0.2947|<0.00005 ∧
    |(39/190:ℝ)-0.2053|<0.00005 ∧
    |(18/19:ℝ)-0.9474|<0.00005 ∧
    |(213/95:ℝ)-2.2421|<0.00005 := by norm_num [abs_lt]

theorem actual_exact_lp_vertex_and_constant_roundings :
    |(39/56:ℝ)-0.6964|<0.00005 ∧
    |(25/14:ℝ)-1.7857|<0.00005 ∧
    |(5/28:ℝ)-0.1786|<0.00005 ∧
    |(13/142:ℝ)-0.09155|<0.000005 ∧
    |(85/71:ℝ)-1.1972|<0.00005 ∧
    |(15/71:ℝ)-0.2113|<0.00005 := by norm_num [abs_lt]

theorem actual_exact_policy_prices_constraints_and_value_roundings :
    |(15/14:ℝ)-1.0714|<0.00005 ∧
    |(115/142:ℝ)-0.8099|<0.00005 ∧
    |(22/71:ℝ)-0.3099|<0.00005 ∧
    |(13/44:ℝ)-0.2955|<0.00005 ∧
    |(412/1045:ℝ)-0.3943|<0.00005 ∧
    |(39/64:ℝ)-0.6094|<0.00005 ∧
    |(12/19:ℝ)-0.6316|<0.00005 := by norm_num [abs_lt]

end SafeLearning.CompleteChowBounds21
