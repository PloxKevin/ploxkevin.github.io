import SafeLearning.CompletePolicyFOCOPSTight20
import SafeLearning.CompletePolicyFOCOPSProbabilityNumbers20

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompletePolicyFOCOPSBranches20
open SafeLearning.CompletePolicyFOCOPSModel20
open SafeLearning.CompletePolicyFOCOPSNumbers20
open SafeLearning.CompletePolicyFOCOPSProbabilityNumbers20

def exactCostPrice (lam : ℝ) : ℝ := 1/2-lam/4*Real.log (5/3)
def leastNonnegativePrice (lam : ℝ) : ℝ := max 0 (exactCostPrice lam)

theorem actual_price_at_temperature_one_is_the_least_admissible_feasible_price
    (ν : ℝ) (hν : 0≤ν) :
    cost (gibbs 1 ν)≤1/2 ↔ exactCostPrice 1≤ν := by
  simpa only [exactCostPrice] using
    actual_gibbs_cost_feasibility_exact_multiplier 1 ν (by norm_num)

theorem actual_cost_tight_price_has_the_literal_probability (lam : ℝ) (hlam : 0 < lam) :
    probability lam (exactCostPrice lam)=5/8 ∧
      cost (gibbs lam (exactCostPrice lam))=1/2 := by
  have h:=actual_exact_cost_tight_price_reproduces_five_eighths_at_every_positive_temperature
    lam hlam
  change probability lam (exactCostPrice lam)=5/8 at h
  refine ⟨h,?_⟩
  rw [(actual_reward_and_cost_expectations _).2,(actual_gibbs_masses _ _).1,h]
  norm_num

theorem actual_least_nonnegative_feasible_price (lam : ℝ) (hlam : 0 < lam) :
    0≤leastNonnegativePrice lam ∧
      cost (gibbs lam (leastNonnegativePrice lam))≤1/2 ∧
      ∀ ν : ℝ, 0≤ν → cost (gibbs lam ν)≤1/2 → leastNonnegativePrice lam≤ν := by
  refine ⟨le_max_left _ _,?_,?_⟩
  · rw [actual_gibbs_cost_feasibility_exact_multiplier _ _ hlam]
    exact le_max_right _ _
  · intro ν hν hc
    rw [actual_gibbs_cost_feasibility_exact_multiplier _ _ hlam] at hc
    exact max_le hν hc

theorem actual_hot_temperature_unpriced_policy_has_strictly_slack_cost
    (lam : ℝ) (hhot : 2/Real.log (5/3)<lam) :
    probability lam 0<5/8 ∧ cost (gibbs lam 0)<1/2 := by
  have hlog : 0<Real.log (5/3:ℝ) := by linarith [actual_log_five_thirds_enclosure.1]
  have hlam : 0 < lam := lt_trans (div_pos (by norm_num) hlog) hhot
  have he : (2:ℝ)/lam<Real.log (5/3) := by
    have h:= (div_lt_iff₀ hlog).mp hhot
    rw [div_lt_iff₀ hlam]
    nlinarith
  have hp:=actual_gibbs_probability_in_open_unit_interval lam 0
  have hr : probability lam 0/(1-probability lam 0)<5/3 := by
    apply (Real.log_lt_log_iff (div_pos hp.1 (by linarith [hp.2])) (by norm_num)).mp
    simpa only [actual_gibbs_log_odds,mul_zero,sub_zero,mul_one] using he
  rw [div_lt_iff₀ (by linarith [hp.2])] at hr
  have hl : probability lam 0<5/8 := by linarith
  refine ⟨hl,?_⟩
  rw [(actual_reward_and_cost_expectations _).2,(actual_gibbs_masses _ _).1]
  linarith

theorem actual_minimal_price_satisfies_complementarity (lam : ℝ) (hlam : 0 < lam) :
    leastNonnegativePrice lam*(cost (gibbs lam (leastNonnegativePrice lam))-1/2)=0 := by
  by_cases h : 0≤exactCostPrice lam
  · have he : leastNonnegativePrice lam=exactCostPrice lam := max_eq_right h
    rw [he,(actual_cost_tight_price_has_the_literal_probability lam hlam).2]
    ring
  · have he : leastNonnegativePrice lam=0 := max_eq_left (le_of_not_ge h)
    rw [he];ring

theorem actual_minimal_price_policy_is_unique_cost_constrained_regularized_optimizer
    (lam : ℝ) (hlam : 0 < lam) (law : PMF (Fin 2)) (hlaw : cost law≤1/2) :
    regularizedReward lam law≤regularizedReward lam (gibbs lam (leastNonnegativePrice lam)) ∧
      (regularizedReward lam law=regularizedReward lam (gibbs lam (leastNonnegativePrice lam)) ↔
        law=gibbs lam (leastNonnegativePrice lam)) := by
  have h:=actual_least_nonnegative_feasible_price lam hlam
  exact actual_feasible_complementary_gibbs_is_unique_constrained_regularized_optimizer
    lam (leastNonnegativePrice lam) hlam h.1 h.2.1
    (actual_minimal_price_satisfies_complementarity lam hlam) law hlaw

end SafeLearning.CompletePolicyFOCOPSBranches20
