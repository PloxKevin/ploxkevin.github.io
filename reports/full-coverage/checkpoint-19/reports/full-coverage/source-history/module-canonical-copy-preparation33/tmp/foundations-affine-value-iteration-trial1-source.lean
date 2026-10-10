import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter ProbabilityTheory
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsAffineValueIteration

def sourceStep (x : ℝ) : ℝ := (1/2:ℝ)*x+1
def rewardStep (gamma : ℝ) (value : ℝ) : ℝ := 1+gamma*value

theorem actual_graph_diagonal_intersection_is_exactly_the_fixed_point_condition
    (g : ℝ → ℝ) (x : ℝ) :
    (x,x) ∈ {p : ℝ×ℝ | p.2=g p.1} ↔ g x=x := by
  simp only [Set.mem_setOf_eq, eq_comm]

theorem actual_cobweb_graph_and_diagonal_pairs_follow_the_genuine_iteration
    (g : ℝ → ℝ) (initial : ℝ) (k : ℕ) :
    (g^[k] initial,g^[k+1] initial) ∈ {p : ℝ×ℝ | p.2=g p.1} ∧
      (g^[k+1] initial,g^[k+1] initial) ∈ {p : ℝ×ℝ | p.2=p.1} :=
  ⟨Function.iterate_succ_apply' _ _ _,rfl⟩

theorem actual_source_affine_fixed_point_is_uniquely_two (x : ℝ) :
    sourceStep x=x ↔ x=2 := by
  unfold sourceStep
  constructor <;> intro h <;> linarith

theorem actual_source_affine_step_has_the_exact_half_distance (x y : ℝ) :
    |sourceStep x-sourceStep y|=(1/2:ℝ)*|x-y| := by
  rw [show sourceStep x-sourceStep y=(1/2:ℝ)*(x-y) by unfold sourceStep; ring,abs_mul]
  norm_num

theorem actual_source_first_four_iterates_and_five_errors :
    sourceStep^[1] (0:ℝ)=1 ∧ sourceStep^[2] (0:ℝ)=3/2 ∧
      sourceStep^[3] (0:ℝ)=7/4 ∧ sourceStep^[4] (0:ℝ)=15/8 ∧
    |sourceStep^[0] (0:ℝ)-2|=2 ∧ |sourceStep^[1] (0:ℝ)-2|=1 ∧
      |sourceStep^[2] (0:ℝ)-2|=1/2 ∧ |sourceStep^[3] (0:ℝ)-2|=1/4 ∧
      |sourceStep^[4] (0:ℝ)-2|=1/8 := by
  norm_num [Function.iterate_succ_apply',sourceStep]

theorem actual_source_every_iterate_and_error_are_derived_by_induction (k : ℕ) :
    sourceStep^[k] (0:ℝ)=2*(1-(1/2:ℝ)^k) ∧
      |sourceStep^[k] (0:ℝ)-2|=2*(1/2:ℝ)^k := by
  have hi : ∀ k,sourceStep^[k] (0:ℝ)=2*(1-(1/2:ℝ)^k) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [Function.iterate_succ_apply',ih];unfold sourceStep;rw [pow_succ];ring
  refine ⟨hi k,?_⟩
  rw [hi k,show 2*(1-(1/2:ℝ)^k)-2=-(2*(1/2:ℝ)^k) by ring,abs_neg]
  exact abs_of_nonneg (by positivity)

theorem actual_zero_initial_reward_iteration_is_the_true_natural_prefix_sum
    (gamma : ℝ) (k : ℕ) :
    (rewardStep gamma)^[k] (0:ℝ)=∑ j ∈ Finset.range k,gamma^j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,Finset.sum_range_succ']
    simp only [rewardStep,pow_succ,pow_zero,Finset.sum_mul]
    ring

def actualSingleStateBellman (gamma : ℝ) (value : Unit → ℝ) (_state : Unit) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun _action : Unit =>
    1+gamma*(∑ next : Unit, (PMF.pure () next).toReal*value next))

theorem actual_one_state_one_action_stochastic_bellman_backup_is_the_reward_recursion
    (gamma : ℝ) (value : Unit → ℝ) (state : Unit) :
    actualSingleStateBellman gamma value state=rewardStep gamma (value ()) := by
  simp [actualSingleStateBellman,rewardStep,PMF.pure_apply]

theorem actual_source_half_discount_is_the_same_value_iteration_and_partial_sum (k : ℕ) :
    sourceStep=rewardStep (1/2:ℝ) ∧
      sourceStep^[k] (0:ℝ)=∑ j ∈ Finset.range k,(1/2:ℝ)^j := by
  have he : sourceStep=rewardStep (1/2:ℝ) := by funext x;unfold sourceStep rewardStep;ring
  exact ⟨he,by rw [he];exact actual_zero_initial_reward_iteration_is_the_true_natural_prefix_sum _ _⟩

theorem actual_discounted_value_iterates_converge_to_the_true_geometric_return
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) :
    Tendsto (fun k => (rewardStep gamma)^[k] (0:ℝ)) atTop
      (𝓝 (1/(1-gamma))) := by
  have h := (hasSum_geometric_of_lt_one hg0 hg1).tendsto_sum_nat
  simpa only [actual_zero_initial_reward_iteration_is_the_true_natural_prefix_sum,one_div] using h

theorem actual_source_half_discount_converges_to_two :
    Tendsto (fun k => sourceStep^[k] (0:ℝ)) atTop (𝓝 (2:ℝ)) := by
  have h := actual_discounted_value_iterates_converge_to_the_true_geometric_return
    (1/2:ℝ) (by norm_num) (by norm_num)
  have he : sourceStep=rewardStep (1/2:ℝ) :=
    (actual_source_half_discount_is_the_same_value_iteration_and_partial_sum 0).1
  simpa only [←he,show (1/(1-(1/2:ℝ)))=2 by norm_num] using h

end SafeLearning.CompleteFoundationsAffineValueIteration
