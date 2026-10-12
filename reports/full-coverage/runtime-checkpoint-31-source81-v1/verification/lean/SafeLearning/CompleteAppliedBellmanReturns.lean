import SafeLearning.CompleteAppliedBellman
import SafeLearning.CompleteFiniteHistoryPathLinearProgram
import SafeLearning.CompleteFiniteCMDPDeterministicVertices

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteAppliedBellmanReturns
open CompleteAppliedBellman CompleteFiniteCMDPOccupancy CompleteFiniteCMDPFlow
open CompleteFiniteHistoryPathLinearProgram CompleteFiniteControlledPathMeasure
open CompleteFiniteMarkovPathCorrespondence CompleteFiniteCMDPDeterministicVertices

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

def actualPMFModel (initial : PMF S) (transition : S → A → PMF S) : Model S A where
  initial s := (initial s).toReal
  transition s a t := (transition s a t).toReal
  initial_nonneg _ := ENNReal.toReal_nonneg
  initial_sum := finite_weights_sum initial
  transition_nonneg _ _ _ := ENNReal.toReal_nonneg
  transition_sum s a := finite_weights_sum (transition s a)

theorem actual_bellman_fixed_point_upper_bounds_each_action
    (transition : S → A → PMF S) (reward : S → A → ℝ) (gamma : ℝ)
    (value : S → ℝ) (hv : ∀ s,bellman transition reward gamma value s=value s) :
    ∀ s a,reward s a+gamma*finiteMean (transition s a) value≤value s := by
  classical
  intro s a
  rw [← hv s]
  exact Finset.le_sup' (fun b => reward s b+gamma*finiteMean (transition s b) value)
    (Finset.mem_univ a)

def greedyAction (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ) (value : S → ℝ) (s : S) : A := by
  classical
  exact Classical.choose (Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a => reward s a+gamma*finiteMean (transition s a) value))

theorem actual_greedy_action_attains_the_actual_bellman_maximum
    (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ) (value : S → ℝ) (s : S) :
    reward s (greedyAction transition reward gamma value s)+
      gamma*finiteMean (transition s (greedyAction transition reward gamma value s)) value=
      bellman transition reward gamma value s := by
  classical
  exact (Classical.choose_spec (Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a => reward s a+gamma*finiteMean (transition s a) value))).2.symm

theorem actual_flow_potential_identity (M : Model S A) (gamma : ℝ)
    (rho : S → A → ℝ) (hrho : FlowFeasible M gamma rho) (value : S → ℝ) :
    (∑ s,∑ a,rho s a*value s)=
      (1-gamma)*(∑ s,M.initial s*value s)+
        gamma*(∑ s,∑ a,rho s a*(∑ t,M.transition s a t*value t)) := by
  have he := congrArg (fun f : S → ℝ => ∑ t,f t*value t) (funext hrho.2)
  have hleft : (∑ t,stateMarginal rho t*value t)=∑ s,∑ a,rho s a*value s := by
    simp only [stateMarginal,Finset.sum_mul]
  have hright : (∑ t,((1-gamma)*M.initial t+
      gamma*(∑ s,∑ a,rho s a*M.transition s a t))*value t)=
      (1-gamma)*(∑ s,M.initial s*value s)+
        gamma*(∑ s,∑ a,rho s a*(∑ t,M.transition s a t*value t)) := by
    simp only [add_mul,Finset.sum_add_distrib,mul_assoc,
      ← Finset.mul_sum,Finset.sum_mul]
    congr 1
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum,mul_assoc]
  exact hleft.symm.trans (he.trans hright)

theorem actual_all_feasible_flows_obey_the_bellman_return_upper_bound
    (initial : PMF S) (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ) (hg : gamma<1) (value : S → ℝ)
    (hv : ∀ s,bellman transition reward gamma value s=value s)
    (rho : S → A → ℝ) (hrho : FlowFeasible (actualPMFModel initial transition) gamma rho) :
    (∑ s,∑ a,rho s a*reward s a)/(1-gamma)≤finiteMean initial value := by
  have hi : (∑ s,∑ a,rho s a*(reward s a+gamma*finiteMean (transition s a) value))≤
      ∑ s,∑ a,rho s a*value s := by
    apply Finset.sum_le_sum
    intro s hs
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left
      (actual_bellman_fixed_point_upper_bounds_each_action transition reward gamma value hv s a)
      (hrho.1 s a)
  have hp := actual_flow_potential_identity (actualPMFModel initial transition) gamma rho hrho value
  simp only [actualPMFModel,finiteMean] at hp hi ⊢
  have he : (∑ s,∑ a,rho s a*(reward s a+gamma*(∑ t,(transition s a t).toReal*value t)))=
      (∑ s,∑ a,rho s a*reward s a)+
        gamma*(∑ s,∑ a,rho s a*(∑ t,(transition s a t).toReal*value t)) := by
    simp only [mul_add,Finset.sum_add_distrib,mul_left_comm (rho _ _) gamma,
      ← Finset.mul_sum]
  rw [he,hp] at hi
  apply (div_le_iff₀ (sub_pos.mpr hg)).mpr
  nlinarith

theorem actual_greedy_deterministic_occupancy_attains_the_bellman_bound
    (initial : PMF S) (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ) (hg0 : 0≤gamma) (hg1 : gamma<1) (value : S → ℝ)
    (hv : ∀ s,bellman transition reward gamma value s=value s) :
    expectedReturn (actualPMFModel initial transition)
      (purePolicy (greedyAction transition reward gamma value)) gamma reward=
      finiteMean initial value := by
  let M := actualPMFModel initial transition
  let d := greedyAction transition reward gamma value
  let rho := occupancy M (purePolicy d) gamma
  have hrho : FlowFeasible M gamma rho := actual_occupancy_satisfies_flow M (purePolicy d) gamma hg0 hg1
  have heach : ∀ s a,rho s a*(reward s a+gamma*finiteMean (transition s a) value)=rho s a*value s := by
    intro s a
    by_cases ha : a=d s
    · subst a
      rw [actual_greedy_action_attains_the_actual_bellman_maximum,hv s]
    · have hz : rho s a=0 := actual_pure_policy_occupancy_has_only_selected_actions M d gamma hg0 hg1 s a ha
      rw [hz];ring
  have hsum := congrArg (fun f : S → A → ℝ => ∑ s,∑ a,f s a) (funext fun s => funext (heach s))
  have hp := actual_flow_potential_identity M gamma rho hrho value
  have he : (∑ s,∑ a,rho s a*(reward s a+gamma*finiteMean (transition s a) value))=
      (∑ s,∑ a,rho s a*reward s a)+
        gamma*(∑ s,∑ a,rho s a*finiteMean (transition s a) value) := by
    simp only [mul_add,Finset.sum_add_distrib,mul_left_comm (rho _ _) gamma,
      ← Finset.mul_sum]
  change (∑ s,∑ a,rho s a*(reward s a+gamma*finiteMean (transition s a) value))=
    ∑ s,∑ a,rho s a*value s at hsum
  rw [he,hp] at hsum
  change (∑ s,∑ a,rho s a*reward s a)+gamma*(∑ s,∑ a,rho s a*finiteMean (transition s a) value)=
    (1-gamma)*finiteMean initial value+gamma*(∑ s,∑ a,rho s a*finiteMean (transition s a) value) at hsum
  rw [actual_reward_return_identity _ _ gamma hg0 hg1]
  apply (div_eq_iff (ne_of_gt (sub_pos.mpr hg1))).mpr
  nlinarith

variable [MeasurableSpace S] [MeasurableSpace A]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

theorem actual_every_history_dependent_path_return_is_bounded_by_the_bellman_value
    (initial : PMF S) (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ) (hg0 : 0≤gamma) (hg1 : gamma<1) (value : S → ℝ)
    (hv : ∀ s,bellman transition reward gamma value s=value s) (pi : HistoryPolicy S A) :
    pathReturn (actualPMFModel initial transition) gamma pi reward≤finiteMean initial value := by
  rw [actual_history_path_return_linear_formula _ _ hg0 hg1]
  exact actual_all_feasible_flows_obey_the_bellman_return_upper_bound initial transition reward gamma hg1 value hv _
    (CompleteFiniteControlledPathMeasureLaws.actual_all_history_policies_have_flow_feasible_path_occupancy _ pi gamma hg0 hg1)

theorem actual_greedy_constructed_path_return_attains_the_bellman_value
    (initial : PMF S) (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ) (hg0 : 0≤gamma) (hg1 : gamma<1) (value : S → ℝ)
    (hv : ∀ s,bellman transition reward gamma value s=value s) :
    pathReturn (actualPMFModel initial transition) gamma
      (markovHistoryPolicy (purePolicy (greedyAction transition reward gamma value))) reward=
      finiteMean initial value := by
  rw [show pathReturn (actualPMFModel initial transition) gamma
      (markovHistoryPolicy (purePolicy (greedyAction transition reward gamma value))) reward=
        expectedReturn (actualPMFModel initial transition)
          (purePolicy (greedyAction transition reward gamma value)) gamma reward from
            actual_constructed_markov_path_expected_return _ _ gamma hg0 hg1 reward]
  exact actual_greedy_deterministic_occupancy_attains_the_bellman_bound initial transition reward gamma hg0 hg1 value hv

theorem actual_bellman_fixed_point_is_the_attained_optimum_over_all_history_paths
    (initial : PMF S) (transition : S → A → PMF S) (reward : S → A → ℝ)
    (gamma : ℝ) (hg0 : 0≤gamma) (hg1 : gamma<1) (value : S → ℝ)
    (hv : ∀ s,bellman transition reward gamma value s=value s) :
    IsGreatest {v : ℝ | ∃ pi : HistoryPolicy S A,
      pathReturn (actualPMFModel initial transition) gamma pi reward=v} (finiteMean initial value) := by
  constructor
  · exact ⟨markovHistoryPolicy (purePolicy (greedyAction transition reward gamma value)),
      actual_greedy_constructed_path_return_attains_the_bellman_value initial transition reward gamma hg0 hg1 value hv⟩
  · rintro v ⟨pi,rfl⟩
    exact actual_every_history_dependent_path_return_is_bounded_by_the_bellman_value initial transition reward gamma hg0 hg1 value hv pi

end SafeLearning.CompleteAppliedBellmanReturns
