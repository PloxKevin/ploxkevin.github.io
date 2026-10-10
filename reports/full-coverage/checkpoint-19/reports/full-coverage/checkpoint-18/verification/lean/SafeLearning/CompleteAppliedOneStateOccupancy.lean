import SafeLearning.CompleteAppliedReturns

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedOneStateOccupancy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Function

def actualActionLaw (parameter : unitInterval) : Measure Bool :=
  bernoulliMeasure true false parameter

def actualActionPathLaw (parameter : unitInterval) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ => actualActionLaw parameter)

instance (parameter : unitInterval) : IsProbabilityMeasure (actualActionLaw parameter) := by
  unfold actualActionLaw
  infer_instance

instance (parameter : unitInterval) : IsProbabilityMeasure (actualActionPathLaw parameter) := by
  unfold actualActionPathLaw
  infer_instance

def actualAction (time : ℕ) (path : ℕ → Bool) : Bool := path time
def actualActionQuantity (amount : ℝ) (action : Bool) : ℝ := if action then amount else 0
def actualPathQuantity (amount : ℝ) (time : ℕ) (path : ℕ → Bool) : ℝ :=
  actualActionQuantity amount (actualAction time path)
def actualDiscountedReturn (amount : ℝ) (path : ℕ → Bool) : ℝ :=
  ∑' time : ℕ,(4/5:ℝ)^time*actualPathQuantity amount time path

/-- Actual iid actions, not merely a probability parameter used in scalar arithmetic. -/
theorem actual_stationary_actions_are_independent_with_the_true_action_law
    (parameter : unitInterval) :
    iIndepFun actualAction (actualActionPathLaw parameter) ∧
      ∀ time,HasLaw (actualAction time) (actualActionLaw parameter)
        (actualActionPathLaw parameter) := by
  constructor
  · exact iIndepFun_infinitePi (fun _ => measurable_id)
  · intro time
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => actualActionLaw parameter) time).hasLaw

theorem actual_action_quantity_expectation (parameter : unitInterval) (amount : ℝ) :
    (∫ action,actualActionQuantity amount action ∂actualActionLaw parameter)=
      (parameter:ℝ)*amount := by
  rw [actualActionLaw,integral_bernoulliMeasure]
  simp [actualActionQuantity]

theorem actual_each_path_stage_has_the_source_expectation
    (parameter : unitInterval) (amount : ℝ) (time : ℕ) :
    (∫ path,actualPathQuantity amount time path ∂actualActionPathLaw parameter)=
      (parameter:ℝ)*amount := by
  have hlaw := (actual_stationary_actions_are_independent_with_the_true_action_law parameter).2 time
  have hm : Measurable (actualActionQuantity amount) := measurable_of_countable _
  change (∫ path,actualActionQuantity amount (actualAction time path)
    ∂actualActionPathLaw parameter)=_
  calc
    _ = ∫ action,actualActionQuantity amount action ∂actualActionLaw parameter := by
      simpa only [Function.comp_apply] using hlaw.integral_comp hm.aestronglyMeasurable
    _ = _ := actual_action_quantity_expectation parameter amount

theorem actual_path_quantity_is_bounded (amount : ℝ) (time : ℕ) (path : ℕ → Bool) :
    |actualPathQuantity amount time path| ≤ |amount| := by
  unfold actualPathQuantity actualActionQuantity
  split_ifs <;> simp

theorem actual_true_infinite_expected_discounted_return
    (parameter : unitInterval) (amount : ℝ) :
    (∫ path,actualDiscountedReturn amount path ∂actualActionPathLaw parameter)=
      5*(parameter:ℝ)*amount := by
  have hm : ∀ time,AEStronglyMeasurable (actualPathQuantity amount time)
      (actualActionPathLaw parameter) := by
    intro time
    have hq : Measurable (actualActionQuantity amount) := measurable_of_countable _
    exact (hq.comp (measurable_pi_apply time)).aestronglyMeasurable
  have hi := SafeLearning.CompleteAppliedReturns.discounted_expectation_interchange
    (actualActionPathLaw parameter) (actualPathQuantity amount) (4/5) |amount|
    (by norm_num) hm
    (fun time => Filter.Eventually.of_forall (actual_path_quantity_is_bounded amount time))
  change (∫ path,∑' time : ℕ,(4/5:ℝ)^time*actualPathQuantity amount time path
    ∂actualActionPathLaw parameter)=_
  rw [hi]
  simp_rw [actual_each_path_stage_has_the_source_expectation]
  have hg := ((hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 4/5)
    (by norm_num : (4/5:ℝ)<1)).mul_right ((parameter:ℝ)*amount)).tsum_eq
  rw [hg]
  ring

def actualNormalizedOccupancy (parameter : unitInterval) (action : Bool) : ℝ :=
  (1-(4/5:ℝ))*∑' time : ℕ,(4/5:ℝ)^time*
    (actualActionPathLaw parameter).real {path | actualAction time path=action}

theorem actual_source_action_event_probabilities (parameter : unitInterval) (time : ℕ) :
    (actualActionPathLaw parameter).real {path | actualAction time path=true}=(parameter:ℝ) ∧
      (actualActionPathLaw parameter).real {path | actualAction time path=false}=1-(parameter:ℝ) := by
  have h := (actual_stationary_actions_are_independent_with_the_true_action_law parameter).2 time
  have he (action : Bool) : (actualActionPathLaw parameter).real
      {path | actualAction time path=action}=(actualActionLaw parameter).real {action} := by
    exact h.measureReal_eq (measurableSet_singleton action)
  rw [he true,he false,actualActionLaw]
  simp

theorem actual_normalized_occupancies_equal_the_stationary_probabilities (parameter : unitInterval) :
    actualNormalizedOccupancy parameter true=(parameter:ℝ) ∧
      actualNormalizedOccupancy parameter false=1-(parameter:ℝ) := by
  have he (mass : ℝ) : (1-(4/5:ℝ))*(∑' time : ℕ,(4/5:ℝ)^time*mass)=mass := by
    have h := ((hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 4/5)
      (by norm_num : (4/5:ℝ)<1)).mul_right mass).tsum_eq
    rw [h]
    ring
  constructor
  · unfold actualNormalizedOccupancy
    simp_rw [(actual_source_action_event_probabilities parameter _).1]
    exact he _
  · unfold actualNormalizedOccupancy
    simp_rw [(actual_source_action_event_probabilities parameter _).2]
    exact he _

def actualExpectedReward (parameter : unitInterval) : ℝ :=
  ∫ path,actualDiscountedReturn 2 path ∂actualActionPathLaw parameter
def actualExpectedCost (parameter : unitInterval) : ℝ :=
  ∫ path,actualDiscountedReturn 1 path ∂actualActionPathLaw parameter

theorem actual_source_returns_and_budget (parameter : unitInterval) :
    actualExpectedReward parameter=10*(parameter:ℝ) ∧
      actualExpectedCost parameter=5*(parameter:ℝ) ∧
      (actualExpectedCost parameter ≤ 2 ↔ (parameter:ℝ) ≤ 2/5) := by
  have hr := actual_true_infinite_expected_discounted_return parameter 2
  have hc := actual_true_infinite_expected_discounted_return parameter 1
  have hre : actualExpectedReward parameter=10*(parameter:ℝ) := by
    unfold actualExpectedReward;rw [hr];ring
  have hce : actualExpectedCost parameter=5*(parameter:ℝ) := by
    unfold actualExpectedCost;rw [hc];ring
  refine ⟨hre,hce,?_⟩
  rw [hce]
  constructor <;> intro h <;> linarith

def actualOptimalParameter : unitInterval := ⟨2/5,by norm_num⟩

theorem actual_feasible_reward_has_unique_optimizer (parameter : unitInterval)
    (hbudget : actualExpectedCost parameter ≤ 2) :
    actualExpectedReward parameter ≤ actualExpectedReward actualOptimalParameter ∧
      (actualExpectedReward parameter=actualExpectedReward actualOptimalParameter ↔
        parameter=actualOptimalParameter) := by
  have hp := (actual_source_returns_and_budget parameter).2.2.mp hbudget
  have hr := (actual_source_returns_and_budget parameter).1
  have ho := (actual_source_returns_and_budget actualOptimalParameter).1
  have hv : (actualOptimalParameter:ℝ)=2/5 := rfl
  rw [hr,ho,hv]
  refine ⟨by linarith,?_⟩
  constructor
  · intro h
    apply Subtype.ext
    change (parameter:ℝ)=2/5
    linarith
  · intro h
    rw [h,hv]

theorem actual_optimizer_values_and_positive_single_action_cost_probability :
    actualExpectedReward actualOptimalParameter=4 ∧
      actualExpectedCost actualOptimalParameter=2 ∧
      (actualActionPathLaw actualOptimalParameter).real
        {path | actualPathQuantity 1 0 path=1}=2/5 := by
  have h := actual_source_returns_and_budget actualOptimalParameter
  have hv : (actualOptimalParameter:ℝ)=2/5 := rfl
  refine ⟨by rw [h.1,hv];norm_num,by rw [h.2.1,hv];norm_num,?_⟩
  have he : {path | actualPathQuantity 1 0 path=1}=
      {path | actualAction 0 path=true} := by
    ext path
    cases hc : actualAction 0 path <;> simp [actualPathQuantity,actualActionQuantity,hc]
  rw [he,(actual_source_action_event_probabilities actualOptimalParameter 0).1,hv]

end SafeLearning.CompleteAppliedOneStateOccupancy
