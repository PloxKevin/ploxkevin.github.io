import SafeLearning.CompleteModulesLandscapeDelayFailure

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace SafeLearning.CompleteModulesLandscapeControlledDelay
open SafeLearning.CompleteModulesLandscapeDelayFailure

abbrev State := ℕ×Bool
def sourceInitialState : State := (0,false)
def sourceFixedSafeSet : Set State := {state | state.2=false}
def sourceControlledDynamics (state : State) (action : Bool) : State := (state.1+1,action)
def sourceThresholdPolicy (delay : ℕ) (state : State) : Bool := decide (delay ≤ state.1+1)
def sourceThresholdPath (delay time : ℕ) : State := (time,decide (delay ≤ time))
def sourceStateViolationCost (state : State) : ℝ := if state.2 then 1 else 0

def sourcePolicyTrajectory (policy : State→Bool) : ℕ→State
  | 0=>sourceInitialState
  | time+1=>sourceControlledDynamics (sourcePolicyTrajectory policy time)
      (policy (sourcePolicyTrajectory policy time))

theorem actual_fixed_initial_state_is_safe : sourceInitialState∈sourceFixedSafeSet := rfl

theorem actual_threshold_policy_has_the_printed_delayed_controlled_trajectory
    (delay : ℕ) (hdelay : 1 ≤ delay) :
    (∀ time : ℕ,sourcePolicyTrajectory (sourceThresholdPolicy delay) time=
      sourceThresholdPath delay time) ∧
    (∀ time : ℕ,sourceThresholdPath delay (time+1)=
      sourceControlledDynamics (sourceThresholdPath delay time)
        (sourceThresholdPolicy delay (sourceThresholdPath delay time))) := by
  have hstart : sourceThresholdPath delay 0=sourceInitialState := by
    simp [sourceThresholdPath,sourceInitialState,show ¬delay ≤ 0 by omega]
  have hstep (time : ℕ) : sourceThresholdPath delay (time+1)=
      sourceControlledDynamics (sourceThresholdPath delay time)
        (sourceThresholdPolicy delay (sourceThresholdPath delay time)) := rfl
  constructor
  · intro time
    induction time with
    | zero=>exact hstart.symm
    | succ time ih=>rw [sourcePolicyTrajectory,ih];exact (hstep time).symm
  · exact hstep

theorem actual_fixed_safe_set_indicator_is_exactly_the_source_delayed_cost
    (delay time : ℕ) :
    sourceStateViolationCost (sourceThresholdPath delay time)=actualViolationCost delay time ∧
      sourceStateViolationCost (sourceThresholdPath delay time)=
        sourceFixedSafeSetᶜ.indicator (fun _ : State=>(1:ℝ)) (sourceThresholdPath delay time) := by
  classical
  by_cases h : delay ≤ time <;>
    simp [sourceStateViolationCost,sourceThresholdPath,actualViolationCost,
      sourceFixedSafeSet,Set.indicator,h]

theorem actual_every_positive_budget_has_a_policy_in_one_fixed_safe_set_model
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (gamma budget : ℝ) (hgamma : 0<gamma) (hgamma1 : gamma<1) (hbudget : 0<budget) :
    ∃ delay : ℕ,1 ≤ delay ∧
      (∫ _ω : Ω,(∑'time : ℕ,gamma^time*
        sourceStateViolationCost (sourcePolicyTrajectory (sourceThresholdPolicy delay) time)) ∂P) ≤ budget ∧
      P.real {_ω : Ω | ∃time : ℕ,
        sourcePolicyTrajectory (sourceThresholdPolicy delay) time∉sourceFixedSafeSet}=1 := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (mul_pos hbudget (sub_pos.mpr hgamma1)) hgamma1
  let delay := n+1
  have hd : 1 ≤ delay := by omega
  have hp : gamma^delay ≤ budget*(1-gamma) := by
    dsimp [delay]
    rw [pow_succ]
    exact (mul_le_of_le_one_right (pow_nonneg hgamma.le n) hgamma1.le).trans hn.le
  have hpath := (actual_threshold_policy_has_the_printed_delayed_controlled_trajectory delay hd).1
  refine ⟨delay,hd,?_,?_⟩
  · simp_rw [hpath,(actual_fixed_safe_set_indicator_is_exactly_the_source_delayed_cost _ _).1]
    change (∫ _ω : Ω,(∑'time : ℕ,actualDiscountedTerm gamma delay time) ∂P) ≤ budget
    rw [integral_const]
    have hu : P.real Set.univ=1 := by simp
    rw [hu,one_smul,actual_full_delayed_discounted_cost_is_the_genuine_geometric_tail
      gamma hgamma hgamma1 delay,div_le_iff₀ (sub_pos.mpr hgamma1)]
    exact hp
  · have event : {_ω : Ω | ∃time : ℕ,
        sourcePolicyTrajectory (sourceThresholdPolicy delay) time∉sourceFixedSafeSet}=Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true]
      refine ⟨delay,?_⟩
      rw [hpath]
      simp [sourceThresholdPath,sourceFixedSafeSet]
    rw [event]
    simp

end SafeLearning.CompleteModulesLandscapeControlledDelay
