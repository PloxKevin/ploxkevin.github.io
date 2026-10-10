import SafeLearning.CompleteModulesGoSafeBackupConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeHiddenState
open CompleteModulesGoSafeBackupConsequences

def hiddenControllerFlow : ClosedLoop (ℝ×Bool) where
  path := fun time state=>(if state.2 then state.1-time else state.1,state.2)
  start := by rintro ⟨p,flag⟩;cases flag <;> simp
  restart := by
    intro t s state ht hs
    rcases state with ⟨p,flag⟩
    cases flag <;> simp
    ring

def controllerPositionMargin (state : ℝ×Bool) : ℝ := 1-|state.1|

theorem actual_same_observed_position_hides_two_different_controller_futures :
    ((0:ℝ),false).1=((0:ℝ),true).1 ∧
      (∀ time : ℝ,0 ≤ time→controllerPositionMargin (hiddenControllerFlow.path time (0,false))=1) ∧
      controllerPositionMargin (hiddenControllerFlow.path 2 (0,true))= -1 ∧
      hiddenControllerFlow.path 2 (0,false)≠hiddenControllerFlow.path 2 (0,true) := by
  norm_num [hiddenControllerFlow,controllerPositionMargin]

theorem actual_omitting_hidden_controller_state_breaks_safety_of_a_position_only_restart :
    IsLeast (trajectoryMargins hiddenControllerFlow controllerPositionMargin (0,false)) 1 ∧
      (0:ℝ) ≤ controllerPositionMargin (hiddenControllerFlow.path 0 (0,false)) ∧
      controllerPositionMargin (hiddenControllerFlow.path 2 (0,true))<0 := by
  constructor
  · constructor
    · exact ⟨0,by norm_num,by norm_num [hiddenControllerFlow,controllerPositionMargin]⟩
    · rintro value ⟨time,ht,rfl⟩
      norm_num [hiddenControllerFlow,controllerPositionMargin]
  norm_num [hiddenControllerFlow,controllerPositionMargin]

/-- The second state component is the clock required to make this autonomous. -/
def hiddenClockFlow : ClosedLoop (ℝ×ℝ) where
  path := fun time state=>(state.1+time^2+2*state.2*time,state.2+time)
  start := by rintro ⟨p,clock⟩;simp
  restart := by
    intro t s state ht hs
    rcases state with ⟨p,clock⟩
    apply Prod.ext <;> simp <;> ring

def clockPositionMargin (state : ℝ×ℝ) : ℝ := state.1

theorem actual_same_position_with_an_omitted_clock_can_have_an_unsafe_restart :
    ((1/5:ℝ),0).1=((1/5:ℝ),-1).1 ∧
      (∀ time : ℝ,0 ≤ time→(1/5:ℝ) ≤ clockPositionMargin (hiddenClockFlow.path time (1/5,0))) ∧
      clockPositionMargin (hiddenClockFlow.path 1 (1/5,-1))= -4/5 := by
  constructor
  · rfl
  constructor
  · intro time ht
    dsimp [clockPositionMargin,hiddenClockFlow]
    nlinarith [sq_nonneg time]
  norm_num [clockPositionMargin,hiddenClockFlow]

theorem actual_recording_the_clock_gives_a_genuine_point_two_infimum_attainer :
    IsLeast (trajectoryMargins hiddenClockFlow clockPositionMargin (1/5,0)) (1/5:ℝ) := by
  constructor
  · exact ⟨0,by norm_num,by norm_num [hiddenClockFlow,clockPositionMargin]⟩
  · rintro value ⟨time,ht,rfl⟩
    dsimp [clockPositionMargin,hiddenClockFlow]
    nlinarith [sq_nonneg time]

end SafeLearning.CompleteModulesGoSafeHiddenState
