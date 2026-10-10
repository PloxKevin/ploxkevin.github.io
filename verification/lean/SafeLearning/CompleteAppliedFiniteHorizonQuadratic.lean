import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteAppliedFiniteHorizonQuadratic

def nextState (state input : ℝ) : ℝ := state+input
def finalStepCost (state input : ℝ) : ℝ := input^2+(nextState state input)^2
def finalStepValue (state : ℝ) : ℝ := sInf (range (finalStepCost state))
def firstStepCost (state input : ℝ) : ℝ := input^2+finalStepValue (nextState state input)
def twoStepCost (state first second : ℝ) : ℝ :=
  first^2+second^2+(nextState (nextState state first) second)^2

theorem actual_final_step_completed_square (state input : ℝ) :
    finalStepCost state input=state^2/2+2*(input+state/2)^2 := by
  simp only [finalStepCost,nextState];ring

theorem actual_final_step_global_minimum_and_unique_input (state : ℝ) :
    IsLeast (range (finalStepCost state)) (state^2/2) ∧
    ∀input : ℝ,finalStepCost state input=state^2/2↔input= -state/2 := by
  constructor
  · constructor
    · refine ⟨-state/2,?_⟩;rw [actual_final_step_completed_square];ring
    · rintro value ⟨input,rfl⟩
      rw [actual_final_step_completed_square];nlinarith [sq_nonneg (input+state/2)]
  · intro input
    rw [actual_final_step_completed_square]
    constructor
    · intro h;have hz : (input+state/2)^2=0 := by linarith
      have he := sq_eq_zero_iff.mp hz;linarith
    · intro h;subst input;ring

theorem actual_final_step_bellman_value (state : ℝ) :
    finalStepValue state=state^2/2 := by
  exact (actual_final_step_global_minimum_and_unique_input state).1.csInf_eq

theorem actual_final_step_derivative_and_positive_second_derivative (state input : ℝ) :
    HasDerivAt (finalStepCost state) (4*input+2*state) input ∧
    HasDerivAt (fun u : ℝ=>4*u+2*state) 4 input := by
  constructor
  · convert ((hasDerivAt_id input).pow 2).add
      (((hasDerivAt_const input state).add (hasDerivAt_id input)).pow 2) using 1 <;>
      (try ext u) <;> (try dsimp [finalStepCost,nextState]) <;> ring
  · convert ((hasDerivAt_id input).const_mul 4).add_const (2*state) using 1 <;>
      (try ext u) <;> (try dsimp) <;> ring

theorem actual_one_step_source_optimum_and_comparison :
    nextState 2 (-1)=1 ∧ finalStepCost 2 (-1)=2 ∧
    IsLeast (range (finalStepCost 2)) 2 ∧
    (∀u : ℝ,finalStepCost 2 u=2↔u= -1) ∧ finalStepCost 2 (-2)=4 ∧
    HasDerivAt (finalStepCost 2) 0 (-1) := by
  have h := actual_final_step_global_minimum_and_unique_input 2
  have hd := (actual_final_step_derivative_and_positive_second_derivative 2 (-1)).1
  norm_num at h hd
  norm_num [nextState,finalStepCost]
  exact ⟨h.1,h.2,hd⟩

theorem actual_first_step_completed_square (state input : ℝ) :
    firstStepCost state input=state^2/3+(3/2:ℝ)*(input+state/3)^2 := by
  rw [firstStepCost,actual_final_step_bellman_value]
  simp only [nextState];ring

theorem actual_first_step_derivative (state input : ℝ) :
    HasDerivAt (firstStepCost state) (3*input+state) input := by
  have he : firstStepCost state=(fun u : ℝ=>u^2+(state+u)^2/2) := by
    funext u;rw [firstStepCost,actual_final_step_bellman_value];rfl
  rw [he]
  convert ((hasDerivAt_id input).pow 2).add
    ((((hasDerivAt_const input state).add (hasDerivAt_id input)).pow 2).div_const 2) using 1 <;>
      (try ext u) <;> (try dsimp) <;> ring

theorem actual_first_step_global_minimum_and_unique_input (state : ℝ) :
    IsLeast (range (firstStepCost state)) (state^2/3) ∧
    ∀input : ℝ,firstStepCost state input=state^2/3↔input= -state/3 := by
  constructor
  · constructor
    · refine ⟨-state/3,?_⟩;rw [actual_first_step_completed_square];ring
    · rintro value ⟨input,rfl⟩
      rw [actual_first_step_completed_square];nlinarith [sq_nonneg (input+state/3)]
  · intro input;rw [actual_first_step_completed_square]
    constructor
    · intro h;have hz : (input+state/3)^2=0 := by linarith
      have he := sq_eq_zero_iff.mp hz;linarith
    · intro h;subst input;ring

theorem actual_two_step_bellman_inner_minimum (state first : ℝ) :
    IsLeast (range (twoStepCost state first)) (firstStepCost state first) := by
  have h := (actual_final_step_global_minimum_and_unique_input (nextState state first)).1
  have he (second : ℝ) : twoStepCost state first second=
      first^2+finalStepCost (nextState state first) second := by
    simp only [twoStepCost,finalStepCost];ring
  constructor
  · refine ⟨-(nextState state first)/2,?_⟩
    rw [he]
    rw [actual_final_step_completed_square]
    rw [firstStepCost,actual_final_step_bellman_value]
    ring
  · rintro value ⟨second,rfl⟩
    have hi := h.2 ⟨second,rfl⟩
    rw [firstStepCost,actual_final_step_bellman_value]
    rw [he]
    linarith

theorem actual_two_step_source_controls_states_and_total_optimum :
    finalStepValue 2=2 ∧ nextState 3 (-1)=2 ∧ nextState 2 (-1)=1 ∧
    firstStepCost 3 (-1)=3 ∧ twoStepCost 3 (-1) (-1)=3 ∧
    (∀first second : ℝ,3≤twoStepCost 3 first second) ∧
    (∀first second : ℝ,twoStepCost 3 first second=3↔first= -1 ∧ second= -1) ∧
    HasDerivAt (firstStepCost 3) 0 (-1) := by
  have hv := actual_final_step_bellman_value 2
  have hfirst := actual_first_step_global_minimum_and_unique_input 3
  have hd := actual_first_step_derivative 3 (-1)
  norm_num at hv hfirst hd
  refine ⟨hv,by norm_num [nextState],by norm_num [nextState],?_,
    by norm_num [twoStepCost,nextState],?_,?_,hd⟩
  · rw [actual_first_step_completed_square];norm_num
  · intro first second
    exact (hfirst.1.2 ⟨first,rfl⟩).trans
      ((actual_two_step_bellman_inner_minimum 3 first).2 ⟨second,rfl⟩)
  · intro first second
    have hc : twoStepCost 3 first second=3+
        (3/2:ℝ)*(first+1)^2+2*(second+(3+first)/2)^2 := by
      simp only [twoStepCost,nextState];ring
    rw [hc]
    constructor
    · intro h
      have h0 : (first+1)^2=0 := by nlinarith [sq_nonneg (second+(3+first)/2)]
      have h1 : (second+(3+first)/2)^2=0 := by nlinarith [sq_nonneg (first+1)]
      have e0 := sq_eq_zero_iff.mp h0
      have e1 := sq_eq_zero_iff.mp h1
      constructor <;> linarith
    · rintro ⟨rfl,rfl⟩;norm_num

end SafeLearning.CompleteAppliedFiniteHorizonQuadratic
