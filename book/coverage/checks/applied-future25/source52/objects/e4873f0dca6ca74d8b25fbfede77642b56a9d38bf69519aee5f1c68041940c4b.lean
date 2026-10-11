import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteModulesLandscapeNotation

def controlClosedLoop {S A : Type*} (f : S→A→S) (policy : S→A) (x : S) : S :=
  f x (policy x)
def rlClosedLoop {S A : Type*} (f : S→A→S) (policy : S→A) (s : S) : S :=
  f s (policy s)

theorem actual_control_to_rl_notation_preserves_the_closed_loop_update
    {S A : Type*} (f : S→A→S) (policy : S→A) (state : S) :
    controlClosedLoop f policy state=rlClosedLoop f policy state ∧
    rlClosedLoop f policy state=f state (policy state) := ⟨rfl,rfl⟩

theorem actual_control_trajectory_and_policy_have_the_source_rl_recurrence
    {S A : Type*} (f : S→A→S) (policy : S→A)
    (state : ℕ→S) (action : ℕ→A)
    (policy_rule : ∀t,action t=policy (state t))
    (transition_rule : ∀t,state (t+1)=f (state t) (action t)) :
    ∀t,state (t+1)=f (state t) (policy (state t)) := by
  intro t;rw [transition_rule,policy_rule]

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

def stochasticClosedLoop (transition : Kernel (S×A) S) (policy : Kernel S A) : Kernel S S :=
  transition ∘ₖ (Kernel.id ×ₖ policy)

instance stochasticClosedLoop_markov (transition : Kernel (S×A) S) (policy : Kernel S A)
    [IsMarkovKernel transition] [IsMarkovKernel policy] :
    IsMarkovKernel (stochasticClosedLoop transition policy) := by
  unfold stochasticClosedLoop;infer_instance

theorem actual_stochastic_transition_and_policy_are_probability_laws
    (transition : Kernel (S×A) S) (policy : Kernel S A)
    [IsMarkovKernel transition] [IsMarkovKernel policy] :
    (∀s a,IsProbabilityMeasure (transition (s,a))) ∧
    (∀s,IsProbabilityMeasure (policy s)) := by
  constructor <;> intros <;> infer_instance

theorem actual_state_and_randomized_action_joint_law
    (policy : Kernel S A) [IsMarkovKernel policy] (state : S) :
    (Kernel.id ×ₖ policy) state=(Measure.dirac state).prod (policy state) := by
  rw [Kernel.prod_apply,Kernel.id_apply]

theorem actual_closed_loop_next_state_law_is_normalized
    (transition : Kernel (S×A) S) (policy : Kernel S A)
    [IsMarkovKernel transition] [IsMarkovKernel policy] (state : S) :
    stochasticClosedLoop transition policy state Set.univ=1 := by
  exact measure_univ

def actualNextStateLaw (initial : Measure S) (transition : Kernel (S×A) S)
    (policy : Kernel S A) : Measure S := stochasticClosedLoop transition policy ∘ₘ initial

theorem actual_initial_action_and_transition_laws_form_a_probability_measure
    (initial : Measure S) (transition : Kernel (S×A) S) (policy : Kernel S A)
    [IsProbabilityMeasure initial] [IsMarkovKernel transition] [IsMarkovKernel policy] :
    IsProbabilityMeasure (actualNextStateLaw initial transition policy) := by
  unfold actualNextStateLaw;infer_instance

theorem actual_deterministic_transition_and_policy_reduce_to_the_literal_source_map
    (f : S→A→S) (policy : S→A)
    (hf : Measurable (fun pair : S×A =>f pair.1 pair.2)) (hp : Measurable policy) :
    stochasticClosedLoop (Kernel.deterministic (fun pair : S×A =>f pair.1 pair.2) hf)
      (Kernel.deterministic policy hp)=
    Kernel.deterministic (fun state =>f state (policy state))
      (hf.comp (measurable_id.prodMk hp)) := by
  unfold stochasticClosedLoop Kernel.id
  rw [Kernel.deterministic_prod_deterministic measurable_id hp]
  exact Kernel.deterministic_comp_deterministic (measurable_id.prodMk hp) hf

end SafeLearning.CompleteModulesLandscapeNotation
