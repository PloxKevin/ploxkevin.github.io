import SafeLearning.CompleteModulesChowVisitCost21
import SafeLearning.CompleteChowLP21

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteModulesChowControlled21
open SafeLearning.CompleteFiniteCMDPOccupancy
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteFiniteControlledPathMeasureLaws
open SafeLearning.CompleteFiniteControlledPathFlow
open SafeLearning.CompleteModulesChowVisitCost21
local instance : MeasurableSpace (Fin 4) := ⊤
local instance : MeasurableSingletonClass (Fin 4) := ⟨fun _ => MeasurableSet.of_discrete⟩

private theorem sum_bool_false_first (f : Bool → ℝ) : (∑ a, f a)=f false+f true := by
  simp [Fintype.sum_bool,add_comm]

/-- Fixed two-action model: false is the baseline action and true is the fast action.
The model does not depend on the policy's mixing probability. -/
def model : Model (Fin 4) Bool where
  initial s := if s=0 then 1 else 0
  initial_nonneg s := by split_ifs <;> norm_num
  initial_sum := by simp
  transition s a t := fullKernel (if a then 1 else 0) s t
  transition_nonneg s a t := by
    cases a <;> fin_cases s <;> fin_cases t <;> norm_num [fullKernel]
  transition_sum s a := by
    cases a <;> fin_cases s <;> norm_num [fullKernel,Fin.sum_univ_succ]

def law (π : HistoryPolicy (Fin 4) Bool) : Measure (ℕ → Fin 4 × Bool) :=
  controlledPathMeasure model π

instance (π : HistoryPolicy (Fin 4) Bool) : IsProbabilityMeasure (law π) := by
  unfold law
  infer_instance

def initialMix (π : HistoryPolicy (Fin 4) Bool) : ℝ :=
  π.action 0 (fun i => Fin.elim0 i) 0 true

def mass (π : HistoryPolicy (Fin 4) Bool) (n : ℕ) (s : Fin 4) : ℝ :=
  (law π).real {path | (path n).1=s}

def joint (π : HistoryPolicy (Fin 4) Bool) (n : ℕ) (s : Fin 4) (a : Bool) : ℝ :=
  (law π).real {path | (path n).1=s ∧ (path n).2=a}

theorem actual_initial_policy_mixing_probability_is_in_the_unit_interval
    (π : HistoryPolicy (Fin 4) Bool) : 0 ≤ initialMix π ∧ initialMix π ≤ 1 := by
  have hf := π.action_nonneg 0 (fun i => Fin.elim0 i) 0 false
  have ht := π.action_nonneg 0 (fun i => Fin.elim0 i) 0 true
  have hs := π.action_sum 0 (fun i => Fin.elim0 i) 0
  simp only [sum_bool_false_first] at hs
  exact ⟨ht,by unfold initialMix; linarith⟩

theorem actual_initial_false_action_probability_is_one_minus_the_true_probability
    (π : HistoryPolicy (Fin 4) Bool) :
    π.action 0 (fun i => Fin.elim0 i) 0 false=1-initialMix π := by
  have hs := π.action_sum 0 (fun i => Fin.elim0 i) 0
  simp only [sum_bool_false_first] at hs
  unfold initialMix
  linarith

theorem actual_history_joint_masses_sum_to_the_state_mass
    (π : HistoryPolicy (Fin 4) Bool) (n : ℕ) (s : Fin 4) :
    joint π n s false+joint π n s true=mass π n s := by
  have h := actual_joint_state_marginal (law π) model
    (fun n path => (path n).1) (fun n path => (path n).2)
    (actual_constructed_history_path_controlled_law model π) n s
  simpa only [sum_bool_false_first,jointProbability,stateProbability,joint,mass,law] using h

theorem actual_history_state_masses_follow_the_fixed_two_action_model
    (π : HistoryPolicy (Fin 4) Bool) (n : ℕ) (t : Fin 4) :
    mass π (n+1) t=∑ s : Fin 4,
      (joint π n s false*fullKernel 0 s t+joint π n s true*fullKernel 1 s t) := by
  have h := actual_history_independent_transition_identity (law π) model
    (fun n path => (path n).1) (fun n path => (path n).2)
    (actual_constructed_history_path_controlled_law model π) n t
  simpa only [sum_bool_false_first,jointProbability,stateProbability,joint,mass,law,
    model,Bool.false_eq_true,ite_false,ite_true] using h

theorem actual_initial_history_joint_mass
    (π : HistoryPolicy (Fin 4) Bool) (s : Fin 4) (a : Bool) :
    joint π 0 s a=(if s=0 then 1 else 0)*π.action 0 (fun i => Fin.elim0 i) s a := by
  have h := actual_initial_joint_event_probability model π (s,a)
  simpa only [joint,law,Prod.ext_iff,initialJoint,model] using h

theorem actual_initial_state_mass (π : HistoryPolicy (Fin 4) Bool) (s : Fin 4) :
    mass π 0 s=if s=0 then 1 else 0 := by
  exact actual_constructed_path_initial_state_law model π s

theorem actual_no_policy_can_return_to_the_initial_state
    (π : HistoryPolicy (Fin 4) Bool) (n : ℕ) : mass π (n+1) 0=0 := by
  rw [actual_history_state_masses_follow_the_fixed_two_action_model]
  apply Finset.sum_eq_zero
  intro s _
  fin_cases s <;> norm_num [fullKernel]

theorem actual_history_joint_initial_state_mass_vanishes_after_time_zero
    (π : HistoryPolicy (Fin 4) Bool) (n : ℕ) (a : Bool) : joint π (n+1) 0 a=0 := by
  have h := actual_history_joint_masses_sum_to_the_state_mass π (n+1) 0
  rw [actual_no_policy_can_return_to_the_initial_state] at h
  have hf : 0 ≤ joint π (n+1) 0 false := measureReal_nonneg
  have ht : 0 ≤ joint π (n+1) 0 true := measureReal_nonneg
  cases a <;> linarith

theorem actual_actions_only_change_the_first_transition
    (p : ℝ) (s : Fin 4) (hs : s≠0) (t : Fin 4) :
    fullKernel 0 s t=fullKernel p s t ∧ fullKernel 1 s t=fullKernel p s t := by
  fin_cases s <;> fin_cases t <;> norm_num [fullKernel] at *

theorem actual_every_history_policy_has_the_literal_matrix_power_marginals
    (π : HistoryPolicy (Fin 4) Bool) (n : ℕ) (j : Fin 3) :
    mass π n j.castSucc=(transientKernel (initialMix π)^n) 0 j := by
  induction n generalizing j with
  | zero =>
      rw [actual_initial_state_mass]
      simp [Matrix.one_apply,eq_comm]
  | succ n ih =>
      rw [actual_history_state_masses_follow_the_fixed_two_action_model]
      have ht0 : fullKernel 0 (Fin.last 3) j.castSucc=0 :=
        actual_terminal_state_cannot_return_to_a_nonterminal_state 0 j
      have ht1 : fullKernel 1 (Fin.last 3) j.castSucc=0 :=
        actual_terminal_state_cannot_return_to_a_nonterminal_state 1 j
      rw [Fin.sum_univ_castSucc,ht0,ht1,mul_zero,mul_zero,add_zero,add_zero]
      rw [pow_succ,Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i=0
      · subst i
        cases n with
        | zero =>
            rw [Fin.castSucc_zero,actual_initial_history_joint_mass,actual_initial_history_joint_mass]
            simp only [ite_true,one_mul]
            rw [actual_initial_false_action_probability_is_one_minus_the_true_probability]
            change (1-initialMix π)*fullKernel 0 0 j.castSucc+
              initialMix π*fullKernel 1 0 j.castSucc =
              (transientKernel (initialMix π)^0) 0 0 * transientKernel (initialMix π) 0 j
            fin_cases j <;> norm_num [fullKernel,transientKernel] <;> ring
        | succ n =>
            rw [Fin.castSucc_zero,actual_history_joint_initial_state_mass_vanishes_after_time_zero,
              actual_history_joint_initial_state_mass_vanishes_after_time_zero]
            have hz := actual_no_policy_can_return_to_the_initial_state π n
            have hi0 := ih (0 : Fin 3)
            change mass π (n+1) 0=(transientKernel (initialMix π)^(n+1)) 0 0 at hi0
            rw [hz] at hi0
            rw [← hi0]
            ring
      · have his : i.castSucc≠(0 : Fin 4) := by
          intro h
          apply hi
          exact Fin.castSucc_inj.mp (h.trans Fin.castSucc_zero.symm)
        obtain ⟨hf,ht⟩ := actual_actions_only_change_the_first_transition
          (initialMix π) i.castSucc his j.castSucc
        rw [hf,ht,← add_mul,actual_history_joint_masses_sum_to_the_state_mass,ih,
          actual_full_chain_restricts_to_the_literal_nonterminal_kernel]

end SafeLearning.CompleteModulesChowControlled21
