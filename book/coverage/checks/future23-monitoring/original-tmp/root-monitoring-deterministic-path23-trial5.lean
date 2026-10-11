import SafeLearning.CompleteMonitoringAchievable22
import SafeLearning.CompleteModulesMonitoringBlockLimitsClosed22
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteMonitoringDeterministicPath23
open SafeLearning.CompleteFiniteCMDPOccupancy
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteFiniteControlledPathMeasureLaws
open SafeLearning.CompleteFiniteControlledPathFlow
open SafeLearning.CompleteFiniteMarkovPathCorrespondence
open SafeLearning.CompleteMonitoringMeans22
open SafeLearning.CompleteMonitoringAchievable22
local instance : MeasurableSpace (Fin 3) := ⊤
local instance : MeasurableSingletonClass (Fin 3) := ⟨fun _ => MeasurableSet.of_discrete⟩

def chosenAction (x : ℕ → Fin 3) (hx : ∀ n, ∃ a : Bool, model.transition (x n) a (x (n+1))=1) (n : ℕ) : Bool := Classical.choose (hx n)
def scheduledPolicy (x : ℕ → Fin 3) (hx : ∀ n, ∃ a : Bool, model.transition (x n) a (x (n+1))=1) : Policy (Fin 3) Bool where
  action n _ a := if a=chosenAction x hx n then 1 else 0
  action_nonneg n _ a := by split_ifs <;> norm_num
  action_sum n _ := by cases h : chosenAction x hx n <;> simp [Fintype.sum_bool,h]

theorem actual_admitted_path_scheduled_policy_has_dirac_state_marginals
    (x : ℕ → Fin 3) (h0 : x 0=0)
    (hx : ∀ n, ∃ a : Bool, model.transition (x n) a (x (n+1))=1) (n : ℕ) (s : Fin 3) :
    stateMass model (scheduledPolicy x hx) n s = if s=x n then 1 else 0 := by
  have ht (n : ℕ) : ∀ s, model.transition (x n) (chosenAction x hx n) s=if s=x (n+1) then 1 else 0 := by
    have hh:=Classical.choose_spec (hx n)
    change model.transition (x n) (chosenAction x hx n) (x (n+1))=1 at hh
    let t : Fin 3 := if x n=0 then (if chosenAction x hx n then 2 else 1) else (if chosenAction x hx n then x n else 0)
    change (if x (n+1)=t then (1:ℝ) else 0)=1 at hh
    have he : x (n+1)=t := by
      by_contra he
      simp [he] at hh
    intro s
    change (if s=t then (1:ℝ) else 0)=if s=x (n+1) then 1 else 0
    rw [he]
  induction n generalizing s with
  | zero => simp [stateMass,model,h0]
  | succ n ih =>
    rw [stateMass]
    simp_rw [ih]
    simp [scheduledPolicy,ite_mul,mul_ite,ht]

theorem actual_admitted_path_is_realized_by_a_genuine_controlled_history_policy
    (x : ℕ → Fin 3) (h0 : x 0=0)
    (hx : ∀ n, ∃ a : Bool, model.transition (x n) a (x (n+1))=1) :
    ∀ᵐ sample ∂historyLaw (markovHistoryPolicy (scheduledPolicy x hx)), ∀ n, (sample n).1=x n := by
  apply ae_all_iff.mpr
  intro n
  have hm (a : Bool) := actual_constructed_markov_path_joint_mass model (scheduledPolicy x hx) n (x n) a
  have hp := actual_finite_event_partition (historyLaw (markovHistoryPolicy (scheduledPolicy x hx)))
    (fun sample => (sample n).2) {sample | (sample n).1=x n}
    (fun a => by
      have hma : MeasurableSet {sample : ℕ → Fin 3 × Bool | (sample n).2=a} := (measurableSet_singleton a).preimage (measurable_pi_apply n).snd
      have hms : MeasurableSet {sample : ℕ → Fin 3 × Bool | (sample n).1=x n} := (measurableSet_singleton (x n)).preimage (measurable_pi_apply n).fst
      exact hma.inter hms)
  have he : (historyLaw (markovHistoryPolicy (scheduledPolicy x hx))).real {sample | (sample n).1=x n}=1 := by
    rw [hp]
    simp only [Fintype.sum_bool]
    have hj (a : Bool) : (historyLaw (markovHistoryPolicy (scheduledPolicy x hx))).real
        {sample | (sample n).2=a ∧ sample ∈ {sample | (sample n).1=x n}}=
        (scheduledPolicy x hx).action n (x n) a := by
      have hh := hm a
      rw [jointMass,actual_admitted_path_scheduled_policy_has_dirac_state_marginals x h0 hx n (x n)] at hh
      simpa [historyLaw,Prod.ext_iff,and_comm] using hh
    simp_rw [hj]
    simpa [Fintype.sum_bool] using (scheduledPolicy x hx).action_sum n (x n)
  apply (ae_iff_prob_eq_one (by fun_prop)).mpr
  calc _ = ENNReal.ofReal ((historyLaw (markovHistoryPolicy (scheduledPolicy x hx))).real {sample | (sample n).1=x n}) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = 1 := by rw [he];norm_num


theorem actual_scheduled_controlled_policy_state_probability
    (x : ℕ → Fin 3) (h0 : x 0=0)
    (hx : ∀ n, ∃ a : Bool, model.transition (x n) a (x (n+1))=1) (n : ℕ) (s : Fin 3) :
    historyMass (markovHistoryPolicy (scheduledPolicy x hx)) n s=if s=x n then 1 else 0 := by
  have hj (a : Bool) : historyJoint (markovHistoryPolicy (scheduledPolicy x hx)) n s a=
      stateMass model (scheduledPolicy x hx) n s*(scheduledPolicy x hx).action n s a := by
    simpa [historyJoint,historyLaw,Prod.ext_iff,jointMass] using
      actual_constructed_markov_path_joint_mass model (scheduledPolicy x hx) n s a
  have h:=actual_history_joint_marginal (markovHistoryPolicy (scheduledPolicy x hx)) n s
  rw [hj false,hj true,← mul_add] at h
  have ha:= (scheduledPolicy x hx).action_sum n s
  simp only [Fintype.sum_bool] at ha
  rw [show (scheduledPolicy x hx).action n s false+(scheduledPolicy x hx).action n s true=1 by simpa [add_comm] using ha,mul_one] at h
  rw [←h]
  exact actual_admitted_path_scheduled_policy_has_dirac_state_marginals x h0 hx n s

open SafeLearning.CompleteModulesMonitoringBlocksClosed22
open SafeLearning.CompleteModulesMonitoringBlockLimitsClosed22

def growingPolicy : HistoryPolicy (Fin 3) Bool := markovHistoryPolicy
  (scheduledPolicy path actual_source_growing_block_path_is_admitted.2)

theorem actual_growing_blocks_are_realized_almost_surely_by_the_constructed_history_policy :
    ∀ᵐ sample ∂historyLaw growingPolicy, ∀ n, (sample n).1=path n :=
  actual_admitted_path_is_realized_by_a_genuine_controlled_history_policy path
    actual_source_growing_block_path_is_admitted.1 actual_source_growing_block_path_is_admitted.2

theorem actual_growing_history_policy_expected_fractions_are_the_true_deterministic_fractions
    (T : ℕ) (s : Fin 3) : expectedHistoryFraction growingPolicy T s=fraction T s := by
  rw [actual_expected_history_fraction_equals_its_state_average]
  unfold historyAverage growingPolicy fraction visits
  simp_rw [actual_scheduled_controlled_policy_state_probability path
    actual_source_growing_block_path_is_admitted.1 actual_source_growing_block_path_is_admitted.2]
  push_cast
  simp only [eq_comm]

theorem actual_growing_controlled_history_policy_has_expected_fraction_limits_zero_half_half :
    Tendsto (fun T => expectedHistoryFraction growingPolicy T 0) atTop (𝓝 0) ∧
    Tendsto (fun T => expectedHistoryFraction growingPolicy T 1) atTop (𝓝 (1/2)) ∧
    Tendsto (fun T => expectedHistoryFraction growingPolicy T 2) atTop (𝓝 (1/2)) := by
  simp_rw [actual_growing_history_policy_expected_fractions_are_the_true_deterministic_fractions]
  exact actual_all_horizon_fraction_limits

end SafeLearning.CompleteMonitoringDeterministicPath23
