import SafeLearning.CompleteMonitoringDeficit22
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
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


def prefixPath (n : ℕ) : Fin 3 := if n=0 then 0 else if n=1 then 2 else if n=2 then 0 else 1

theorem actual_deliberate_finite_prefix_monitoring_path_is_admitted :
    prefixPath 0=0 ∧ ∀ n, ∃ a : Bool, model.transition (prefixPath n) a (prefixPath (n+1))=1 := by
  constructor
  · simp [prefixPath]
  intro n
  by_cases h0 : n=0
  · subst n;exact ⟨true,by norm_num [prefixPath,model]⟩
  by_cases h1 : n=1
  · subst n;exact ⟨false,by norm_num [prefixPath,model]⟩
  by_cases h2 : n=2
  · subst n;exact ⟨false,by norm_num [prefixPath,model]⟩
  exact ⟨true,by simp [prefixPath,model,h0,h1,h2,show n+1≠0 by omega,show n+1≠1 by omega,show n+1≠2 by omega]⟩

def prefixPolicy : HistoryPolicy (Fin 3) Bool := markovHistoryPolicy
  (scheduledPolicy prefixPath actual_deliberate_finite_prefix_monitoring_path_is_admitted.2)

theorem actual_finite_prefix_monitoring_policy_has_vertex_one_expected_limits (s : Fin 3) :
    Tendsto (fun T => expectedHistoryFraction prefixPolicy T s) atTop (𝓝 (if s=1 then 1 else 0)) := by
  have hmass : Tendsto (fun n => historyMass prefixPolicy n s) atTop (𝓝 (if s=1 then 1 else 0)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    rw [show prefixPolicy=markovHistoryPolicy (scheduledPolicy prefixPath actual_deliberate_finite_prefix_monitoring_path_is_admitted.2) by rfl,
      actual_scheduled_controlled_policy_state_probability prefixPath
        actual_deliberate_finite_prefix_monitoring_path_is_admitted.1 actual_deliberate_finite_prefix_monitoring_path_is_admitted.2]
    simp [prefixPath,show n≠0 by omega,show n≠1 by omega,show n≠2 by omega]
  have h:=hmass.cesaro
  simp_rw [actual_expected_history_fraction_equals_its_state_average]
  simpa [historyAverage,div_eq_mul_inv,mul_comm] using h

theorem actual_long_run_lagrangian_maximization_does_not_force_the_first_region_action :
    historyMass prefixPolicy 1 2=1 ∧
    Tendsto (fun T => expectedHistoryFraction prefixPolicy T 0) atTop (𝓝 0) ∧
    Tendsto (fun T => expectedHistoryFraction prefixPolicy T 1) atTop (𝓝 1) ∧
    Tendsto (fun T => expectedHistoryFraction prefixPolicy T 2) atTop (𝓝 0) ∧
    SafeLearning.CompleteMonitoringGeometry21.IsMaximizer 2 0 SafeLearning.CompleteMonitoringGeometry21.vertex1 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [show prefixPolicy=markovHistoryPolicy (scheduledPolicy prefixPath actual_deliberate_finite_prefix_monitoring_path_is_admitted.2) by rfl,
      actual_scheduled_controlled_policy_state_probability prefixPath
        actual_deliberate_finite_prefix_monitoring_path_is_admitted.1 actual_deliberate_finite_prefix_monitoring_path_is_admitted.2]
    norm_num [prefixPath]
  · simpa using actual_finite_prefix_monitoring_policy_has_vertex_one_expected_limits 0
  · simpa using actual_finite_prefix_monitoring_policy_has_vertex_one_expected_limits 1
  · simpa using actual_finite_prefix_monitoring_policy_has_vertex_one_expected_limits 2
  · refine ⟨SafeLearning.CompleteMonitoringGeometry21.actual_four_vertices_and_primal_optimum_in_the_polytope.1,?_⟩
    intro v hv
    exact SafeLearning.CompleteMonitoringGeometry21.actual_larger_first_price_above_one_vertex_bound 2 0 (by norm_num) (by norm_num) v hv

end SafeLearning.CompleteMonitoringDeterministicPath23

namespace SafeLearning.CompleteMonitoringDualTrajectory23
open SafeLearning.CompleteMonitoringDeterministicPath23
open SafeLearning.CompleteMonitoringMeans22
open SafeLearning.CompleteMonitoringDeficit22
structure AugmentedState where
  physical : Fin 3
  first : ℕ
  second : ℕ
  deriving DecidableEq

def selector (z : AugmentedState) : Bool :=
  if z.physical=0 then decide (z.first<z.second)
  else if z.physical=1 then decide (max 3 z.second<z.first)
  else decide (max 3 z.first<z.second)

def step (z : AugmentedState) : AugmentedState where
  physical := if z.physical=0 then (if selector z then 2 else 1)
    else (if selector z then z.physical else 0)
  first := z.first+1-(if z.physical=1 then 3 else 0)
  second := z.second+1-(if z.physical=2 then 3 else 0)

def trajectory : ℕ → AugmentedState
  | 0 => ⟨0,0,0⟩
  | n+1 => step (trajectory n)

def cycle (r : ℕ) : AugmentedState :=
  if r=0 then ⟨1,3,2⟩ else if r=1 then ⟨0,1,3⟩
  else if r=2 then ⟨2,2,4⟩ else if r=3 then ⟨2,3,2⟩
  else if r=4 then ⟨0,4,0⟩ else ⟨1,5,1⟩

theorem actual_initial_five_steps_enter_the_six_cycle : trajectory 5=cycle 0 := by
  norm_num [trajectory,step,selector,cycle]

theorem actual_cycle_step (n : ℕ) : step (cycle (n%6))=cycle ((n+1)%6) := by
  have hn : n%6<6 := Nat.mod_lt _ (by omega)
  have hm : (n+1)%6=(n%6+1)%6 := by omega
  rw [hm]
  interval_cases h : n%6 <;> norm_num [cycle,step,selector]

theorem actual_projected_dual_rollout_has_an_exact_six_periodic_tail (n : ℕ) :
    trajectory (n+5)=cycle (n%6) := by
  induction n with
  | zero => simpa using actual_initial_five_steps_enter_the_six_cycle
  | succ n ih =>
    rw [show n+1+5=(n+5)+1 by omega,trajectory,ih,actual_cycle_step]

theorem actual_projected_monitoring_trajectory_is_admitted :
    (trajectory 0).physical=0 ∧ ∀ n, model.transition (trajectory n).physical
      (selector (trajectory n)) (trajectory (n+1)).physical=1 := by
  constructor
  · rfl
  intro n
  simp only [trajectory,step]
  simp [model]

theorem actual_scaled_prices_stay_bounded (n : ℕ) :
    (trajectory n).first ≤ 5 ∧ (trajectory n).second ≤ 4 := by
  by_cases h : n<5
  · interval_cases n <;> norm_num [trajectory,step,selector]
  · obtain ⟨k,rfl⟩ : ∃ k, n=k+5 := ⟨n-5,by omega⟩
    rw [actual_projected_dual_rollout_has_an_exact_six_periodic_tail]
    have hk : k%6<6 := Nat.mod_lt _ (by omega)
    interval_cases h : k%6 <;> norm_num [cycle]

end SafeLearning.CompleteMonitoringDualTrajectory23
