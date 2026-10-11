import SafeLearning.CompleteMonitoringMeans22
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteMonitoringAchievable22
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteFiniteControlledPathMeasureLaws
open SafeLearning.CompleteFiniteControlledPathFlow
open SafeLearning.CompleteMonitoringMeans22
open SafeLearning.CompleteMonitoringGeometry21
local instance : MeasurableSpace (Fin 3) := ⊤
local instance : MeasurableSingletonClass (Fin 3) := ⟨fun _ => MeasurableSet.of_discrete⟩

def historyLaw (π : HistoryPolicy (Fin 3) Bool) : Measure (ℕ → Fin 3 × Bool) := controlledPathMeasure model π
instance (π : HistoryPolicy (Fin 3) Bool) : IsProbabilityMeasure (historyLaw π) := by unfold historyLaw;infer_instance
def historyMass (π : HistoryPolicy (Fin 3) Bool) (n : ℕ) (s : Fin 3) : ℝ := (historyLaw π).real {path | (path n).1=s}
def historyJoint (π : HistoryPolicy (Fin 3) Bool) (n : ℕ) (s : Fin 3) (a : Bool) : ℝ := (historyLaw π).real {path | (path n).1=s ∧ (path n).2=a}

theorem actual_history_joint_marginal (π : HistoryPolicy (Fin 3) Bool) (n : ℕ) (s : Fin 3) :
    historyJoint π n s false+historyJoint π n s true=historyMass π n s := by
  have h:=actual_joint_state_marginal (historyLaw π) model (fun n path => (path n).1) (fun n path => (path n).2) (actual_constructed_history_path_controlled_law model π) n s
  simpa [jointProbability,stateProbability,historyMass,historyJoint,Fintype.sum_bool,add_comm] using h

theorem actual_history_total_mass (π : HistoryPolicy (Fin 3) Bool) (n : ℕ) :
    historyMass π n 0+historyMass π n 1+historyMass π n 2=1 := by
  have hp:=actual_finite_event_partition (historyLaw π) (fun path => (path n).1) Set.univ
    (fun s => by
      have hm : Measurable (fun path : ℕ → Fin 3 × Bool => path n) := measurable_pi_apply n
      simpa using (measurableSet_singleton s).preimage hm.fst)
  simpa [historyMass,Fin.sum_univ_succ,add_assoc] using hp.symm

theorem actual_history_zero_successor_mass (π : HistoryPolicy (Fin 3) Bool) (n : ℕ) :
    historyMass π (n+1) 0=historyJoint π n 1 false+historyJoint π n 2 false := by
  have h:=actual_history_independent_transition_identity (historyLaw π) model
    (fun n path => (path n).1) (fun n path => (path n).2)
    (actual_constructed_history_path_controlled_law model π) n 0
  simpa [jointProbability,stateProbability,historyMass,historyJoint,model,Fin.sum_univ_succ] using h

theorem actual_every_history_policy_has_the_adjacent_zero_mass_bound
    (π : HistoryPolicy (Fin 3) Bool) (n : ℕ) : historyMass π n 0+historyMass π (n+1) 0 ≤ 1 := by
  have h1:=actual_history_joint_marginal π n 1
  have h2:=actual_history_joint_marginal π n 2
  have ht:=actual_history_total_mass π n
  have hn1 : 0 ≤ historyJoint π n 1 true := measureReal_nonneg
  have hn2 : 0 ≤ historyJoint π n 2 true := measureReal_nonneg
  rw [actual_history_zero_successor_mass]
  linarith

private theorem shifted_sum (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, f (n+1)) = (∑ n ∈ Finset.range N, f n)+f N-f 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,Finset.sum_range_succ,ih];ring

def historyAverage (π : HistoryPolicy (Fin 3) Bool) (N : ℕ) (s : Fin 3) : ℝ :=
  (∑ n ∈ Finset.range N, historyMass π n s)/(N:ℝ)

theorem actual_every_history_policy_has_the_finite_horizon_zero_bound
    (π : HistoryPolicy (Fin 3) Bool) (N : ℕ) :
    2*(∑ n ∈ Finset.range N, historyMass π n 0) ≤ (N:ℝ)+1 := by
  have hsum:=Finset.sum_le_sum (s:=Finset.range N) (fun n _ => actual_every_history_policy_has_the_adjacent_zero_mass_bound π n)
  rw [Finset.sum_add_distrib,shifted_sum (fun k => historyMass π k 0) N] at hsum
  have hn : 0 ≤ historyMass π N 0 := measureReal_nonneg
  have h0 : historyMass π 0 0 ≤ 1 := measureReal_le_one
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hsum
  linarith

theorem actual_every_history_policy_zero_fraction_limit_is_at_most_one_half
    (π : HistoryPolicy (Fin 3) Bool) (v0 : ℝ)
    (hv : Tendsto (fun N => historyAverage π N 0) atTop (𝓝 v0)) : v0 ≤ 1/2 := by
  have hleft : Tendsto (fun N => 2*historyAverage π N 0) atTop (𝓝 (2*v0)) := hv.const_mul 2
  have hright : Tendsto (fun N : ℕ => 1+1/(N:ℝ)) atTop (𝓝 1) := by
    have h:=(tendsto_const_nhds (x:=(1:ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
    simpa using h
  have hbound : (fun N => 2*historyAverage π N 0) ≤ᶠ[atTop] (fun N : ℕ => 1+1/(N:ℝ)) := by
    filter_upwards [eventually_ne_atTop (0:ℕ)] with N hN
    have hn : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have h:=actual_every_history_policy_has_the_finite_horizon_zero_bound π N
    unfold historyAverage
    have ht := (div_le_div_iff_of_pos_right hn).mpr h
    convert ht using 1 <;> field_simp <;> ring
  have h:=le_of_tendsto_of_tendsto hleft hright hbound
  linarith
end SafeLearning.CompleteMonitoringAchievable22
