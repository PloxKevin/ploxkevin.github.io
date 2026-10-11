import SafeLearning.CompleteMonitoringMeans22
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteMonitoringTrapping22
open SafeLearning.CompleteFiniteCMDPOccupancy
open SafeLearning.CompleteFiniteMarkovPathCorrespondence
open SafeLearning.CompleteFiniteControlledPathMeasureLaws
open SafeLearning.CompleteMonitoringMeans22
local instance : MeasurableSpace (Fin 3) := ⊤
local instance : MeasurableSingletonClass (Fin 3) := ⟨fun _ => MeasurableSet.of_discrete⟩
variable (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
local notation "μ" => law q 0 hq0 hq1 (le_refl 0) (by norm_num)

theorem actual_no_return_region_exit_event_has_zero_probability
    (n : ℕ) (s t : Fin 3) (hs : s≠0) (ht : t≠s) :
    (μ).real {path | (path n).1=s ∧ (path (n+1)).1=t}=0 := by
  have hp := SafeLearning.CompleteFiniteControlledPathFlow.actual_finite_event_partition μ
    (fun path => (path n).2) {path | (path n).1=s ∧ (path (n+1)).1=t}
    (fun a : Bool => by
      have ha : MeasurableSet {path : ℕ → Fin 3 × Bool | (path n).2=a} := (measurableSet_singleton a).preimage (measurable_pi_apply n).snd
      have hb : MeasurableSet {path : ℕ → Fin 3 × Bool | (path n).1=s} := (measurableSet_singleton s).preimage (measurable_pi_apply n).fst
      have hc : MeasurableSet {path : ℕ → Fin 3 × Bool | (path (n+1)).1=t} := (measurableSet_singleton t).preimage (measurable_pi_apply (n+1)).fst
      simpa only [Set.inter_def,Set.mem_ofPred_eq] using ha.inter (hb.inter hc))
  rw [hp]
  apply Finset.sum_eq_zero
  intro a _
  have h := actual_constructed_path_has_the_controlled_transition_law model
    (markovHistoryPolicy (policy q 0 hq0 hq1 (le_refl 0) (by norm_num))) n s a t
  have hj := actual_constructed_markov_path_joint_mass model
    (policy q 0 hq0 hq1 (le_refl 0) (by norm_num)) n s a
  have he : {path : ℕ → Fin 3 × Bool | (path n).1=s ∧ (path n).2=a} = {path | path n=(s,a)} := by ext path;simp [Prod.ext_iff]
  rw [he,hj] at h
  cases a <;> simpa [law,model,policy,jointMass,hs,ht,and_assoc,and_comm,and_left_comm] using h

theorem actual_stationary_no_return_paths_remain_in_the_first_region_almost_surely :
    ∀ᵐ path ∂μ, (path 0).1=0 ∧ (path 1).1≠0 ∧ ∀ n : ℕ, (path (n+1)).1=(path 1).1 := by
  have hi0 : ∀ᵐ path ∂μ, (path 0).1=0 := by
    have h := actual_path_state_event_probability q 0 hq0 hq1 (le_refl 0) (by norm_num) 0 0
    simp [stateMass,model] at h
    have he : μ {path | (path 0).1=0} = 1 := by
      apply ENNReal.toReal_eq_toReal (measure_ne_top _ _) ENNReal.one_ne_top |>.mp
      simpa only [measureReal_def,ENNReal.toReal_one] using h
    exact (ae_iff_prob_eq_one (by fun_prop)).mpr he
  have hi1 : ∀ᵐ path ∂μ, (path 1).1≠0 := by
    have h := actual_path_state_event_probability q 0 hq0 hq1 (le_refl 0) (by norm_num) 1 0
    rw [(actual_source_chain_closed_marginals q 0 hq0 hq1 (le_refl 0) (by norm_num) 1).1] at h
    norm_num at h
    exact measure_eq_zero_iff_ae_notMem.mp ((measureReal_eq_zero_iff).mp h)
  have hbad (n : ℕ) (s t : Fin 3) : ∀ᵐ path ∂μ,
      s≠0 → t≠s → ¬((path n).1=s ∧ (path (n+1)).1=t) := by
    by_cases hs : s=0
    · simp [hs]
    by_cases ht : t=s
    · simp [ht]
    have h := actual_no_return_region_exit_event_has_zero_probability q hq0 hq1 n s t hs ht
    exact (measure_eq_zero_iff_ae_notMem.mp ((measureReal_eq_zero_iff).mp h)).mono (fun _ h => by simpa [hs,ht] using h)
  have hall : ∀ᵐ path ∂μ, ∀ n : ℕ, ∀ s t : Fin 3, s≠0 → t≠s → ¬((path n).1=s ∧ (path (n+1)).1=t) :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun s => ae_all_iff.mpr (hbad n s)))
  filter_upwards [hi0,hi1,hall] with path h0 h1 hp
  refine ⟨h0,h1,?_⟩
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    by_contra hh
    exact hp (n+1) (path 1).1 (path (n+1+1)).1 h1 hh ⟨ih,rfl⟩

def pathFraction (path : ℕ → Fin 3 × Bool) (N : ℕ) (s : Fin 3) : ℝ :=
  (∑ n ∈ Finset.range N, if (path n).1=s then (1:ℝ) else 0)/(N:ℝ)

theorem actual_each_stationary_no_return_trajectory_starves_a_region_almost_surely :
    ∀ᵐ path ∂μ, ∃ s : Fin 3, (s=1 ∨ s=2) ∧ ∀ N : ℕ, pathFraction path N s=0 := by
  filter_upwards [actual_stationary_no_return_paths_remain_in_the_first_region_almost_surely q hq0 hq1] with path hp
  have hchosen : (path 1).1=1 ∨ (path 1).1=2 := by
    have hh:=hp.2.1
    generalize hx : (path 1).1=s at *
    fin_cases s <;> norm_num at * <;> tauto
  have hz (s : Fin 3) (hs0 : s≠0) (hsc : s≠(path 1).1) : ∀ N, pathFraction path N s=0 := by
    intro N
    have hnever : ∀ n, (path n).1≠s := by
      intro n
      cases n with
      | zero => simpa only [hp.1] using hs0.symm
      | succ n => simpa only [hp.2.2 n] using hsc.symm
    simp [pathFraction,hnever]
  rcases hchosen with h | h
  · refine ⟨2,Or.inr rfl,hz 2 (by decide) ?_⟩
    simp [h]
  · refine ⟨1,Or.inl rfl,hz 1 (by decide) ?_⟩
    simp [h]

theorem actual_stationary_no_return_expected_feasibility_interval :
    (1/3 ≤ q ∧ 1/3 ≤ 1-q) ↔ (1/3 ≤ q ∧ q ≤ 2/3) := by constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem actual_monitoring_has_a_strict_slater_policy_with_margin_one_fifteenth :
    Tendsto (fun N => expectedPathFraction (1/2) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) N 1) atTop (𝓝 (1/3+1/15)) ∧
    Tendsto (fun N => expectedPathFraction (1/2) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) N 2) atTop (𝓝 (1/3+1/15)) := by
  have h:=actual_expected_path_fraction_limits (1/2) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · convert h.2.1 using 1 <;> norm_num
  · convert h.2.2 using 1 <;> norm_num

end SafeLearning.CompleteMonitoringTrapping22
