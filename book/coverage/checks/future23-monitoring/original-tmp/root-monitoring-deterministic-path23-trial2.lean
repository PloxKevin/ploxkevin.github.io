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
    simp only [model] at hh ⊢
    split_ifs at hh with he
    · intro s
      rw [he]
    · norm_num at hh
  induction n generalizing s with
  | zero => simp [stateMass,model,h0]
  | succ n ih =>
    simp only [stateMass,ih,scheduledPolicy]
    simp_rw [ite_mul,mul_ite,one_mul,zero_mul]
    simp [ht]

theorem actual_admitted_path_is_realized_by_a_genuine_controlled_history_policy
    (x : ℕ → Fin 3) (h0 : x 0=0)
    (hx : ∀ n, ∃ a : Bool, model.transition (x n) a (x (n+1))=1) :
    ∀ᵐ sample ∂historyLaw (markovHistoryPolicy (scheduledPolicy x hx)), ∀ n, (sample n).1=x n := by
  apply ae_all_iff.mpr
  intro n
  have hm (a : Bool) := actual_constructed_markov_path_joint_mass model (scheduledPolicy x hx) n (x n) a
  have hp := actual_finite_event_partition (historyLaw (markovHistoryPolicy (scheduledPolicy x hx)))
    (fun sample => (sample n).2) {sample | (sample n).1=x n}
    (fun a => by fun_prop)
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

end SafeLearning.CompleteMonitoringDeterministicPath23
