import SafeLearning.CompleteFiniteMarkovPathCorrespondence

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteModulesChowVisitCost21
open SafeLearning.CompleteFiniteCMDPOccupancy
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteFiniteMarkovPathCorrespondence

local instance : MeasurableSpace (Fin 4) := ⊤
local instance : MeasurableSingletonClass (Fin 4) := ⟨fun _ => MeasurableSet.of_discrete⟩

def transientKernel (p : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1/5 + 2/5*p, 4/5*(1-p); 0, 0, 1/2; 0, 1/10, 0]

def fullKernel (p : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1/5 + 2/5*p, 4/5*(1-p), 2/5*p;
     0, 0, 1/2, 1/2;
     0, 1/10, 0, 9/10;
     0, 0, 0, 1]

def soleAction : Policy (Fin 4) Unit where
  action _ _ _ := 1
  action_nonneg _ _ _ := by norm_num
  action_sum _ _ := by simp

def chainModel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (start : Fin 3) :
    Model (Fin 4) Unit where
  initial s := if s=start.castSucc then 1 else 0
  initial_nonneg s := by split_ifs <;> norm_num
  initial_sum := by simp
  transition s _ t := fullKernel p s t
  transition_nonneg s _ t := by
    fin_cases s <;> fin_cases t <;>
      norm_num [fullKernel] <;> nlinarith
  transition_sum s _ := by
    fin_cases s <;> norm_num [fullKernel, Fin.sum_univ_succ] <;> ring

def pathLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (start : Fin 3) :
    Measure (ℕ → Fin 4 × Unit) :=
  controlledPathMeasure (chainModel p hp0 hp1 start) (markovHistoryPolicy soleAction)

instance pathLaw_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (start : Fin 3) :
    IsProbabilityMeasure (pathLaw p hp0 hp1 start) := by
  unfold pathLaw
  infer_instance

theorem actual_full_chain_restricts_to_the_literal_nonterminal_kernel
    (p : ℝ) (i j : Fin 3) :
    fullKernel p i.castSucc j.castSucc=transientKernel p i j := by
  fin_cases i <;> fin_cases j <;> norm_num [fullKernel,transientKernel]

theorem actual_terminal_state_cannot_return_to_a_nonterminal_state
    (p : ℝ) (j : Fin 3) : fullKernel p (Fin.last 3) j.castSucc=0 := by
  fin_cases j <;> norm_num [fullKernel, Fin.last]

theorem actual_nonterminal_state_mass_is_the_real_matrix_power
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (start : Fin 3) (n : ℕ) (j : Fin 3) :
    stateMass (chainModel p hp0 hp1 start) soleAction n j.castSucc =
      (transientKernel p ^ n) start j := by
  induction n generalizing j with
  | zero => simp [stateMass,chainModel,Matrix.one_apply,eq_comm]
  | succ n ih =>
    change (∑ s : Fin 4, ∑ _a : Unit,
      stateMass (chainModel p hp0 hp1 start) soleAction n s * 1 * fullKernel p s j.castSucc)=_
    simp only [Fintype.sum_unique, mul_one]
    rw [Fin.sum_univ_castSucc]
    rw [actual_terminal_state_cannot_return_to_a_nonterminal_state,mul_zero,add_zero]
    rw [pow_succ,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih]
    congr 1
    exact actual_full_chain_restricts_to_the_literal_nonterminal_kernel p i j

theorem actual_constructed_path_has_the_nonterminal_matrix_power_marginal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (start : Fin 3) (n : ℕ) (j : Fin 3) :
    (pathLaw p hp0 hp1 start).real {path | (path n).1=j.castSucc}=
      (transientKernel p ^ n) start j := by
  have he : {path : ℕ → Fin 4 × Unit | (path n).1=j.castSucc}=
      {path | path n=(j.castSucc,())} := by
    ext path
    simp [Prod.ext_iff]
  rw [he]
  have h := actual_constructed_markov_path_joint_mass
    (chainModel p hp0 hp1 start) soleAction n j.castSucc ()
  dsimp only [jointMass] at h
  have ha : soleAction.action n j.castSucc ()=1 := rfl
  rw [ha,mul_one,actual_nonterminal_state_mass_is_the_real_matrix_power] at h
  simpa only [pathLaw] using h

section CountableVisits
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : ℕ → Set Ω)

def extendedVisits (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℕ, (events n).indicator (fun _ => (1 : ℝ≥0∞)) ω

def realVisits (ω : Ω) : ℝ :=
  ∑' n : ℕ, (events n).indicator (fun _ => (1 : ℝ)) ω

theorem actual_undiscounted_expected_visits_are_the_sum_of_actual_event_probabilities
    (hm : ∀ n, MeasurableSet (events n)) :
    (∫⁻ ω, extendedVisits events ω ∂μ)=∑' n : ℕ, μ (events n) := by
  unfold extendedVisits
  rw [lintegral_tsum (fun n => ((measurable_const.indicator (hm n)).aemeasurable))]
  simp only [lintegral_indicator_const (hm _), one_mul]

theorem actual_summable_visit_probabilities_make_the_undiscounted_count_finite_and_integrable
    (hm : ∀ n, MeasurableSet (events n)) (value : ℝ)
    (hseries : HasSum (fun n : ℕ => μ.real (events n)) value) :
    (∀ᵐ ω ∂μ, extendedVisits events ω ≠ ∞) ∧
      Integrable (realVisits events) μ ∧ (∫ ω, realVisits events ω ∂μ)=value := by
  have hmeas : AEMeasurable (extendedVisits events) μ :=
    AEMeasurable.tsum (fun n => (measurable_const.indicator (hm n)).aemeasurable)
  have hnonneg (n : ℕ) : 0 ≤ μ.real (events n) := measureReal_nonneg
  have hv : 0 ≤ value := hseries.nonneg hnonneg
  have hcoeff : (∑' n : ℕ, μ (events n))=ENNReal.ofReal value := by
    rw [← hseries.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnonneg hseries.summable]
    congr 1
    funext n
    exact (ENNReal.ofReal_toReal (measure_ne_top μ (events n))).symm
  have hfinite : (∫⁻ ω, extendedVisits events ω ∂μ) ≠ ∞ := by
    rw [actual_undiscounted_expected_visits_are_the_sum_of_actual_event_probabilities μ events hm,hcoeff]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ ω ∂μ, extendedVisits events ω < ∞ := ae_lt_top' hmeas hfinite
  have heq : (fun ω => (extendedVisits events ω).toReal)=ᵐ[μ] realVisits events := by
    filter_upwards [hae] with ω hω
    unfold extendedVisits realVisits
    rw [ENNReal.tsum_toReal_eq (f:=fun n => (events n).indicator (fun _ => (1:ℝ≥0∞)) ω)
      (fun n => by by_cases hh : ω∈events n <;> simp [Set.indicator,hh])]
    apply tsum_congr
    intro n
    by_cases hh : ω∈events n <;> simp [Set.indicator,hh]
  refine ⟨hae.mono (fun _ h => h.ne),
    (integrable_toReal_of_lintegral_ne_top hmeas hfinite).congr heq,?_⟩
  rw [← integral_congr_ae heq,integral_toReal hmeas hae,
    actual_undiscounted_expected_visits_are_the_sum_of_actual_event_probabilities μ events hm,hcoeff,
    ENNReal.toReal_ofReal hv]
end CountableVisits

theorem actual_constructed_undiscounted_chain_visit_cost_is_the_true_matrix_series
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (start j : Fin 3) (value : ℝ)
    (hseries : HasSum (fun n : ℕ => (transientKernel p ^ n) start j) value) :
    (∀ᵐ path ∂pathLaw p hp0 hp1 start,
      extendedVisits (fun n => {path | (path n).1=j.castSucc}) path ≠ ∞) ∧
      Integrable (realVisits (fun n => {path | (path n).1=j.castSucc}))
        (pathLaw p hp0 hp1 start) ∧
      (∫ path, realVisits (fun n => {path | (path n).1=j.castSucc}) path
        ∂pathLaw p hp0 hp1 start)=value := by
  apply actual_summable_visit_probabilities_make_the_undiscounted_count_finite_and_integrable
  · intro n
    exact (measurableSet_singleton j.castSucc).preimage
      (measurable_fst.comp (measurable_pi_apply n))
  · simpa only [actual_constructed_path_has_the_nonterminal_matrix_power_marginal] using hseries

end SafeLearning.CompleteModulesChowVisitCost21
