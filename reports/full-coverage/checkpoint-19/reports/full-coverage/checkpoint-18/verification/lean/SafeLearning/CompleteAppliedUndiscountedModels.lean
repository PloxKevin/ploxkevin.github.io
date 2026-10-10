import SafeLearning.CompleteFoundationsDiscountHorizons

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedUndiscountedModels
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Function
open SafeLearning.CompleteFoundationsDiscountHorizons

def actualTerminatingLaw : Measure ℕ := horizonLaw (1/2) (by norm_num) (by norm_num)

instance : IsProbabilityMeasure actualTerminatingLaw :=
  actual_horizon_probability_measure (1/2) (by norm_num) (by norm_num)

def actualTerminatingReward (lastVisit time : ℕ) : ℝ := if time ≤ lastVisit then 1 else 0

def actualTerminatingReturn (lastVisit : ℕ) : ℝ := ∑' time,actualTerminatingReward lastVisit time

theorem actual_undiscounted_terminating_path_return_is_its_finite_number_of_visits
    (lastVisit : ℕ) : actualTerminatingReturn lastVisit=(lastVisit:ℝ)+1 := by
  rw [actualTerminatingReturn,tsum_eq_sum (s := Finset.range (lastVisit+1))]
  · calc
      _ = ∑ _time ∈ Finset.range (lastVisit+1),(1:ℝ) := by
        apply Finset.sum_congr rfl
        intro time htime
        have ht : time ≤ lastVisit := by have := Finset.mem_range.mp htime; omega
        simp [actualTerminatingReward,ht]
      _ = _ := by simp
  · intro time htime
    have ht : ¬time ≤ lastVisit := by
      have hnot : ¬time < lastVisit+1 := by simpa only [Finset.mem_range] using htime
      omega
    simp [actualTerminatingReward,ht]

theorem actual_terminating_model_has_integrable_return_and_expected_value_two :
    Integrable actualTerminatingReturn actualTerminatingLaw ∧
      (∫ lastVisit,actualTerminatingReturn lastVisit ∂actualTerminatingLaw)=2 := by
  have h := actual_horizon_integrable_and_mean (1/2) (by norm_num) (by norm_num)
  have he : actualTerminatingReturn=(fun lastVisit : ℕ => (lastVisit:ℝ)+1) :=
    funext actual_undiscounted_terminating_path_return_is_its_finite_number_of_visits
  have hi : Integrable (fun lastVisit : ℕ => (lastVisit:ℝ)) actualTerminatingLaw := h.1
  constructor
  · rw [he]
    exact hi.add (integrable_const _)
  · rw [he,integral_add hi (integrable_const _),integral_const]
    simp only [probReal_univ,one_smul]
    change (∫ lastVisit : ℕ,(lastVisit:ℝ) ∂horizonLaw (1/2) (by norm_num) (by norm_num))+1=2
    rw [h.2]
    norm_num

theorem actual_survival_probability_at_each_visit (time : ℕ) :
    actualTerminatingLaw.real (Ici time)=(1/2:ℝ)^time := by
  have he : Ici time = ⋃ n : ℕ,{n+time} := by
    ext lastVisit
    simp only [mem_Ici,mem_iUnion,mem_singleton_iff]
    constructor
    · intro h
      exact ⟨lastVisit-time,by omega⟩
    · rintro ⟨n,rfl⟩
      omega
  have hd : Pairwise (Disjoint on (fun n : ℕ => ({n+time}:Set ℕ))) := by
    intro n m hnm
    simp only [disjoint_singleton_left,mem_singleton_iff]
    omega
  rw [measureReal_def,he,measure_iUnion hd (fun _ => measurableSet_singleton _),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top actualTerminatingLaw _)]
  change (∑' n : ℕ,actualTerminatingLaw.real {n+time})=(1/2:ℝ)^time
  have hsum := ((hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)<1)).mul_left ((1/2:ℝ)^time*(1/2))).tsum_eq
  have heterm : (fun n : ℕ => actualTerminatingLaw.real {n+time})=
      (fun n : ℕ => ((1/2:ℝ)^time*(1/2))*(1/2)^n) := by
    funext n
    rw [actualTerminatingLaw,actual_horizon_atoms,pow_add]
    ring
  rw [heterm,hsum]
  ring

theorem actual_conditional_termination_and_survival_per_visit_are_half (time : ℕ) :
    actualTerminatingLaw.real {time}/actualTerminatingLaw.real (Ici time)=1/2 ∧
      actualTerminatingLaw.real (Ici (time+1))/actualTerminatingLaw.real (Ici time)=1/2 := by
  rw [actual_survival_probability_at_each_visit,actual_survival_probability_at_each_visit,
    actualTerminatingLaw,actual_horizon_atoms]
  have hp : (1/2:ℝ)^time ≠ 0 := pow_ne_zero _ (by norm_num)
  constructor <;> field_simp <;> ring

def actualEternalBackup (value : ℝ) : ℝ := 1+value
def actualTerminatingBackup (value : ℝ) : ℝ := 1+(1/2)*value+(1/2)*0

def actualEternalPathReturn : ℝ≥0∞ := ∑' _time : ℕ,(1:ℝ≥0∞)

theorem actual_eternal_model_has_infinite_path_return_and_infinite_expectation
    {Omega : Type*} [MeasurableSpace Omega] (law : Measure Omega) [IsProbabilityMeasure law] :
    actualEternalPathReturn=∞ ∧ (∫⁻ _outcome,actualEternalPathReturn ∂law)=∞ := by
  have he : actualEternalPathReturn=∞ := ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)
  exact ⟨he,by rw [he,lintegral_const,measure_univ,mul_one]⟩

theorem actual_eternal_bellman_equation_has_no_finite_solution (value : ℝ) :
    actualEternalBackup value ≠ value := by unfold actualEternalBackup; linarith

theorem actual_eternal_value_iteration_is_the_number_of_steps_and_diverges :
    (∀ steps : ℕ,actualEternalBackup^[steps] 0=(steps:ℝ)) ∧
      Tendsto (fun steps : ℕ => actualEternalBackup^[steps] 0) atTop atTop := by
  have hformula : ∀ steps : ℕ,actualEternalBackup^[steps] 0=(steps:ℝ) := by
    intro steps
    induction steps with
    | zero => simp
    | succ steps ih => rw [Function.iterate_succ_apply',ih]; simp [actualEternalBackup]; ring
  exact ⟨hformula,by simpa only [hformula] using tendsto_natCast_atTop_atTop⟩

theorem actual_terminating_bellman_equation_has_unique_value_two (value : ℝ) :
    actualTerminatingBackup value=value ↔ value=2 := by unfold actualTerminatingBackup; constructor <;> intro h <;> linarith

theorem actual_terminating_backup_is_a_half_contraction (first second : ℝ) :
    |actualTerminatingBackup first-actualTerminatingBackup second|=(1/2)*|first-second| := by
  have he : actualTerminatingBackup first-actualTerminatingBackup second=(1/2)*(first-second) := by
    unfold actualTerminatingBackup
    ring
  rw [he,abs_mul]
  norm_num

theorem actual_terminating_value_iteration_converges_to_its_true_expected_return :
    (∀ steps : ℕ,actualTerminatingBackup^[steps] 0=2-2*(1/2:ℝ)^steps) ∧
      Tendsto (fun steps : ℕ => actualTerminatingBackup^[steps] 0) atTop (nhds 2) := by
  have hformula : ∀ steps : ℕ,actualTerminatingBackup^[steps] 0=2-2*(1/2:ℝ)^steps := by
    intro steps
    induction steps with
    | zero => simp
    | succ steps ih => rw [Function.iterate_succ_apply',ih,pow_succ]; unfold actualTerminatingBackup; ring
  constructor
  · exact hformula
  · simp only [hformula]
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hp) using 1
    norm_num

end SafeLearning.CompleteAppliedUndiscountedModels
