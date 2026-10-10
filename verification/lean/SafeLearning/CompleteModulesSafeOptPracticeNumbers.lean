import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptPracticeNumbers

theorem actual_negative_noisy_observation_is_a_safe_underlying_query_and_positive_observation_can_be_unsafe :
    (1/10:ℝ)+(-1/5)=(-1/10) ∧ 0 ≤ (1/10:ℝ) ∧
      (-1/10:ℝ)+(1/5)=1/10 ∧ (-1/10:ℝ)<0 ∧ 0<(1/10:ℝ) := by norm_num

theorem actual_noise_upper_allowance_turns_a_measurement_into_a_true_lower_bound
    (trueValue noise allowance : ℝ) (hn : noise ≤ allowance) :
    trueValue+noise-allowance ≤ trueValue := by linarith

theorem actual_source_lipschitz_price_radius_and_all_three_transferred_lower_bounds (distance : ℝ) :
    (3/5:ℝ)-2*distance ≥ 1/10 ↔ distance ≤ 1/4 := by constructor <;> intro h <;> linarith

theorem actual_source_lipschitz_price_numeric_tests :
    (3/5:ℝ)-2*(1/5)=1/5 ∧ (3/5:ℝ)-2*(1/4)=1/10 ∧
      (3/5:ℝ)-2*(3/10)=0 ∧ (1/10:ℝ)≤1/5 ∧ ¬(1/10:ℝ)≤0 := by norm_num

def candidateLower (i : Fin 3) : ℝ := ![2/5,3/5,1/5] i
def candidateUpper (i : Fin 3) : ℝ := ![4/5,7/10,1/2] i

theorem actual_source_best_lower_bound_and_unique_pessimistic_recommendation :
    IsGreatest (Set.range candidateLower) (3/5:ℝ) ∧
      ∀ i : Fin 3, candidateLower i=3/5 ↔ i=1 := by
  constructor
  · constructor
    · exact ⟨1,by norm_num [candidateLower]⟩
    · rintro value ⟨i,rfl⟩
      fin_cases i <;> norm_num [candidateLower]
  · intro i
    fin_cases i <;> norm_num [candidateLower]

theorem actual_source_potential_maximizers_are_exactly_a_and_b (i : Fin 3) :
    (3/5:ℝ) ≤ candidateUpper i ↔ i=0 ∨ i=1 := by fin_cases i <;> norm_num [candidateUpper]

def possibleTrueValue (i : Fin 3) : ℝ := ![4/5,3/5,1/5] i

theorem actual_source_a_might_be_better_in_truth_despite_the_recommendation_b :
    (∀ i, candidateLower i ≤ possibleTrueValue i ∧ possibleTrueValue i ≤ candidateUpper i) ∧
      possibleTrueValue 1 < possibleTrueValue 0 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [candidateLower,candidateUpper,possibleTrueValue]
  · norm_num [possibleTrueValue]

def sourceExpanderSet : Set (Fin 4) := {2}
def sourceMaximizerSet : Set (Fin 4) := {0,1}
def sourceWidth (i : Fin 4) : ℝ := ![1/5,1/2,2/5,2] i

theorem actual_source_eligible_union_and_largest_width_query :
    sourceExpanderSet ∪ sourceMaximizerSet=({0,1,2}:Set (Fin 4)) ∧
      IsGreatest (sourceWidth '' (sourceExpanderSet ∪ sourceMaximizerSet)) (1/2:ℝ) ∧
      3 ∉ sourceExpanderSet ∪ sourceMaximizerSet ∧ (1/2:ℝ)<sourceWidth 3 := by
  refine ⟨?_,?_,?_,?_⟩
  · ext i
    fin_cases i <;> simp [sourceExpanderSet,sourceMaximizerSet]
  · constructor
    · exact ⟨1,by simp [sourceExpanderSet,sourceMaximizerSet],by norm_num [sourceWidth]⟩
    · rintro value ⟨i,hi,rfl⟩
      fin_cases i <;> simp_all [sourceExpanderSet,sourceMaximizerSet,sourceWidth] <;> norm_num
  · simp [sourceExpanderSet,sourceMaximizerSet]
  · norm_num [sourceWidth]

theorem actual_source_width_query_is_uniquely_b (i : Fin 4)
    (hi : i ∈ sourceExpanderSet ∪ sourceMaximizerSet) : sourceWidth i=1/2 ↔ i=1 := by
  fin_cases i <;> simp_all [sourceExpanderSet,sourceMaximizerSet,sourceWidth] <;> norm_num

theorem actual_closed_interval_intersection_is_the_max_min_endpoint_interval
    (a b c d : ℝ) : Icc a b ∩ Icc c d = Icc (max a c) (min b d) := by
  ext x
  simp only [mem_inter_iff,mem_Icc,max_le_iff,le_min_iff]
  tauto

theorem actual_source_interval_intersections_and_width_and_empty_conflict :
    Icc (1/5:ℝ) (4/5) ∩ Icc (2/5:ℝ) 1=Icc (2/5:ℝ) (4/5) ∧
      (4/5:ℝ)-(2/5)=2/5 ∧
      Icc (1/5:ℝ) (4/5) ∩ Icc (9/10:ℝ) (11/10)=∅ := by
  rw [actual_closed_interval_intersection_is_the_max_min_endpoint_interval,
    actual_closed_interval_intersection_is_the_max_min_endpoint_interval]
  norm_num

theorem actual_intersection_preserves_any_common_true_value_and_monotone_endpoints
    (trueValue a b c d : ℝ) (hold : trueValue ∈ Icc a b) (hnew : trueValue ∈ Icc c d) :
    trueValue ∈ Icc (max a c) (min b d) ∧ a ≤ max a c ∧ min b d ≤ b := by
  refine ⟨?_,le_max_left _ _,min_le_left _ _⟩
  rw [← actual_closed_interval_intersection_is_the_max_min_endpoint_interval]
  exact ⟨hold,hnew⟩

theorem actual_empty_confidence_intersection_excludes_simultaneous_validity
    (trueValue a b c d : ℝ) (hempty : Icc a b ∩ Icc c d = (∅:Set ℝ)) :
    ¬(trueValue ∈ Icc a b ∧ trueValue ∈ Icc c d) := by
  intro h
  have hm : trueValue ∈ Icc a b ∩ Icc c d := h
  rw [hempty] at hm
  exact hm

def expanderLower (i : Fin 3) : ℝ := ![1,2/5,0] i
def expanderUpper (i : Fin 3) : ℝ := ![7/5,6/5,0] i
def expanderSafe : Set (Fin 3) := {0,1}
def expanderDistance (i j : Fin 3) : ℝ := |(i.val:ℝ)-(j.val:ℝ)|
def actualExpanders : Set (Fin 3) := {i | i ∈ expanderSafe ∧
  ∃ j, j ∉ expanderSafe ∧ 0 ≤ expanderUpper i-expanderDistance i j}

theorem actual_source_expander_test_is_exactly_the_witness_point_one : actualExpanders=({1}:Set (Fin 3)) := by
  ext i
  fin_cases i <;> norm_num [actualExpanders,expanderSafe,expanderUpper,expanderDistance,Fin.exists_fin_succ]

theorem actual_source_expander_problem_maximizers_widths_query_and_no_current_certificate_for_two :
    (∀ i ∈ expanderSafe, (1:ℝ) ≤ expanderUpper i) ∧
      expanderUpper 0-expanderLower 0=2/5 ∧ expanderUpper 1-expanderLower 1=4/5 ∧
      (∀ i ∈ expanderSafe, expanderUpper i-expanderLower i ≤ (4/5:ℝ)) ∧
      (∀ i ∈ expanderSafe, expanderLower i-expanderDistance i 2<0) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi
    fin_cases i
    all_goals norm_num [expanderSafe] at hi
    all_goals norm_num [expanderUpper]
  · norm_num [expanderUpper,expanderLower]
  · norm_num [expanderUpper,expanderLower]
  · intro i hi
    fin_cases i
    all_goals norm_num [expanderSafe] at hi
    all_goals norm_num [expanderUpper,expanderLower]
  · intro i hi
    fin_cases i
    all_goals norm_num [expanderSafe] at hi
    all_goals norm_num [expanderLower,expanderDistance]

theorem actual_source_expander_optimistic_transfers_and_true_best_lower_bound :
    expanderUpper 0-expanderDistance 0 2=(-3/5:ℝ) ∧
      expanderUpper 1-expanderDistance 1 2=(1/5:ℝ) ∧
      IsGreatest (expanderLower '' expanderSafe) (1:ℝ) := by
  refine ⟨by norm_num [expanderUpper,expanderDistance],
    by norm_num [expanderUpper,expanderDistance],?_⟩
  constructor
  · exact ⟨0,by simp [expanderSafe],by norm_num [expanderLower]⟩
  · rintro value ⟨i,hi,rfl⟩
    fin_cases i
    all_goals norm_num [expanderSafe] at hi
    all_goals norm_num [expanderLower]

theorem actual_source_expander_width_query_is_uniquely_one (i : Fin 3) (hi : i ∈ expanderSafe) :
    expanderUpper i-expanderLower i=4/5 ↔ i=1 := by
  fin_cases i
  all_goals norm_num [expanderSafe] at hi
  all_goals norm_num [expanderUpper,expanderLower]

def constraintLower (candidate : Fin 3) (constraint : Fin 2) : ℝ :=
  (![![1/5,-1/10],![0,3/10],![2/5,1/10]] : Fin 3 → Fin 2 → ℝ) candidate constraint

theorem actual_source_all_constraints_certify_exactly_b_and_c (candidate : Fin 3) :
    (∀ constraint, 0 ≤ constraintLower candidate constraint) ↔ candidate=1 ∨ candidate=2 := by
  fin_cases candidate <;> norm_num [constraintLower,Fin.forall_fin_succ]

theorem actual_source_negative_lower_bound_need_not_mean_negative_true_constraint :
    constraintLower 0 1<0 ∧ constraintLower 0 1 ≤ (1/5:ℝ) ∧ 0 ≤ (1/5:ℝ) := by
  norm_num [constraintLower]

end SafeLearning.CompleteModulesSafeOptPracticeNumbers
