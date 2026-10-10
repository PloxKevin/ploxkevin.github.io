import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptEightPointReachability

def actualValue (i : Fin 8) : ℝ := ![1/2,6/5,2,7/5,2/5,1/5,11/10,21/10] i
def actualDistance (i j : Fin 8) : ℝ := |(i.val:ℝ)-(j.val:ℝ)|
def actualReach (epsilon : ℝ) (old : Set (Fin 8)) : Set (Fin 8) :=
  old ∪ {candidate | ∃ anchor ∈ old, 0 ≤ actualValue anchor-epsilon-actualDistance anchor candidate}
def actualIterates (epsilon : ℝ) : ℕ → Set (Fin 8)
  | 0 => {2}
  | n+1 => actualReach epsilon (actualIterates epsilon n)
def actualFinal : Set (Fin 8) := {0,1,2,3,4}

theorem actual_source_eight_values_are_all_safe_and_genuinely_one_lipschitz_on_every_pair :
    (∀ i : Fin 8, 0 ≤ actualValue i) ∧
      ∀ i j : Fin 8, |actualValue i-actualValue j| ≤ actualDistance i j := by
  constructor
  · intro i
    fin_cases i <;> norm_num [actualValue]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [actualValue,actualDistance]

theorem actual_source_slack_point_two_first_second_expansions_and_true_fixed_point :
    actualReach (1/5) ({2}:Set (Fin 8))=({1,2,3}:Set (Fin 8)) ∧
      actualReach (1/5) ({1,2,3}:Set (Fin 8))=actualFinal ∧
      actualReach (1/5) actualFinal=actualFinal := by
  constructor
  · ext i
    fin_cases i <;> norm_num [actualReach,actualValue,actualDistance,Fin.exists_fin_succ]
  constructor
  · ext i
    fin_cases i <;> norm_num [actualReach,actualValue,actualDistance,actualFinal,Fin.exists_fin_succ]
  · ext i
    fin_cases i <;> norm_num [actualReach,actualValue,actualDistance,actualFinal,Fin.exists_fin_succ]

theorem actual_source_zero_slack_reaches_the_same_true_fixed_point :
    actualReach 0 ({2}:Set (Fin 8))=actualFinal ∧
      actualReach 0 actualFinal=actualFinal := by
  constructor
  · ext i
    fin_cases i <;> norm_num [actualReach,actualValue,actualDistance,actualFinal,Fin.exists_fin_succ]
  · ext i
    fin_cases i <;> norm_num [actualReach,actualValue,actualDistance,actualFinal,Fin.exists_fin_succ]

theorem actual_source_every_later_slack_round_is_exactly_the_five_point_set :
    ∀ n, actualIterates (1/5) (n+2)=actualFinal := by
  intro n
  induction n with
  | zero =>
    change actualReach (1/5) (actualReach (1/5) {2})=actualFinal
    rw [actual_source_slack_point_two_first_second_expansions_and_true_fixed_point.1]
    exact actual_source_slack_point_two_first_second_expansions_and_true_fixed_point.2.1
  | succ n ih =>
    change actualReach (1/5) (actualIterates (1/5) (n+2))=actualFinal
    rw [ih]
    exact actual_source_slack_point_two_first_second_expansions_and_true_fixed_point.2.2

theorem actual_source_every_later_zero_slack_round_is_exactly_the_five_point_set :
    ∀ n, actualIterates 0 (n+1)=actualFinal := by
  intro n
  induction n with
  | zero => exact actual_source_zero_slack_reaches_the_same_true_fixed_point.1
  | succ n ih =>
    change actualReach 0 (actualIterates 0 (n+1))=actualFinal
    rw [ih]
    exact actual_source_zero_slack_reaches_the_same_true_fixed_point.2

theorem actual_source_both_reachable_closures_are_the_actual_five_point_set :
    (⋃ n, actualIterates (1/5) n)=actualFinal ∧ (⋃ n, actualIterates 0 n)=actualFinal := by
  constructor
  · ext i
    constructor
    · intro hi
      obtain ⟨n,hn⟩ := mem_iUnion.mp hi
      rcases n with _|n
      · have he : i=2 := hn
        rw [he]
        simp [actualFinal]
      rcases n with _|n
      · change i ∈ actualReach (1/5) {2} at hn
        rw [actual_source_slack_point_two_first_second_expansions_and_true_fixed_point.1] at hn
        fin_cases i
        all_goals norm_num at hn
        all_goals norm_num [actualFinal]
      · rwa [actual_source_every_later_slack_round_is_exactly_the_five_point_set] at hn
    · intro hi
      exact mem_iUnion.mpr ⟨2,by simpa only [actual_source_every_later_slack_round_is_exactly_the_five_point_set 0] using hi⟩
  · ext i
    constructor
    · intro hi
      obtain ⟨n,hn⟩ := mem_iUnion.mp hi
      rcases n with _|n
      · have he : i=2 := hn
        rw [he]
        simp [actualFinal]
      · rwa [actual_source_every_later_zero_slack_round_is_exactly_the_five_point_set] at hn
    · intro hi
      exact mem_iUnion.mpr ⟨1,by simpa only [actual_source_every_later_zero_slack_round_is_exactly_the_five_point_set 0] using hi⟩

theorem actual_source_reachable_maximum_is_uniquely_two_and_global_maximum_is_uniquely_seven :
    IsGreatest (actualValue '' actualFinal) (2:ℝ) ∧
      (∀ i ∈ actualFinal, actualValue i=2 ↔ i=2) ∧
      IsGreatest (Set.range actualValue) (21/10:ℝ) ∧
      (∀ i : Fin 8, actualValue i=21/10 ↔ i=7) ∧
      (7:Fin 8) ∉ actualFinal ∧ actualValue 5=(1/5:ℝ) := by
  refine ⟨?_,?_,?_,?_,by simp [actualFinal],by norm_num [actualValue]⟩
  · constructor
    · exact ⟨2,by simp [actualFinal],by norm_num [actualValue]⟩
    · rintro v ⟨i,hi,rfl⟩
      fin_cases i
      all_goals norm_num [actualFinal] at hi
      all_goals norm_num [actualValue]
  · intro i hi
    fin_cases i
    all_goals norm_num [actualFinal] at hi
    all_goals norm_num [actualValue]
  · constructor
    · exact ⟨7,by norm_num [actualValue]⟩
    · rintro v ⟨i,rfl⟩
      fin_cases i <;> norm_num [actualValue]
  · intro i
    fin_cases i <;> norm_num [actualValue]

end SafeLearning.CompleteModulesSafeOptEightPointReachability
