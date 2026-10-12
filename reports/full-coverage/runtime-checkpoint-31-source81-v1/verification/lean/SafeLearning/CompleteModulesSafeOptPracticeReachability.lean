import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptPracticeReachability

def sourceValue (i : Fin 4) : ℝ := ![11/10,11/10,1/10,11/10] i
def sourceDistance (i j : Fin 4) : ℝ := |(i.val:ℝ)-(j.val:ℝ)|
def actualExpansion (old : Set (Fin 4)) : Set (Fin 4) :=
  {candidate | ∃ witness ∈ old, 0 ≤ sourceValue witness-sourceDistance witness candidate}
def actualRounds : ℕ → Set (Fin 4)
  | 0 => {0}
  | n+1 => actualExpansion (actualRounds n)

theorem actual_source_values_are_all_nonnegative_and_satisfy_the_genuine_lipschitz_bound :
    (∀ i, 0 ≤ sourceValue i) ∧
      ∀ i j, |sourceValue i-sourceValue j| ≤ sourceDistance i j := by
  constructor
  · intro i
    fin_cases i <;> norm_num [sourceValue]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [sourceValue,sourceDistance]

theorem actual_source_first_three_reachable_rounds :
    actualRounds 0=({0}:Set (Fin 4)) ∧ actualRounds 1=({0,1}:Set (Fin 4)) ∧
      actualRounds 2=({0,1,2}:Set (Fin 4)) := by
  refine ⟨rfl,?_,?_⟩
  · ext i
    fin_cases i <;> norm_num [actualRounds,actualExpansion,sourceValue,sourceDistance,Fin.exists_fin_succ]
  · ext i
    fin_cases i <;> norm_num [actualRounds,actualExpansion,sourceValue,sourceDistance,Fin.exists_fin_succ]

theorem actual_source_three_point_reachable_set_is_a_true_fixed_point :
    actualExpansion ({0,1,2}:Set (Fin 4))=({0,1,2}:Set (Fin 4)) := by
  ext i
  fin_cases i <;> norm_num [actualExpansion,sourceValue,sourceDistance,Fin.exists_fin_succ]

theorem actual_source_every_round_from_the_second_is_the_exact_fixed_point (n : ℕ) :
    actualRounds (n+2)=({0,1,2}:Set (Fin 4)) := by
  induction n with
  | zero => exact actual_source_first_three_reachable_rounds.2.2
  | succ n ih =>
    have hindex : n+1+2=(n+2)+1 := by omega
    rw [hindex,actualRounds,ih]
    exact actual_source_three_point_reachable_set_is_a_true_fixed_point

theorem actual_source_all_three_transfers_to_unreachable_point_three :
    sourceValue 0-sourceDistance 0 3=(-19/10:ℝ) ∧
      sourceValue 1-sourceDistance 1 3=(-9/10:ℝ) ∧
      sourceValue 2-sourceDistance 2 3=(-9/10:ℝ) := by norm_num [sourceValue,sourceDistance]

theorem actual_source_point_three_is_safe_but_never_reachable_in_any_round :
    0 ≤ sourceValue 3 ∧ ∀ n, 3 ∉ actualRounds n := by
  constructor
  · norm_num [sourceValue]
  · intro n
    rcases n with _ | n
    · simp [actualRounds]
    rcases n with _ | n
    · rw [actual_source_first_three_reachable_rounds.2.1]
      simp
    · rw [show n+1+1=n+2 by omega,actual_source_every_round_from_the_second_is_the_exact_fixed_point]
      simp

end SafeLearning.CompleteModulesSafeOptPracticeReachability
