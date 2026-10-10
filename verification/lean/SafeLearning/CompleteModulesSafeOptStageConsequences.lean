import SafeLearning.CompleteModulesSafeOptConfidenceIntersections

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptStageConsequences
open SafeLearning.CompleteModulesSafeOptConfidenceIntersections

theorem actual_printed_raw_bands_are_valid_for_every_truth_in_the_stated_interval
    (f : Fin 2 → ℝ) (ha : f 0 ∈ Icc (9/10:ℝ) 1)
    (hb : f 1 ∈ Icc (1/5:ℝ) (4/5)) :
    ∀ round point, sourceLower round point ≤ f point ∧ f point ≤ sourceUpper round point := by
  intro round point
  fin_cases round <;> fin_cases point
  all_goals norm_num [sourceLower,sourceUpper] at *
  all_goals constructor <;> linarith

def actualStageCandidates (round : Fin 3) : Set (Fin 2) :=
  actualExpanders univ (sourceUpper round) (fun _ _ => 0) 0 ∪
    actualMaximizers univ (sourceLower round) (sourceUpper round)
def actualStageWidth (round : Fin 3) (point : Fin 2) : ℝ :=
  sourceUpper round point-sourceLower round point

theorem actual_fixed_safe_stage_expanders_are_empty_and_candidates_reenter :
    (∀ round : Fin 3, actualExpanders univ (sourceUpper round) (fun _ _ => 0) 0=∅) ∧
      actualStageCandidates 1=({0}:Set (Fin 2)) ∧
      actualStageCandidates 2=univ ∧
      (1:Fin 2) ∉ actualStageCandidates 1 ∧ (1:Fin 2) ∈ actualStageCandidates 2 := by
  have he (round : Fin 3) : actualExpanders univ (sourceUpper round) (fun _ _ => 0) 0=∅ := by
    ext x
    simp [actualExpanders]
  refine ⟨he,?_,?_,?_,?_⟩
  · ext point
    fin_cases point <;> norm_num [actualStageCandidates,he,actualMaximizers,sourceLower,sourceUpper,Fin.forall_fin_succ]
  · ext point
    fin_cases point <;> norm_num [actualStageCandidates,he,actualMaximizers,sourceLower,sourceUpper,Fin.forall_fin_succ]
  · norm_num [actualStageCandidates,he,actualMaximizers,sourceLower,sourceUpper,Fin.forall_fin_succ]
  · norm_num [actualStageCandidates,he,actualMaximizers,sourceLower,sourceUpper,Fin.forall_fin_succ]

theorem actual_source_stage_queries_are_genuine_width_maximizers_and_break_the_square_sum :
    (0:Fin 2) ∈ actualStageCandidates 1 ∧
      (∀ x ∈ actualStageCandidates 1, actualStageWidth 1 x ≤ actualStageWidth 1 0) ∧
      (1:Fin 2) ∈ actualStageCandidates 2 ∧
      (∀ x ∈ actualStageCandidates 2, actualStageWidth 2 x ≤ actualStageWidth 2 1) ∧
      actualStageWidth 1 0=3/10 ∧ actualStageWidth 2 1=3/5 ∧
      actualStageWidth 1 0 < actualStageWidth 2 1 ∧
      (actualStageWidth 1 0)^2+(actualStageWidth 2 1)^2 < 2*(actualStageWidth 2 1)^2 := by
  have hold := actual_fixed_safe_stage_expanders_are_empty_and_candidates_reenter.2.1
  have hnew := actual_fixed_safe_stage_expanders_are_empty_and_candidates_reenter.2.2.1
  refine ⟨by rw [hold];simp,?_,by rw [hnew];simp,?_,by norm_num [actualStageWidth,sourceUpper,sourceLower],
    by norm_num [actualStageWidth,sourceUpper,sourceLower],by norm_num [actualStageWidth,sourceUpper,sourceLower],
    by norm_num [actualStageWidth,sourceUpper,sourceLower]⟩
  · intro x hx
    rw [hold] at hx
    have he : x=0 := hx
    rw [he]
  · intro x _
    fin_cases x <;> norm_num [actualStageWidth,sourceUpper,sourceLower]

end SafeLearning.CompleteModulesSafeOptStageConsequences
