import SafeLearning.CompleteModulesGoSafeToyObjective

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyObjectiveConsequences
open SafeLearning.CompleteModulesGoSafeToyAffine SafeLearning.CompleteModulesGoSafeToyFeasibility
open SafeLearning.CompleteModulesGoSafeToyIslands SafeLearning.CompleteModulesGoSafeToyObjective

theorem actual_source_objective_is_smooth_at_every_order : ContDiff ℝ ⊤ actualObjective := by
  unfold actualObjective
  fun_prop

theorem actual_source_continuous_global_box_maximum_is_attained_strictly_in_the_actual_second_safe_island :
    ∃ p ∈ actualParameterBox,
      IsGreatest (actualObjective '' actualParameterBox) (actualObjective p) ∧
      p.1 ∈ Ioo (1/2+actualBoundary (actualGain p.2)) (1-actualBoundary (actualGain p.2)) ∧
      0 ≤ actualSourceSafety (actualGain p.2) p.1 := by
  obtain ⟨p,hp,hm⟩ := actual_source_objective_has_a_genuine_global_box_maximum_and_every_maximizer_is_in_the_second_island_core.1
  have hs : actualObjective (3/4,3/5) ≤ actualObjective p :=
    hm.2 ⟨(3/4,3/5),by norm_num [actualParameterBox],rfl⟩
  have hi := actual_source_every_high_objective_box_point_belongs_to_the_actual_second_safe_island p hp
    (actual_source_second_island_center_objective_is_at_least_one_point_zero_six.trans hs)
  exact ⟨p,hp,hm,hi.1,hi.2⟩

theorem actual_source_no_continuous_global_maximizer_belongs_to_the_first_safe_island
    (p : ℝ × ℝ) (hp : p ∈ actualParameterBox)
    (hm : IsGreatest (actualObjective '' actualParameterBox) (actualObjective p)) :
    p.1 ∉ Icc (actualBoundary (actualGain p.2)) (1/2-actualBoundary (actualGain p.2)) := by
  have hx := actual_source_objective_has_a_genuine_global_box_maximum_and_every_maximizer_is_in_the_second_island_core.2 p hp hm
  have hy := hp.2
  have hg : actualGain p.2 ∈ Icc (3:ℝ) 8 := by
    constructor <;> unfold actualGain <;> linarith [hy.1,hy.2]
  have hb := actual_boundary_lies_strictly_between_one_twelfth_and_one_eighth _ hg
  intro h
  linarith [hx.1,h.2,hb.1]

end SafeLearning.CompleteModulesGoSafeToyObjectiveConsequences
