import SafeLearning.CompleteModulesGoSafeToyFeasibility

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToySmoothness
open SafeLearning.CompleteModulesGoSafeToyAffine SafeLearning.CompleteModulesGoSafeToyFeasibility

def actualParameterMargin (a : ℝ × ℝ) : ℝ :=
  1-actualEquilibrium (actualGain a.2) (actualReference a.1)

def actualSourceParameterBox : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1

theorem actual_reference_is_smooth_of_every_order : ContDiff ℝ ⊤ actualReference := by
  unfold actualReference
  fun_prop

theorem actual_equilibrium_margin_is_smooth_on_the_positive_denominator_domain :
    ContDiffOn ℝ ⊤ actualParameterMargin {a : ℝ × ℝ | -4/5 < a.2} := by
  have hn : ContDiff ℝ ⊤ (fun a : ℝ × ℝ => actualGain a.2*actualReference a.1+3/5) := by
    unfold actualGain actualReference
    fun_prop
  have hd : ContDiff ℝ ⊤ (fun a : ℝ × ℝ => 1+actualGain a.2) := by
    unfold actualGain
    fun_prop
  have hquot := hn.contDiffOn.div hd.contDiffOn (s := {a : ℝ × ℝ | -4/5 < a.2})
    (fun a ha => by simp only [mem_ofPred_eq,actualGain] at ha ⊢; linarith)
  unfold actualParameterMargin actualEquilibrium
  exact contDiffOn_const.sub hquot

theorem actual_source_trajectory_infimum_margin_is_the_same_smooth_parameter_function :
    (∀ a ∈ actualSourceParameterBox,
      actualSourceSafety (actualGain a.2) a.1=actualParameterMargin a) ∧
      ContDiffOn ℝ ⊤ (fun a : ℝ × ℝ => actualSourceSafety (actualGain a.2) a.1)
        actualSourceParameterBox := by
  have heq : ∀ a ∈ actualSourceParameterBox,
      actualSourceSafety (actualGain a.2) a.1=actualParameterMargin a := by
    intro a ha
    have hg := (actual_source_parameter_ranges a.1 a.2 ha.2).1
    exact actual_source_zero_start_safety_is_the_true_equilibrium_margin _ _ hg
  refine ⟨heq,?_⟩
  have hsub : actualSourceParameterBox ⊆ {a : ℝ × ℝ | -4/5 < a.2} := by
    intro a ha
    simp only [mem_ofPred_eq]
    have hh := ha.2.1
    linarith
  exact (actual_equilibrium_margin_is_smooth_on_the_positive_denominator_domain.mono hsub).congr
    (fun a ha => heq a ha)

end SafeLearning.CompleteModulesGoSafeToySmoothness
