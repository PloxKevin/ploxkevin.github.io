import Mathlib

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace SafeLearning.CompletePolicyConfidence

theorem selected_update_joint_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (rewardEvent costEvent : Set Ω)
    (hrmeas : MeasurableSet rewardEvent) (hcmeas : MeasurableSet costEvent)
    (hrprob : (98 / 100 : ℝ) ≤ μ.real rewardEvent)
    (hcprob : (97 / 100 : ℝ) ≤ μ.real costEvent) :
    (95 / 100 : ℝ) ≤ μ.real (rewardEvent ∩ costEvent) := by
  have hr := probReal_compl_eq_one_sub (μ := μ) hrmeas
  have hc := probReal_compl_eq_one_sub (μ := μ) hcmeas
  have hu := measureReal_union_le (μ := μ) rewardEventᶜ costEventᶜ
  have hb := probReal_compl_eq_one_sub (μ := μ) (hrmeas.compl.union hcmeas.compl)
  rw [compl_union, compl_compl, compl_compl] at hb
  linarith

theorem actual_reward_and_cost_margins (improvement cost : ℝ)
    (hr : |improvement - 2 / 5| ≤ 3 / 10) (hc : cost - 7 ≤ 1 / 2) :
    (1 / 10 : ℝ) ≤ improvement ∧ 0 < improvement ∧ cost ≤ 15 / 2 ∧ cost ≤ 8 := by
  have h := (abs_le.mp hr).1
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem true_selected_update_success_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (rewardEvent costEvent : Set Ω)
    (hrmeas : MeasurableSet rewardEvent) (hcmeas : MeasurableSet costEvent)
    (improvement cost : Ω → ℝ)
    (hr : ∀ ω ∈ rewardEvent, |improvement ω - 2 / 5| ≤ 3 / 10)
    (hc : ∀ ω ∈ costEvent, cost ω - 7 ≤ 1 / 2)
    (hrprob : (98 / 100 : ℝ) ≤ μ.real rewardEvent)
    (hcprob : (97 / 100 : ℝ) ≤ μ.real costEvent) :
    (95 / 100 : ℝ) ≤ μ.real {ω | (1 / 10 : ℝ) ≤ improvement ω ∧
      0 < improvement ω ∧ cost ω ≤ 15 / 2 ∧ cost ω ≤ 8} := by
  apply (selected_update_joint_confidence μ rewardEvent costEvent hrmeas hcmeas
    hrprob hcprob).trans
  refine measureReal_mono ?_ (by finiteness)
  intro ω hω
  exact actual_reward_and_cost_margins _ _ (hr ω hω.1) (hc ω hω.2)

end SafeLearning.CompletePolicyConfidence
