import SafeLearning.CompleteModulesClassificationNorm
import SafeLearning.CompleteModulesClassificationNumbers
import SafeLearning.CompleteModulesClassificationCertificate

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesSourceClassification
open CompleteModulesClassificationNorm CompleteModulesClassificationNumbers CompleteModulesClassificationCertificate
variable {I X : Type*} [Fintype I] [DecidableEq I] [PseudoMetricSpace X]

theorem actual_source_spectral_bound_certifies_every_class_pair
    (weight : Matrix (Fin 3) I ℝ) (hweight : ‖weight‖ ≤ 1)
    (other : Fin 3) (hother : other≠0) :
    actualClassPairGain weight 0 other ≤ Real.sqrt 2 := by
  have h := actual_class_row_difference_norm_is_bounded_by_sqrt_two_spectral_norm weight 0 other hother.symm
  exact h.trans (by nlinarith [Real.sqrt_nonneg (2:ℝ)])

theorem actual_source_global_radius_preserves_actual_prediction
    (weight : Matrix (Fin 3) I ℝ) (bias : Fin 3 → ℝ) (feature : X → I → ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ dist first second)
    (hweight : ‖weight‖ ≤ 1) (first second : X)
    (hlogits : actualClassLogits weight bias feature first=actualSourceLogits)
    (hradius : dist first second < actualGlobalRadius) :
    ∀ other : Fin 3,other≠0 →
      actualClassLogits weight bias feature second other < actualClassLogits weight bias feature second 0 := by
  apply actual_one_vs_rest_radius_preserves_unique_prediction weight bias feature hfeature 0
    (fun _ => Real.sqrt 2) first second
  · intro other hother
    exact Real.sqrt_pos.mpr (by norm_num)
  · intro other hother
    exact actual_source_spectral_bound_certifies_every_class_pair weight hweight other hother
  · intro other hother
    rw [hlogits]
    fin_cases other
    · exact False.elim (hother rfl)
    · rw [actual_source_logit_margins_and_global_radius.2.2] at hradius
      norm_num [actualSourceLogits]
      exact hradius
    · have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      apply lt_of_lt_of_le hradius
      rw [actual_source_logit_margins_and_global_radius.2.2]
      apply div_le_div_of_nonneg_right _ hp.le
      norm_num [actualSourceLogits]

theorem actual_source_pairwise_radius_preserves_actual_prediction
    (weight : Matrix (Fin 3) I ℝ) (bias : Fin 3 → ℝ) (feature : X → I → ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ dist first second)
    (hfirstGain : actualClassPairGain weight 0 1=(6/5:ℝ))
    (hsecondGain : actualClassPairGain weight 0 2=(27/20:ℝ))
    (first second : X) (hlogits : actualClassLogits weight bias feature first=actualSourceLogits)
    (hradius : dist first second < actualPairwiseRadius) :
    ∀ other : Fin 3,other≠0 →
      actualClassLogits weight bias feature second other < actualClassLogits weight bias feature second 0 := by
  apply actual_one_vs_rest_radius_preserves_unique_prediction weight bias feature hfeature 0
    (![1,6/5,27/20] : Fin 3 → ℝ) first second
  · intro other hother
    fin_cases other <;> norm_num
  · intro other hother
    fin_cases other
    · exact False.elim (hother rfl)
    · simp [hfirstGain]
    · simp [hsecondGain]
  · intro other hother
    rw [hlogits]
    fin_cases other
    · exact False.elim (hother rfl)
    · rw [actual_source_pairwise_radius_and_runnerup_ratio.1] at hradius
      norm_num [actualSourceLogits]
      exact hradius
    · apply lt_of_lt_of_le hradius
      norm_num [actualPairwiseRadius,actualSourceLogits]

end SafeLearning.CompleteModulesSourceClassification
