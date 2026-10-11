import SafeLearning.CompleteModulesNormalizedClassification

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesClassificationLevels
open CompleteModulesClassificationNumbers CompleteModulesClassificationCertificate
open CompleteModulesSourceClassification CompleteModulesNormalizedClassification
variable {I X : Type*} [Fintype I] [DecidableEq I] [PseudoMetricSpace X]

theorem actual_unnormalized_global_certificate_covers_both_closed_perturbation_levels
    (weight : Matrix (Fin 3) I ℝ) (bias : Fin 3 → ℝ) (feature : X → I → ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ dist first second)
    (hweight : ‖weight‖ ≤ 1) (first second : X)
    (hlogits : actualClassLogits weight bias feature first=actualSourceLogits)
    (epsilon : ℝ) (hlevel : epsilon=(36/255:ℝ) ∨ epsilon=(72/255:ℝ))
    (hperturbation : dist first second ≤ epsilon) :
    ∀ other : Fin 3,other≠0 →
      actualClassLogits weight bias feature second other < actualClassLogits weight bias feature second 0 := by
  apply actual_source_global_radius_preserves_actual_prediction weight bias feature hfeature hweight first second hlogits
  apply hperturbation.trans_lt
  rcases hlevel with hlevel|hlevel
  · rw [hlevel]
    exact actual_source_both_unnormalized_radii_exceed_both_perturbation_levels.1
  · rw [hlevel]
    exact actual_source_both_unnormalized_radii_exceed_both_perturbation_levels.2.1

theorem actual_unnormalized_pairwise_certificate_covers_both_closed_perturbation_levels
    (weight : Matrix (Fin 3) I ℝ) (bias : Fin 3 → ℝ) (feature : X → I → ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ dist first second)
    (hfirstGain : actualClassPairGain weight 0 1=(6/5:ℝ))
    (hsecondGain : actualClassPairGain weight 0 2=(27/20:ℝ))
    (first second : X) (hlogits : actualClassLogits weight bias feature first=actualSourceLogits)
    (epsilon : ℝ) (hlevel : epsilon=(36/255:ℝ) ∨ epsilon=(72/255:ℝ))
    (hperturbation : dist first second ≤ epsilon) :
    ∀ other : Fin 3,other≠0 →
      actualClassLogits weight bias feature second other < actualClassLogits weight bias feature second 0 := by
  apply actual_source_pairwise_radius_preserves_actual_prediction weight bias feature hfeature hfirstGain hsecondGain first second hlogits
  apply hperturbation.trans_lt
  rcases hlevel with hlevel|hlevel
  · rw [hlevel]
    exact actual_source_both_unnormalized_radii_exceed_both_perturbation_levels.2.2.1
  · rw [hlevel]
    exact actual_source_both_unnormalized_radii_exceed_both_perturbation_levels.2.2.2

theorem actual_larger_pixel_level_is_outside_both_normalized_strict_radius_criteria :
    ¬ ((72/255:ℝ) < actualGlobalRadius/4) ∧
    ¬ ((72/255:ℝ) < actualPairwiseRadius/4) := by
  constructor
  · exact not_lt.mpr actual_source_normalized_pixel_radii_certify_only_smaller_level.2.1.le
  · exact not_lt.mpr actual_source_normalized_pixel_radii_certify_only_smaller_level.2.2.2.le

end SafeLearning.CompleteModulesClassificationLevels
