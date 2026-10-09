import SafeLearning.CompleteModulesSourceClassification

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesNormalizedClassification
open CompleteModulesClassificationNorm CompleteModulesClassificationNumbers
open CompleteModulesClassificationCertificate CompleteModulesSourceClassification
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def actualEuclideanQuarterScaleNormalizer (center : I → ℝ) (input : EuclideanSpace ℝ I) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (actualQuarterScaleNormalizer center (WithLp.ofLp input))

theorem actual_euclidean_normalization_distance (center : I → ℝ) (first second : EuclideanSpace ℝ I) :
    dist (actualEuclideanQuarterScaleNormalizer center first) (actualEuclideanQuarterScaleNormalizer center second)=
      4*dist first second := by
  simp only [dist_eq_norm,actualEuclideanQuarterScaleNormalizer,← WithLp.toLp_sub]
  simpa using actual_quarter_scale_normalizer_distance center (WithLp.ofLp first) (WithLp.ofLp second)

theorem actual_normalized_classifier_preserves_prediction_within_global_pixel_radius
    (center : I → ℝ) (weight : Matrix (Fin 3) J ℝ) (bias : Fin 3 → ℝ)
    (feature : EuclideanSpace ℝ I → J → ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ dist first second)
    (hweight : ‖weight‖ ≤ 1) (first second : EuclideanSpace ℝ I)
    (hlogits : actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center first)=actualSourceLogits)
    (hradius : dist first second < actualGlobalRadius/4) :
    ∀ other : Fin 3,other≠0 →
      actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center second) other <
      actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center second) 0 := by
  apply actual_source_global_radius_preserves_actual_prediction weight bias feature hfeature hweight
    (actualEuclideanQuarterScaleNormalizer center first) (actualEuclideanQuarterScaleNormalizer center second) hlogits
  rw [actual_euclidean_normalization_distance]
  have h := (lt_div_iff₀ (show (0:ℝ) < 4 by norm_num)).mp hradius
  linarith

theorem actual_normalized_classifier_preserves_prediction_within_pairwise_pixel_radius
    (center : I → ℝ) (weight : Matrix (Fin 3) J ℝ) (bias : Fin 3 → ℝ)
    (feature : EuclideanSpace ℝ I → J → ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ dist first second)
    (hfirstGain : actualClassPairGain weight 0 1=(6/5:ℝ))
    (hsecondGain : actualClassPairGain weight 0 2=(27/20:ℝ))
    (first second : EuclideanSpace ℝ I)
    (hlogits : actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center first)=actualSourceLogits)
    (hradius : dist first second < actualPairwiseRadius/4) :
    ∀ other : Fin 3,other≠0 →
      actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center second) other <
      actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center second) 0 := by
  apply actual_source_pairwise_radius_preserves_actual_prediction weight bias feature hfeature hfirstGain hsecondGain
    (actualEuclideanQuarterScaleNormalizer center first) (actualEuclideanQuarterScaleNormalizer center second) hlogits
  rw [actual_euclidean_normalization_distance]
  have h := (lt_div_iff₀ (show (0:ℝ) < 4 by norm_num)).mp hradius
  linarith

theorem actual_normalized_global_certificate_covers_closed_smaller_pixel_ball
    (center : I → ℝ) (weight : Matrix (Fin 3) J ℝ) (bias : Fin 3 → ℝ)
    (feature : EuclideanSpace ℝ I → J → ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ dist first second)
    (hweight : ‖weight‖ ≤ 1) (first second : EuclideanSpace ℝ I)
    (hlogits : actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center first)=actualSourceLogits)
    (hperturbation : dist first second ≤ (36/255:ℝ)) :
    ∀ other : Fin 3,other≠0 →
      actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center second) other <
      actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center second) 0 := by
  apply actual_normalized_classifier_preserves_prediction_within_global_pixel_radius center weight bias feature hfeature hweight first second hlogits
  exact hperturbation.trans_lt actual_source_normalized_pixel_radii_certify_only_smaller_level.1

theorem actual_normalized_pairwise_certificate_covers_closed_smaller_pixel_ball
    (center : I → ℝ) (weight : Matrix (Fin 3) J ℝ) (bias : Fin 3 → ℝ)
    (feature : EuclideanSpace ℝ I → J → ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ dist first second)
    (hfirstGain : actualClassPairGain weight 0 1=(6/5:ℝ))
    (hsecondGain : actualClassPairGain weight 0 2=(27/20:ℝ))
    (first second : EuclideanSpace ℝ I)
    (hlogits : actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center first)=actualSourceLogits)
    (hperturbation : dist first second ≤ (36/255:ℝ)) :
    ∀ other : Fin 3,other≠0 →
      actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center second) other <
      actualClassLogits weight bias feature (actualEuclideanQuarterScaleNormalizer center second) 0 := by
  apply actual_normalized_classifier_preserves_prediction_within_pairwise_pixel_radius center weight bias feature hfeature hfirstGain hsecondGain first second hlogits
  exact hperturbation.trans_lt actual_source_normalized_pixel_radii_certify_only_smaller_level.2.2.1

end SafeLearning.CompleteModulesNormalizedClassification
