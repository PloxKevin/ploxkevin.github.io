import SafeLearning.CompleteModulesLipSDPProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesClassificationCertificate
open CompleteModulesLipSDP
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def actualClassLogits {X : Type*} (weight : Matrix O I ℝ) (bias : O → ℝ)
    (feature : X → I → ℝ) (input : X) : O → ℝ := weight *ᵥ feature input+bias

def actualClassPairGain (weight : Matrix O I ℝ) (first second : O) : ℝ :=
  ‖WithLp.toLp 2 (fun coordinate => weight first coordinate-weight second coordinate)‖

theorem actual_class_pair_gap_increment_is_weighted_feature_increment
    {X : Type*} (weight : Matrix O I ℝ) (bias : O → ℝ) (feature : X → I → ℝ)
    (firstClass secondClass : O) (first second : X) :
    (actualClassLogits weight bias feature first firstClass-actualClassLogits weight bias feature first secondClass)-
      (actualClassLogits weight bias feature second firstClass-actualClassLogits weight bias feature second secondClass)=
    ∑ coordinate,(weight firstClass coordinate-weight secondClass coordinate)*
      (feature first coordinate-feature second coordinate) := by
  simp only [actualClassLogits,Pi.add_apply,Matrix.mulVec,dotProduct]
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib]
  ring

theorem actual_class_pair_gap_has_euclidean_increment_bound
    {X : Type*} (weight : Matrix O I ℝ) (bias : O → ℝ) (feature : X → I → ℝ)
    (firstClass secondClass : O) (first second : X) :
    |(actualClassLogits weight bias feature first firstClass-actualClassLogits weight bias feature first secondClass)-
      (actualClassLogits weight bias feature second firstClass-actualClassLogits weight bias feature second secondClass)| ≤
    actualClassPairGain weight firstClass secondClass*‖WithLp.toLp 2 (feature first-feature second)‖ := by
  rw [actual_class_pair_gap_increment_is_weighted_feature_increment]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun coordinate => weight firstClass coordinate-weight secondClass coordinate)
    (fun coordinate => feature first coordinate-feature second coordinate)
  rw [← squared_norm_of_coordinates,← squared_norm_of_coordinates] at h
  change _ ≤ (actualClassPairGain weight firstClass secondClass)^2*‖WithLp.toLp 2 (feature first-feature second)‖^2 at h
  have hp : 0 ≤ actualClassPairGain weight firstClass secondClass := norm_nonneg _
  have hq := norm_nonneg (WithLp.toLp 2 (feature first-feature second))
  have ha := abs_nonneg (∑ coordinate,(weight firstClass coordinate-weight secondClass coordinate)*
    (feature first coordinate-feature second coordinate))
  have hs := sq_abs (∑ coordinate,(weight firstClass coordinate-weight secondClass coordinate)*
    (feature first coordinate-feature second coordinate))
  nlinarith [mul_nonneg hp hq]

theorem actual_class_pair_margin_preserves_order_within_ratio_radius
    {X : Type*} [PseudoMetricSpace X] (weight : Matrix O I ℝ) (bias : O → ℝ) (feature : X → I → ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ dist first second)
    (firstClass secondClass : O) (first second : X) (pairGain : ℝ) (hgain : 0 < pairGain)
    (hbound : actualClassPairGain weight firstClass secondClass ≤ pairGain)
    (hradius : dist first second <
      (actualClassLogits weight bias feature first firstClass-actualClassLogits weight bias feature first secondClass)/pairGain) :
    actualClassLogits weight bias feature second secondClass < actualClassLogits weight bias feature second firstClass := by
  have h := actual_class_pair_gap_has_euclidean_increment_bound weight bias feature firstClass secondClass first second
  have hp : 0 ≤ actualClassPairGain weight firstClass secondClass := norm_nonneg _
  have hb := mul_le_mul_of_nonneg_left (hfeature first second) hp
  have hg := mul_le_mul_of_nonneg_right hbound (dist_nonneg (x := first) (y := second))
  have ht := (lt_div_iff₀ hgain).mp hradius
  have ha := (abs_le.mp h).2
  linarith

theorem actual_one_vs_rest_radius_preserves_unique_prediction
    {X : Type*} [PseudoMetricSpace X] (weight : Matrix O I ℝ) (bias : O → ℝ) (feature : X → I → ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ dist first second)
    (winner : O) (pairGain : O → ℝ) (first second : X)
    (hgain : ∀ other,other≠winner → 0 < pairGain other)
    (hbound : ∀ other,other≠winner → actualClassPairGain weight winner other ≤ pairGain other)
    (hradius : ∀ other,other≠winner → dist first second <
      (actualClassLogits weight bias feature first winner-actualClassLogits weight bias feature first other)/pairGain other) :
    ∀ other,other≠winner → actualClassLogits weight bias feature second other < actualClassLogits weight bias feature second winner := by
  intro other hother
  exact actual_class_pair_margin_preserves_order_within_ratio_radius weight bias feature hfeature winner other first second
    (pairGain other) (hgain other hother) (hbound other hother) (hradius other hother)

end SafeLearning.CompleteModulesClassificationCertificate
