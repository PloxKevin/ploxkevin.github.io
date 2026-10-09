import SafeLearning.CompleteModulesGeneralMargin

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesMarginCorollaries
open CompleteModulesGeneralMargin CompleteModulesClassificationCertificate
variable {O I X : Type*} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] [PseudoMetricSpace X]

theorem actual_uniform_pair_radius_equals_global_margin_radius
    (logits : X → O → ℝ) (winner : O) (first : X) (gain : ℝ) (hgain : 0 < gain)
    (competitors : Finset O) (hcompetitors : competitors.Nonempty) :
    actualOneVsRestRadius logits winner first (fun _ => gain) competitors hcompetitors=
      actualLogitMargin logits winner first competitors hcompetitors/gain := by
  unfold actualOneVsRestRadius actualLogitMargin
  apply le_antisymm
  · obtain ⟨other,hother,he⟩ := Finset.mem_image.mp
      (Finset.max'_mem (competitors.image (logits first)) (hcompetitors.image _))
    rw [← he]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨other,hother,rfl⟩)
  · apply Finset.le_min'
    intro ratio hratio
    obtain ⟨other,hother,he⟩ := Finset.mem_image.mp hratio
    rw [← he]
    apply div_le_div_of_nonneg_right _ hgain.le
    apply sub_le_sub_left
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨other,hother,rfl⟩)

theorem actual_nonnegative_gap_radius_preserves_class_pair_order
    (logits : X → O → ℝ) (winner other : O) (first second : X) (gain : ℝ)
    (hgain : 0 ≤ gain)
    (hbound : |(logits first winner-logits first other)-(logits second winner-logits second other)| ≤ gain*dist first second)
    (hradius : dist first second < (logits first winner-logits first other)/gain) :
    logits second other < logits second winner := by
  by_cases hz : gain=0
  · simp only [hz,div_zero] at hradius
    exact False.elim ((dist_nonneg (x := first) (y := second)).not_gt hradius)
  · exact actual_arbitrary_gap_radius_preserves_class_pair_order logits winner other first second gain
      (lt_of_le_of_ne hgain (Ne.symm hz)) hbound hradius

theorem actual_nonnegative_one_vs_rest_radius_preserves_unique_prediction
    (logits : X → O → ℝ) (winner : O) (gain : O → ℝ) (first second : X)
    (hcompetitors : (Finset.univ.erase winner).Nonempty)
    (hgain : ∀ other,other≠winner → 0 ≤ gain other)
    (hbound : ∀ other,other≠winner →
      |(logits first winner-logits first other)-(logits second winner-logits second other)| ≤
        gain other*dist first second)
    (hradius : dist first second < actualOneVsRestRadius logits winner first gain
      (Finset.univ.erase winner) hcompetitors) :
    ∀ other,other≠winner → logits second other < logits second winner := by
  intro other hother
  apply actual_nonnegative_gap_radius_preserves_class_pair_order logits winner other first second
    (gain other) (hgain other hother) (hbound other hother)
  apply hradius.trans_le
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨other,by simp [hother],rfl⟩)

theorem actual_nonnegative_global_margin_radius_preserves_unique_prediction
    (logits : X → O → ℝ) (winner : O) (first second : X) (L : ℝ) (hL : 0 ≤ L)
    (hcompetitors : (Finset.univ.erase winner).Nonempty)
    (hlogits : ∀ first second,‖WithLp.toLp 2 (logits first-logits second)‖ ≤ L*dist first second)
    (hradius : dist first second < actualLogitMargin logits winner first
      (Finset.univ.erase winner) hcompetitors/(Real.sqrt 2*L)) :
    ∀ other,other≠winner → logits second other < logits second winner := by
  by_cases hz : L=0
  · simp only [hz,mul_zero,div_zero] at hradius
    exact False.elim ((dist_nonneg (x := first) (y := second)).not_gt hradius)
  · exact actual_arbitrary_global_margin_radius_preserves_unique_prediction logits winner first second L
      (lt_of_le_of_ne hL (Ne.symm hz)) hcompetitors hlogits hradius

theorem actual_affine_feature_pair_minimum_radius_preserves_unique_prediction
    (weight : Matrix O I ℝ) (bias : O → ℝ) (feature : X → I → ℝ) (Lsub : ℝ)
    (hLsub : 0 ≤ Lsub)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ Lsub*dist first second)
    (winner : O) (first second : X) (hcompetitors : (Finset.univ.erase winner).Nonempty)
    (hradius : dist first second < actualOneVsRestRadius (actualClassLogits weight bias feature)
      winner first (fun other => Lsub*actualClassPairGain weight winner other)
        (Finset.univ.erase winner) hcompetitors) :
    ∀ other,other≠winner → actualClassLogits weight bias feature second other <
      actualClassLogits weight bias feature second winner := by
  apply actual_nonnegative_one_vs_rest_radius_preserves_unique_prediction
    (actualClassLogits weight bias feature) winner (fun other => Lsub*actualClassPairGain weight winner other)
    first second hcompetitors
  · intro other hother
    exact mul_nonneg hLsub (norm_nonneg _)
  · intro other hother
    exact actual_affine_logit_pair_gain_with_arbitrary_feature_constant weight bias feature Lsub hfeature
      winner other first second
  · exact hradius

theorem actual_zero_global_gain_preserves_actual_prediction_everywhere
    (logits : X → O → ℝ) (winner : O) (first second : X)
    (hlogits : ∀ first second,‖WithLp.toLp 2 (logits first-logits second)‖ ≤ 0)
    (hwinner : ∀ other,other≠winner → logits first other < logits first winner) :
    ∀ other,other≠winner → logits second other < logits second winner := by
  intro other hother
  apply actual_zero_gap_gain_preserves_class_pair_everywhere logits winner other first second _ (hwinner other hother)
  have h := actual_arbitrary_logit_global_gain_certifies_gap_gain logits 0
    (by simpa only [zero_mul] using hlogits) winner other hother.symm first second
  simpa only [mul_zero,zero_mul] using h

end SafeLearning.CompleteModulesMarginCorollaries
