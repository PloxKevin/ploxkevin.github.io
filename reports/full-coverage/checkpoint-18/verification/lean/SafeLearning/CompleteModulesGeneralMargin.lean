import SafeLearning.CompleteModulesClassificationNorm
import SafeLearning.CompleteModulesClassificationCertificate

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesGeneralMargin
open CompleteModulesLipSDP CompleteModulesClassificationNorm CompleteModulesClassificationCertificate
variable {O I X : Type*} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] [PseudoMetricSpace X]

theorem actual_coordinate_gap_has_sqrt_two_norm_bound (vector : O → ℝ)
    (winner other : O) (hdistinct : winner≠other) :
    |vector winner-vector other| ≤ Real.sqrt 2*‖WithLp.toLp 2 vector‖ := by
  have h := abs_real_inner_le_norm
    (WithLp.toLp 2 ((Pi.single winner (1:ℝ) : O → ℝ)-Pi.single other 1))
    (WithLp.toLp 2 vector)
  rw [actual_distinct_class_basis_difference_has_norm_sqrt_two winner other hdistinct] at h
  simpa [PiLp.inner_apply,RCLike.inner_apply,mul_sub,Finset.sum_sub_distrib,Pi.single_apply] using h

theorem actual_arbitrary_logit_global_gain_certifies_gap_gain
    (logits : X → O → ℝ) (L : ℝ)
    (hlogits : ∀ first second,‖WithLp.toLp 2 (logits first-logits second)‖ ≤ L*dist first second)
    (winner other : O) (hdistinct : winner≠other) (first second : X) :
    |(logits first winner-logits first other)-(logits second winner-logits second other)| ≤
      (Real.sqrt 2*L)*dist first second := by
  have h := actual_coordinate_gap_has_sqrt_two_norm_bound (logits first-logits second) winner other hdistinct
  have hm := mul_le_mul_of_nonneg_left (hlogits first second) (Real.sqrt_nonneg (2:ℝ))
  have he : (logits first-logits second) winner-(logits first-logits second) other=
      (logits first winner-logits first other)-(logits second winner-logits second other) := by
    simp only [Pi.sub_apply]
    ring
  rw [he] at h
  exact h.trans (by simpa [mul_assoc] using hm)

theorem actual_arbitrary_gap_radius_preserves_class_pair_order
    (logits : X → O → ℝ) (winner other : O) (first second : X) (gain : ℝ)
    (hgain : 0 < gain)
    (hbound : |(logits first winner-logits first other)-(logits second winner-logits second other)| ≤ gain*dist first second)
    (hradius : dist first second < (logits first winner-logits first other)/gain) :
    logits second other < logits second winner := by
  have hs := (lt_div_iff₀ hgain).mp hradius
  have hb := (abs_le.mp hbound).2
  linarith

def actualOneVsRestRadius (logits : X → O → ℝ) (winner : O) (first : X)
    (gain : O → ℝ) (competitors : Finset O) (hcompetitors : competitors.Nonempty) : ℝ :=
  (competitors.image (fun other => (logits first winner-logits first other)/gain other)).min'
    (hcompetitors.image _)

theorem actual_arbitrary_one_vs_rest_minimum_radius_preserves_unique_prediction
    (logits : X → O → ℝ) (winner : O) (gain : O → ℝ) (first second : X)
    (hcompetitors : (Finset.univ.erase winner).Nonempty)
    (hgain : ∀ other,other≠winner → 0 < gain other)
    (hbound : ∀ other,other≠winner →
      |(logits first winner-logits first other)-(logits second winner-logits second other)| ≤
        gain other*dist first second)
    (hradius : dist first second < actualOneVsRestRadius logits winner first gain
      (Finset.univ.erase winner) hcompetitors) :
    ∀ other,other≠winner → logits second other < logits second winner := by
  intro other hother
  apply actual_arbitrary_gap_radius_preserves_class_pair_order logits winner other first second
    (gain other) (hgain other hother) (hbound other hother)
  apply hradius.trans_le
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨other,by simp [hother],rfl⟩)

def actualLogitMargin (logits : X → O → ℝ) (winner : O) (first : X)
    (competitors : Finset O) (hcompetitors : competitors.Nonempty) : ℝ :=
  logits first winner-(competitors.image (logits first)).max' (hcompetitors.image _)

theorem actual_arbitrary_global_margin_radius_preserves_unique_prediction
    (logits : X → O → ℝ) (winner : O) (first second : X) (L : ℝ) (hL : 0 < L)
    (hcompetitors : (Finset.univ.erase winner).Nonempty)
    (hlogits : ∀ first second,‖WithLp.toLp 2 (logits first-logits second)‖ ≤ L*dist first second)
    (hradius : dist first second < actualLogitMargin logits winner first
      (Finset.univ.erase winner) hcompetitors/(Real.sqrt 2*L)) :
    ∀ other,other≠winner → logits second other < logits second winner := by
  intro other hother
  have hg : 0 < Real.sqrt 2*L := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hL
  apply actual_arbitrary_gap_radius_preserves_class_pair_order logits winner other first second
    (Real.sqrt 2*L) hg
    (actual_arbitrary_logit_global_gain_certifies_gap_gain logits L hlogits winner other hother.symm first second)
  apply hradius.trans_le
  apply div_le_div_of_nonneg_right _ hg.le
  apply sub_le_sub_left
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨other,by simp [hother],rfl⟩)

theorem actual_affine_logit_pair_gain_with_arbitrary_feature_constant
    (weight : Matrix O I ℝ) (bias : O → ℝ) (feature : X → I → ℝ) (Lsub : ℝ)
    (hfeature : ∀ first second,‖WithLp.toLp 2 (feature first-feature second)‖ ≤ Lsub*dist first second)
    (winner other : O) (first second : X) :
    |(actualClassLogits weight bias feature first winner-actualClassLogits weight bias feature first other)-
      (actualClassLogits weight bias feature second winner-actualClassLogits weight bias feature second other)| ≤
      (Lsub*actualClassPairGain weight winner other)*dist first second := by
  have h := actual_class_pair_gap_has_euclidean_increment_bound weight bias feature winner other first second
  have hm := mul_le_mul_of_nonneg_left (hfeature first second)
    (show 0 ≤ actualClassPairGain weight winner other from norm_nonneg _)
  exact h.trans (by simpa [mul_comm,mul_left_comm,mul_assoc] using hm)

theorem actual_zero_gap_gain_preserves_class_pair_everywhere
    (logits : X → O → ℝ) (winner other : O) (first second : X)
    (hbound : |(logits first winner-logits first other)-(logits second winner-logits second other)| ≤ 0)
    (hmargin : logits first other < logits first winner) :
    logits second other < logits second winner := by
  have hz := abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  linarith

end SafeLearning.CompleteModulesGeneralMargin
