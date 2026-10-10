import SafeLearning.CompleteModulesGeneralNormalization
import SafeLearning.CompleteModulesGeneralMargin

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesDesignEasyPreprocessing
open CompleteModulesGeneralNormalization CompleteModulesGeneralMargin

def sourceScale : Fin 2 → ℝ := ![1/2,1/4]
def sourceRadius : ℝ := 1/(8*Real.sqrt 2)
def rawLogits {O : Type*} (center : Fin 2 → ℝ)
    (network : EuclideanSpace ℝ (Fin 2) → O → ℝ) (input : EuclideanSpace ℝ (Fin 2)) : O → ℝ :=
  network (actualPerChannelNormalizer center sourceScale input)

theorem actual_source_inverse_scales_and_gain :
    (∀ i, 0 < sourceScale i) ∧
      (fun i => 1/sourceScale i)=![(2:ℝ),4] ∧
      actualPerChannelNormalizationGain sourceScale=4 ∧
      ‖Matrix.diagonal (fun i => 1/sourceScale i)‖=4 := by
  have hp : ∀ i, 0 < sourceScale i := by intro i;fin_cases i <;>norm_num [sourceScale]
  have hg : actualPerChannelNormalizationGain sourceScale=4 := by
    norm_num [actualPerChannelNormalizationGain,sourceScale,Fin.univ_succ]
  refine ⟨hp,?_,hg,?_⟩
  · ext i;fin_cases i <;>norm_num [sourceScale]
  · rw [actual_per_channel_diagonal_spectral_norm_equals_maximum_inverse_scale _ hp,hg]

theorem actual_source_center_cancels_and_raw_gain_is_three_point_two
    {O : Type*} [Fintype O] (center : Fin 2 → ℝ)
    (network : EuclideanSpace ℝ (Fin 2) → O → ℝ)
    (hnetwork : ∀ a b, ‖WithLp.toLp 2 (network a-network b)‖≤(4/5:ℝ)*dist a b) :
    (∀ a b, actualPerChannelNormalizer center sourceScale a-
      actualPerChannelNormalizer center sourceScale b=
      WithLp.toLp 2 (Matrix.diagonal ![(2:ℝ),4] *ᵥ (WithLp.ofLp a-WithLp.ofLp b))) ∧
      (∀ a b, ‖WithLp.toLp 2 (rawLogits center network a-rawLogits center network b)‖≤
        (16/5:ℝ)*dist a b) := by
  refine ⟨?_,?_⟩
  · intro a b
    rw [actual_per_channel_normalizer_increment_is_diagonal_action,
      actual_source_inverse_scales_and_gain.2.1]
  · intro a b
    have hn := actual_per_channel_normalizer_is_lipschitz_with_maximum_inverse_scale
      center sourceScale actual_source_inverse_scales_and_gain.1 a b
    rw [actual_source_inverse_scales_and_gain.2.2.1] at hn
    have h := (hnetwork _ _).trans (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤4/5))
    simpa only [rawLogits,show (4/5:ℝ)*4=16/5 by norm_num,mul_assoc] using h

theorem actual_source_strict_radius_identity_rounding_and_fourfold_error :
    (2/5:ℝ)/(Real.sqrt 2*(16/5))=sourceRadius ∧
      0 < sourceRadius ∧
      |sourceRadius-883883/10000000|<1/20000000 ∧
      (2/5:ℝ)/(Real.sqrt 2*(4/5))=4*sourceRadius := by
  have hp : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  refine ⟨by unfold sourceRadius;field_simp;ring,by unfold sourceRadius;positivity,?_,
    by unfold sourceRadius;field_simp;ring⟩
  unfold sourceRadius
  rw [abs_lt]
  constructor
  · have h : (883883/10000000-1/20000000:ℝ)*(8*Real.sqrt 2)<1 := by nlinarith
    have hd : (883883/10000000-1/20000000:ℝ)<1/(8*Real.sqrt 2) :=
      (lt_div_iff₀ (by positivity)).mpr h
    linarith
  · have h : (1:ℝ)<(883883/10000000+1/20000000)*(8*Real.sqrt 2) := by nlinarith
    have hd := (div_lt_iff₀ (by positivity : (0:ℝ)<8*Real.sqrt 2)).mpr h
    linarith

theorem actual_source_raw_radius_preserves_every_competing_logit
    {O : Type*} [Fintype O] [DecidableEq O] (center : Fin 2 → ℝ)
    (network : EuclideanSpace ℝ (Fin 2) → O → ℝ) (winner : O)
    (first second : EuclideanSpace ℝ (Fin 2))
    (hc : (Finset.univ.erase winner).Nonempty)
    (hnetwork : ∀ a b, ‖WithLp.toLp 2 (network a-network b)‖≤(4/5:ℝ)*dist a b)
    (hmargin : actualLogitMargin (rawLogits center network) winner first
      (Finset.univ.erase winner) hc=2/5)
    (hradius : dist first second<sourceRadius) :
    ∀ other,other≠winner → rawLogits center network second other<rawLogits center network second winner := by
  apply actual_arbitrary_global_margin_radius_preserves_unique_prediction
    (rawLogits center network) winner first second (16/5) (by norm_num) hc
    (actual_source_center_cancels_and_raw_gain_is_three_point_two center network hnetwork).2
  rw [hmargin,actual_source_strict_radius_identity_rounding_and_fourfold_error.1]
  exact hradius

end SafeLearning.CompleteModulesDesignEasyPreprocessing
