import SafeLearning.CompleteModulesGPLinearInformationBounds
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPCorrectedConfidenceComparison
open CompleteModulesGPLinearInformationBounds
variable {I : Type*} [Fintype I] [DecidableEq I]

def originalSmallNoise (K : Matrix I I ℝ) (R delta : ℝ) : ℝ :=
  R*Real.sqrt (Real.log (1+K).det-2*Real.log delta)
def correctedSmallNoise (K : Matrix I I ℝ) (lambda R delta : ℝ) : ℝ :=
  (R/Real.sqrt lambda)*Real.sqrt (Real.log (1+lambda⁻¹ • K).det-2*Real.log delta)

theorem actual_psd_small_regularizer_increases_the_true_ridge_logdet
    (K : Matrix I I ℝ) (hK : K.PosSemidef) (lambda : ℝ)
    (hlambda : 0 < lambda) (hsmall : lambda ≤ 1) :
    Real.log (1+K).det ≤ Real.log (1+lambda⁻¹ • K).det := by
  have he : Real.log (1+K).det=∑ i,Real.log (1+hK.isHermitian.eigenvalues i) := by
    simpa using actual_positive_semidefinite_logdet_is_the_sum_of_its_true_spectral_logarithms
      K hK 1 (by norm_num)
  rw [he,actual_positive_semidefinite_logdet_is_the_sum_of_its_true_spectral_logarithms K hK lambda hlambda]
  apply Finset.sum_le_sum
  intro i _
  have hp := hK.eigenvalues_nonneg i
  apply Real.log_le_log (show 0 < 1+hK.isHermitian.eigenvalues i by positivity)
  apply add_le_add le_rfl
  apply (le_div_iff₀ hlambda).mpr
  nlinarith

theorem actual_psd_unregularized_unit_ridge_logdet_is_nonnegative
    (K : Matrix I I ℝ) (hK : K.PosSemidef) : 0 ≤ Real.log (1+K).det := by
  have he := actual_positive_semidefinite_logdet_is_the_sum_of_its_true_spectral_logarithms
    K hK 1 (by norm_num)
  simp only [inv_one,one_smul,div_one] at he
  rw [he]
  exact Finset.sum_nonneg (fun i _ => Real.log_nonneg (by linarith [hK.eigenvalues_nonneg i]))

theorem actual_nontrivial_confidence_failure_probability_makes_the_original_square_root_strictly_positive
    (K : Matrix I I ℝ) (hK : K.PosSemidef) (delta : ℝ)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    0 < Real.sqrt (Real.log (1+K).det-2*Real.log delta) := by
  have hd := Real.log_neg hdelta hdeltaOne
  have hk := actual_psd_unregularized_unit_ridge_logdet_is_nonnegative K hK
  exact Real.sqrt_pos.mpr (by linarith)

theorem actual_corrected_noise_is_at_least_inverse_sqrt_lambda_times_original
    (K : Matrix I I ℝ) (hK : K.PosSemidef) (lambda R delta : ℝ)
    (hlambda : 0 < lambda) (hsmall : lambda ≤ 1) (hR : 0 ≤ R) :
    originalSmallNoise K R delta/Real.sqrt lambda ≤ correctedSmallNoise K lambda R delta := by
  have hlog := actual_psd_small_regularizer_increases_the_true_ridge_logdet K hK lambda hlambda hsmall
  have hs := Real.sqrt_le_sqrt (sub_le_sub_right hlog (2*Real.log delta))
  have hp : 0 ≤ R/Real.sqrt lambda := div_nonneg hR (Real.sqrt_nonneg _)
  unfold originalSmallNoise correctedSmallNoise
  convert mul_le_mul_of_nonneg_left hs hp using 1 <;> ring

theorem actual_positive_noise_with_lambda_below_one_strictly_understates_the_corrected_noise
    (K : Matrix I I ℝ) (hK : K.PosSemidef) (lambda R delta : ℝ)
    (hlambda : 0 < lambda) (hsmall : lambda < 1) (hR : 0 < R)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    originalSmallNoise K R delta < correctedSmallNoise K lambda R delta := by
  have hlp : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  have hls : Real.sqrt lambda < 1 := by
    have hs := Real.sqrt_lt_sqrt hlambda.le hsmall
    simpa using hs
  have hp : 0 < originalSmallNoise K R delta := mul_pos hR
    (actual_nontrivial_confidence_failure_probability_makes_the_original_square_root_strictly_positive
      K hK delta hdelta hdeltaOne)
  have hstrict : originalSmallNoise K R delta < originalSmallNoise K R delta/Real.sqrt lambda := by
    apply (lt_div_iff₀ hlp).mpr
    nlinarith
  exact hstrict.trans_le (actual_corrected_noise_is_at_least_inverse_sqrt_lambda_times_original
    K hK lambda R delta hlambda hsmall.le hR.le)

theorem actual_adding_the_same_rkhs_bound_preserves_the_strict_original_error
    (K : Matrix I I ℝ) (hK : K.PosSemidef) (lambda B R delta : ℝ)
    (hlambda : 0 < lambda) (hsmall : lambda < 1) (hR : 0 < R)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    B+originalSmallNoise K R delta < B+correctedSmallNoise K lambda R delta := by
  simpa only [add_comm] using add_lt_add_left
    (actual_positive_noise_with_lambda_below_one_strictly_understates_the_corrected_noise
      K hK lambda R delta hlambda hsmall hR hdelta hdeltaOne) B

theorem actual_at_lambda_one_both_source_noise_formulas_coincide
    (K : Matrix I I ℝ) (R delta : ℝ) :
    correctedSmallNoise K 1 R delta=originalSmallNoise K R delta := by
  simp [correctedSmallNoise,originalSmallNoise]

theorem actual_lambda_at_least_one_original_noise_is_conservatively_larger
    (lambda R A : ℝ) (hlambda : 1 ≤ lambda) (hR : 0 ≤ R) :
    (R/Real.sqrt lambda)*Real.sqrt A ≤ R*Real.sqrt A := by
  have hs : 1 ≤ Real.sqrt lambda := by simpa using Real.sqrt_le_sqrt hlambda
  have hr : R/Real.sqrt lambda ≤ R := by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hs)).mpr
    nlinarith
  exact mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _)

theorem actual_any_valid_narrower_band_is_preserved_by_the_conservative_larger_multiplier
    (mean truth sigma corrected original : ℝ) (hsigma : 0 ≤ sigma)
    (horder : corrected ≤ original) (hvalid : |mean-truth| ≤ corrected*sigma) :
    |mean-truth| ≤ original*sigma :=
  hvalid.trans (mul_le_mul_of_nonneg_right horder hsigma)

end SafeLearning.CompleteModulesGPCorrectedConfidenceComparison
