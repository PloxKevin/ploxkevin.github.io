import SafeLearning.CompleteModulesSafeOptGaussianGapRKHS

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesSafeOptGaussianGapRKHSConsequences
open CompleteModulesSafeOptGaussianGapSeries CompleteModulesSafeOptGaussianGapFeatures
open CompleteModulesSafeOptGaussianGapRKHS

def actualCoefficientCoordinate (coefficient : ActualCoefficientSpace) (n : ℕ) : ℝ :=
  coefficient n

theorem actual_every_gaussian_rkhs_function_has_the_literal_infinite_basis_representation
    (coefficient : ActualCoefficientSpace) (x : ℝ) :
    letI : RKHS ℝ ActualCoefficientSpace ℝ ℝ := actualGaussianRKHS
    HasSum (fun n => actualCoefficientCoordinate coefficient n*actualGaussianFeature n x)
      ((RKHS.coeCLM ℝ) coefficient x) := by
  letI : RKHS ℝ ActualCoefficientSpace ℝ ℝ := actualGaussianRKHS
  change HasSum (fun n => actualCoefficientCoordinate coefficient n*actualGaussianFeature n x)
    (inner ℝ (actualFeatureVector x) coefficient)
  rw [real_inner_comm]
  simpa only [actualCoefficientCoordinate,RCLike.inner_apply,conj_trivial,mul_comm,
    actual_feature_vector_coordinates] using lp.hasSum_inner (𝕜:=ℝ) coefficient (actualFeatureVector x)

theorem actual_every_gaussian_rkhs_coefficient_has_the_literal_sum_of_squares_norm
    (coefficient : ActualCoefficientSpace) :
    ‖coefficient‖^2=∑' n, (actualCoefficientCoordinate coefficient n)^2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ) < (2:ENNReal).toReal) coefficient
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
    actualCoefficientCoordinate] using h

theorem actual_every_gaussian_coefficient_has_the_complete_hilbert_basis_expansion
    (coefficient : ActualCoefficientSpace) :
    HasSum (fun n => actualCoefficientCoordinate coefficient n • actualGaussianHilbertBasis n)
      coefficient := by
  exact actualGaussianHilbertBasis.hasSum_repr coefficient

end SafeLearning.CompleteModulesSafeOptGaussianGapRKHSConsequences
