import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SafeLearning.CompleteModulesGPNoiseConsequences

theorem actual_source_centered_gaussian_noise_has_the_genuine_subgaussian_mgf
    (variance : ℝ≥0) :
    HasSubgaussianMGF id variance (gaussianReal 0 variance) := by
  constructor
  · intro t
    exact integrable_exp_mul_gaussianReal t
  · intro t
    simp only [mgf_id_gaussianReal, zero_mul, zero_add, le_refl]

theorem actual_source_gaussian_noise_scale_one_tenth_has_subgaussian_variance_one_hundredth :
    HasSubgaussianMGF id (1/100 : ℝ≥0) (gaussianReal 0 ((1/10 : ℝ≥0)^2)) := by
  norm_num
  exact actual_source_centered_gaussian_noise_has_the_genuine_subgaussian_mgf _

end SafeLearning.CompleteModulesGPNoiseConsequences
