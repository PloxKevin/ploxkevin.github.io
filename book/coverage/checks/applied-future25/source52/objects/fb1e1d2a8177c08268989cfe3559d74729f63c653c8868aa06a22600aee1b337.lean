import SafeLearning.CompleteModulesPosterior
import SafeLearning.CompleteAppliedGaussianBayesGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace SafeLearning.CompleteModulesSafeOptPosteriorConsequences
open SafeLearning.CompleteModulesKernel SafeLearning.CompleteModulesPosterior

theorem actual_posterior_variance_cannot_increase_when_any_new_observation_is_appended
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype I]
    (feature : I → H) (target anchor : H) (noise : ℝ) (hnoise : 0 < noise) :
    posteriorVariance (Sum.elim feature (fun _ : Unit => anchor)) target
      (posteriorWeights (Sum.elim feature (fun _ : Unit => anchor)) target noise hnoise) ≤
      posteriorVariance feature target (posteriorWeights feature target noise hnoise) := by
  let oldWeight := posteriorWeights feature target noise hnoise
  let extendedFeature : Sum I Unit → H := Sum.elim feature (fun _ => anchor)
  let zeroExtendedWeight : Sum I Unit → ℝ := Sum.elim oldWeight (fun _ => 0)
  have hmin := residual_objective_global_minimum extendedFeature target noise hnoise.le
    (posteriorWeights extendedFeature target noise hnoise) zeroExtendedWeight
    (posterior_weights_solve_system extendedFeature target noise hnoise)
  have he : residualObjective extendedFeature target noise zeroExtendedWeight=
      residualObjective feature target noise oldWeight := by
    simp [residualObjective,combination,extendedFeature,zeroExtendedWeight,Fintype.sum_sum_type]
  rw [he,residual_objective_at_solution feature target noise oldWeight
    (posterior_weights_solve_system feature target noise hnoise)] at hmin
  exact hmin

theorem actual_observed_point_gaussian_posterior_variance_strictly_decreases
    (priorVariance noiseVariance : ℝ≥0) (hv : 0 < priorVariance) (hw : 0 < noiseVariance) :
    SafeLearning.CompleteAppliedGaussianBayesGeneral.posteriorVariance priorVariance noiseVariance < priorVariance := by
  change priorVariance*noiseVariance/(priorVariance+noiseVariance) < priorVariance
  apply (div_lt_iff₀ (add_pos hv hw)).mpr
  nlinarith

open SafeLearning.CompleteAppliedGaussianBayesGeneral

theorem actual_source_low_observation_derives_the_printed_gaussian_mean_and_variance :
    (evidence (21/20) (21/44) (9/400) (9/176))⁻¹ •
      likelihoodWeightedPrior (21/20) (21/44) (9/400) (9/176)=gaussianReal (7/8) (1/64) ∧
      (21/44:ℝ) < 21/20 ∧ (7/8:ℝ) < 21/20 ∧
      (1/64:ℝ) < 9/400 ∧ Real.sqrt (9/400)=3/20 ∧ Real.sqrt (1/64)=1/8 ∧
      (21/20:ℝ)-3/20=9/10 ∧ (21/20:ℝ)+3/20=6/5 ∧
      (7/8:ℝ)-1/8=3/4 ∧ (7/8:ℝ)+1/8=1 := by
  have hp := actual_general_normalized_likelihood_posterior_is_the_derived_gaussian
    (21/20) (21/44) (9/400) (9/176) (by norm_num) (by norm_num)
  have hfirst : (evidence (21/20) (21/44) (9/400) (9/176))⁻¹ •
      likelihoodWeightedPrior (21/20) (21/44) (9/400) (9/176)=gaussianReal (7/8) (1/64) := by
    convert hp using 1 <;> norm_num [posteriorMean,SafeLearning.CompleteAppliedGaussianBayesGeneral.posteriorVariance]
  refine ⟨hfirst,by norm_num,by norm_num,by norm_num,?_,?_,by norm_num,by norm_num,by norm_num,by norm_num⟩
  · norm_num
  · norm_num

end SafeLearning.CompleteModulesSafeOptPosteriorConsequences
