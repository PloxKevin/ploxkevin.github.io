import SafeLearning.CompleteModulesGaussianPSDInformation
import SafeLearning.CompleteModulesGaussianRectangularDesignLaws
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianLinearDesignInformation
open SafeLearning.CompleteModulesGaussianProductInformation
open SafeLearning.CompleteModulesGaussianMatrixLaws
open SafeLearning.CompleteModulesGaussianPSDInformation
open SafeLearning.CompleteModulesGaussianRectangularDesignLaws
open SafeLearning.CompleteModulesGPLinearInformationBounds
variable {D T Omega : Type*} [Fintype D] [DecidableEq D] [Fintype T] [DecidableEq T]
  [MeasurableSpace Omega]

theorem actual_linear_kernel_prior_and_independent_gaussian_noise_have_the_true_official_information_gain
    (P : Measure Omega) [IsProbabilityMeasure P] (theta : Omega → D → ℝ) (E : Omega → T → ℝ)
    (htheta : HasLaw theta (Measure.pi (fun _ : D => gaussianReal 0 1)) P)
    (lambda : ℝ≥0) (hlambda : lambda ≠ 0)
    (hnoise : HasLaw E (Measure.pi (fun _ : T => gaussianReal 0 lambda)) P)
    (hi : IndepFun theta E P) (X : Matrix T D ℝ) :
    klDiv (P.map (fun o => (X*ᵥ theta o,E o+X*ᵥ theta o)))
      ((P.map (fun o => X*ᵥ theta o)).prod (P.map (fun o => E o+X*ᵥ theta o)))=
        ENNReal.ofReal (information (X*Xᵀ) (lambda:ℝ)) := by
  have hstd := actual_every_finite_product_of_scalar_gaussians_is_jointly_gaussian
    (fun _ : D => 0) (fun _ : D => 1)
  haveI : IsGaussian (Measure.pi (fun _ : D => gaussianReal 0 1)) := by
    simpa only [Measure.map_id] using hstd.isGaussian_map
  have hthetaG := htheta.hasGaussianLaw
  have hs := actual_independent_scalar_gaussian_coordinates_have_their_true_means_and_diagonal_covariance
    (fun _ : D => 0) (fun _ : D => 1)
  have hm : ∀ i,(∫ o,theta o i ∂P)=0 := by
    intro i
    simpa only [Function.comp_def,integral_eval,integral_id_gaussianReal] using
      htheta.integral_comp ((measurable_pi_apply i).aestronglyMeasurable)
  have hc : ∀ i j,cov[fun o => theta o i,fun o => theta o j;P]=if i=j then 1 else 0 := by
    intro i j
    have h := htheta.covariance_fun_comp
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    simpa only [hs.2,NNReal.coe_one] using h
  have hF := actual_standard_gaussian_parameter_linear_design_generates_the_true_centered_linear_kernel_signal
    P theta hthetaG hm hc X
  have hind : IndepFun (fun o => X*ᵥ theta o) E P := by
    simpa only [Function.comp_def,id_eq] using
      hi.comp (designCLM X).continuous.measurable measurable_id
  have hG : (X*Xᵀ).PosSemidef := by
    simpa only [Matrix.transpose_transpose] using actual_design_gram_is_positive_semidefinite Xᵀ
  exact actual_arbitrary_centered_finite_gaussian_signal_and_independent_isotropic_noise_have_the_official_half_logdet_mutual_information
    P (fun o => X*ᵥ theta o) E hF.1 hnoise.aemeasurable hind (X*Xᵀ) hG
      hF.2.1 hF.2.2 lambda hlambda hnoise.map_eq

theorem actual_source_noisy_observation_then_latent_order_has_the_same_official_linear_kernel_information_gain
    (P : Measure Omega) [IsProbabilityMeasure P] (theta : Omega → D → ℝ) (E : Omega → T → ℝ)
    (htheta : HasLaw theta (Measure.pi (fun _ : D => gaussianReal 0 1)) P)
    (lambda : ℝ≥0) (hlambda : lambda ≠ 0)
    (hnoise : HasLaw E (Measure.pi (fun _ : T => gaussianReal 0 lambda)) P)
    (hi : IndepFun theta E P) (X : Matrix T D ℝ) :
    klDiv (P.map (fun o => (E o+X*ᵥ theta o,X*ᵥ theta o)))
      ((P.map (fun o => E o+X*ᵥ theta o)).prod (P.map (fun o => X*ᵥ theta o)))=
        ENNReal.ofReal (information (Xᵀ*X) (lambda:ℝ)) := by
  let F := fun o => X*ᵥ theta o
  let Y := fun o => E o+F o
  have hF : AEMeasurable F P := (designCLM X).continuous.measurable.comp_aemeasurable htheta.aemeasurable
  have hY : AEMeasurable Y P := hnoise.aemeasurable.add hF
  have h := actual_official_KL_is_invariant_under_any_measurable_equivalence
    (P.map (fun o => (F o,Y o))) ((P.map F).prod (P.map Y))
      (MeasurableEquiv.prodComm : (T → ℝ) × (T → ℝ) ≃ᵐ (T → ℝ) × (T → ℝ))
  change klDiv ((P.map (fun o => (F o,Y o))).map Prod.swap)
    (((P.map F).prod (P.map Y)).map Prod.swap)=_ at h
  rw [Measure.prod_swap,AEMeasurable.map_map_of_aemeasurable
    measurable_swap.aemeasurable (hF.prodMk hY)] at h
  change klDiv (P.map (fun o => (E o+X*ᵥ theta o,X*ᵥ theta o)))
    ((P.map (fun o => E o+X*ᵥ theta o)).prod (P.map (fun o => X*ᵥ theta o)))=_ at h
  rw [h,actual_linear_kernel_prior_and_independent_gaussian_noise_have_the_true_official_information_gain
    P theta E htheta lambda hlambda hnoise hi X]
  unfold information
  rw [actual_weinstein_aronszajn_identity_for_the_linear_design X (lambda:ℝ)]

end SafeLearning.CompleteModulesGaussianLinearDesignInformation
