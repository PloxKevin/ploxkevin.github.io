import SafeLearning.CompleteModulesGaussianMatrixLaws
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianRectangularDesignLaws
open SafeLearning.CompleteModulesGaussianMatrixLaws
variable {D T Omega : Type*} [Fintype D] [DecidableEq D] [Fintype T] [DecidableEq T]
  [MeasurableSpace Omega]

def designCLM (X : Matrix T D ℝ) : (D → ℝ) →L[ℝ] (T → ℝ) :=
  LinearMap.toContinuousLinearMap X.mulVecLin

theorem actual_standard_gaussian_parameter_linear_design_generates_the_true_centered_linear_kernel_signal
    (P : Measure Omega) [IsProbabilityMeasure P] (theta : Omega → D → ℝ)
    (htheta : HasGaussianLaw theta P)
    (hm : ∀ i,(∫ o,theta o i ∂P)=0)
    (hc : ∀ i j,cov[fun o => theta o i,fun o => theta o j;P]=if i=j then 1 else 0)
    (X : Matrix T D ℝ) :
    HasGaussianLaw (fun o => X*ᵥ theta o) P ∧
      (∀ t,(∫ o,(X*ᵥ theta o) t ∂P)=0) ∧
        (∀ t s,cov[fun o => (X*ᵥ theta o) t,fun o => (X*ᵥ theta o) s;P]=(X*Xᵀ) t s) := by
  refine ⟨htheta.map_fun (designCLM X),?_,?_⟩
  · intro t
    change (∫ o,∑ i,X t i*theta o i ∂P)=0
    rw [integral_finsetSum (fun i _ => (htheta.eval i).integrable.const_mul _)]
    simp only [integral_const_mul,hm,mul_zero,Finset.sum_const_zero]
  · intro t s
    change cov[fun o => ∑ i,X t i*theta o i,fun o => ∑ j,X s j*theta o j;P]=_
    rw [covariance_fun_sum_fun_sum (fun i => (htheta.eval i).memLp_two.const_mul _)
      (fun j => (htheta.eval j).memLp_two.const_mul _)]
    simp_rw [covariance_const_mul_left,covariance_const_mul_right,hc]
    simp [Matrix.mul_apply,Matrix.transpose_apply,mul_ite]

theorem actual_independent_standard_gaussian_parameter_law_provides_the_linear_kernel_prior_for_every_finite_design
    (X : Matrix T D ℝ) :
    HasGaussianLaw (fun theta : D → ℝ => X*ᵥ theta)
      (Measure.pi (fun _ : D => gaussianReal 0 1)) ∧
      (∀ t,(∫ theta : D → ℝ,(X*ᵥ theta) t ∂Measure.pi (fun _ : D => gaussianReal 0 1))=0) ∧
        (∀ t s,cov[fun theta : D → ℝ => (X*ᵥ theta) t,fun theta : D → ℝ => (X*ᵥ theta) s;
          Measure.pi (fun _ : D => gaussianReal 0 1)]=(X*Xᵀ) t s) := by
  have hs := actual_independent_scalar_gaussian_coordinates_have_their_true_means_and_diagonal_covariance
    (fun _ : D => 0) (fun _ : D => 1)
  simpa only [id_eq,NNReal.coe_one] using
    actual_standard_gaussian_parameter_linear_design_generates_the_true_centered_linear_kernel_signal
      (Measure.pi (fun _ : D => gaussianReal 0 1)) id
      (actual_every_finite_product_of_scalar_gaussians_is_jointly_gaussian
        (fun _ : D => 0) (fun _ : D => 1)) hs.1 hs.2 X

end SafeLearning.CompleteModulesGaussianRectangularDesignLaws
