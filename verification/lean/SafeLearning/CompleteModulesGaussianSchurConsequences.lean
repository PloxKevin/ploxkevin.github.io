import SafeLearning.CompleteModulesGaussianRegressionFinite

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianSchurConsequences
open CompleteModulesGaussianRegressionFinite

variable {I J Omega : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [MeasurableSpace Omega]

theorem actual_arbitrary_invertible_covariance_blocks_have_the_literal_schur_block_inverse
    (A : Matrix I I ℝ) (C : Matrix I J ℝ) (B : Matrix J J ℝ)
    (hA : IsUnit A) (hS : IsUnit (B-Cᵀ*A⁻¹*C)) :
    (fromBlocks A C Cᵀ B)⁻¹=
      fromBlocks (A⁻¹+A⁻¹*C*(B-Cᵀ*A⁻¹*C)⁻¹*Cᵀ*A⁻¹)
        (-(A⁻¹*C*(B-Cᵀ*A⁻¹*C)⁻¹))
        (-((B-Cᵀ*A⁻¹*C)⁻¹*Cᵀ*A⁻¹)) ((B-Cᵀ*A⁻¹*C)⁻¹) := by
  obtain ⟨iA⟩ := hA.nonempty_invertible
  letI := iA
  have hs : IsUnit (B-Cᵀ*⅟A*C) := by simpa only [invOf_eq_nonsing_inv] using hS
  obtain ⟨iS⟩ := hs.nonempty_invertible
  letI := iS
  letI := fromBlocks₁₁Invertible A C Cᵀ B
  simpa only [invOf_eq_nonsing_inv] using invOf_fromBlocks₁₁_eq A C Cᵀ B

theorem actual_observation_covariance_is_symmetric
    (P : Measure Omega) (Y : Omega → I → ℝ) :
    (observationCovariance P Y)ᵀ=observationCovariance P Y := by
  ext i j
  exact covariance_comm _ _

theorem actual_inverse_covariance_regression_dot_is_the_printed_cross_transpose_expression
    (P : Measure Omega) (Y : Omega → I → ℝ) (C y : I → ℝ) :
    ((observationCovariance P Y)⁻¹ *ᵥ C) ⬝ᵥ y=
      C ⬝ᵥ ((observationCovariance P Y)⁻¹ *ᵥ y) := by
  have hs : ((observationCovariance P Y)⁻¹)ᵀ=(observationCovariance P Y)⁻¹ := by
    rw [transpose_nonsing_inv,actual_observation_covariance_is_symmetric]
  rw [dotProduct_comm,dotProduct_mulVec,← mulVec_transpose,hs,dotProduct_comm]

theorem actual_zero_mean_finite_joint_gaussian_derives_the_literal_gp_mean_and_schur_variance
    (P : Measure Omega) [IsProbabilityMeasure P] (Y : Omega → I → ℝ) (Z : Omega → ℝ)
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P)
    (hunit : IsUnit (observationCovariance P Y))
    (hY : ∀ i,(∫ o,Y o i ∂P)=0) (hZ : (∫ o,Z o ∂P)=0) :
    P.map (fun o => (Y o,Z o))=(P.map Y) ⊗ₘ
      ⟨fun y => gaussianReal
          (crossCovariance P Y Z ⬝ᵥ ((observationCovariance P Y)⁻¹ *ᵥ y))
          (Var[Z;P]-crossCovariance P Y Z ⬝ᵥ
            ((observationCovariance P Y)⁻¹ *ᵥ crossCovariance P Y Z)).toNNReal,
        by fun_prop⟩ := by
  have h := actual_arbitrary_finite_joint_gaussian_has_the_true_schur_conditional_kernel P Y Z hYZ hunit
  dsimp only at h
  rw [h]
  congr 1
  ext y : 1
  change gaussianReal _ _=gaussianReal _ _
  simp only [conditionalKernel,hY,hZ,mul_zero,Finset.sum_const_zero,sub_zero,zero_add]
  rw [actual_inverse_covariance_regression_dot_is_the_printed_cross_transpose_expression,
    dotProduct_comm ((observationCovariance P Y)⁻¹ *ᵥ crossCovariance P Y Z)]

theorem actual_gp_covariance_identification_translates_to_the_source_ridge_and_query_formula
    (P : Measure Omega) [IsProbabilityMeasure P] (Y : Omega → I → ℝ) (Z : Omega → ℝ)
    (K : Matrix I I ℝ) (C : I → ℝ) (B lambda : ℝ)
    (hYZ : HasGaussianLaw (fun o => (Y o,Z o)) P)
    (hcov : observationCovariance P Y=K+lambda • (1 : Matrix I I ℝ))
    (hcross : crossCovariance P Y Z=C) (hvariance : Var[Z;P]=B)
    (hunit : IsUnit (K+lambda • (1 : Matrix I I ℝ)))
    (hY : ∀ i,(∫ o,Y o i ∂P)=0) (hZ : (∫ o,Z o ∂P)=0) :
    P.map (fun o => (Y o,Z o))=(P.map Y) ⊗ₘ
      ⟨fun y => gaussianReal (C ⬝ᵥ ((K+lambda • (1 : Matrix I I ℝ))⁻¹ *ᵥ y))
          (B-C ⬝ᵥ ((K+lambda • (1 : Matrix I I ℝ))⁻¹ *ᵥ C)).toNNReal,
        by fun_prop⟩ := by
  have hu : IsUnit (observationCovariance P Y) := by rw [hcov];exact hunit
  simpa only [hcov,hcross,hvariance] using
    actual_zero_mean_finite_joint_gaussian_derives_the_literal_gp_mean_and_schur_variance
      P Y Z hYZ hu hY hZ

end SafeLearning.CompleteModulesGaussianSchurConsequences
