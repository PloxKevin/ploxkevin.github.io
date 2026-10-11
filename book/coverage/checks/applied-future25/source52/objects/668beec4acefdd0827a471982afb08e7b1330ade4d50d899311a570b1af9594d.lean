import SafeLearning.CompleteAppliedCovarianceMatrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace SafeLearning.CompleteAppliedCovarianceConsequences
open CompleteAppliedCovarianceMatrix

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem actual_linear_combination_mean_is_the_same_combination_of_coordinate_means
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) (v : I → ℝ) :
    (∫ω,linearCombination X v ω ∂μ)=∑ i,v i*(∫ω,X i ω ∂μ) := by
  unfold linearCombination
  rw [integral_finsetSum _ (fun i _ => ((hX i).integrable (by norm_num)).const_mul (v i))]
  simp only [integral_const_mul]

theorem actual_covariance_quadratic_form_is_the_literal_centered_square_expectation
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) (v : I → ℝ) :
    v ⬝ᵥ (covarianceMatrix X μ *ᵥ v)=
      ∫ω,(∑ i,v i*(X i ω-(∫z,X i z ∂μ)))^2 ∂μ := by
  rw [actual_covariance_matrix_quadratic_form_is_the_true_variance X hX v,
    variance_eq_integral (actual_linear_combination_has_finite_second_moment X hX v).aemeasurable,
    actual_linear_combination_mean_is_the_same_combination_of_coordinate_means X hX v]
  congr 1
  ext ω
  simp only [linearCombination,mul_sub,Finset.sum_sub_distrib]

theorem actual_nondegenerate_covariance_matrix_is_genuinely_invertible
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ)
    (h : ∀ v : I → ℝ,v≠0 → ¬∃ c : ℝ,linearCombination X v =ᵐ[μ] fun _ => c) :
    IsUnit (covarianceMatrix X μ) ∧
      covarianceMatrix X μ*(covarianceMatrix X μ)⁻¹=1 ∧
      (covarianceMatrix X μ)⁻¹*covarianceMatrix X μ=1 := by
  have hp := (actual_covariance_matrix_positive_definite_iff_no_nonzero_combination_is_constant X hX).2 h
  letI := Matrix.invertibleOfIsUnitDet (covarianceMatrix X μ) (isUnit_iff_ne_zero.mpr hp.det_pos.ne')
  exact ⟨hp.isUnit,Matrix.mul_inv_of_invertible _,Matrix.inv_mul_of_invertible _⟩

theorem actual_isotropic_covariance_has_the_same_variance_in_every_unit_direction
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) (sigma : ℝ)
    (hisotropic : covarianceMatrix X μ=diagonal (fun _ => sigma^2))
    (v : I → ℝ) (hunit : ∑ i,(v i)^2=1) :
    Var[linearCombination X v;μ]=sigma^2 := by
  rw [←actual_covariance_matrix_quadratic_form_is_the_true_variance X hX v,hisotropic]
  simp only [Matrix.mulVec_diagonal,dotProduct]
  calc
    (∑ i,v i*(sigma^2*v i))=sigma^2*∑ i,(v i)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=sigma^2 := by rw [hunit,mul_one]

theorem actual_scalar_variance_has_both_printed_finite_second_moment_formulas
    (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    Var[Y;μ]=(∫ω,(Y ω-(∫z,Y z ∂μ))^2 ∂μ) ∧
      Var[Y;μ]=(∫ω,Y ω^2 ∂μ)-(∫ω,Y ω ∂μ)^2 :=
  ⟨variance_eq_integral hY.aemeasurable,variance_eq_sub hY⟩

theorem actual_scalar_affine_variance_is_the_literal_squared_scale
    (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    Var[fun ω => a*Y ω+b;μ]=a^2*Var[Y;μ] := by
  rw [variance_add_const (hY.const_mul a).aestronglyMeasurable,variance_const_mul]

theorem actual_standard_deviation_is_nonnegative_and_squared_equals_variance
    (Y : Ω → ℝ) :
    0≤Real.sqrt (Var[Y;μ]) ∧ (Real.sqrt (Var[Y;μ]))^2=Var[Y;μ] :=
  ⟨Real.sqrt_nonneg _,Real.sq_sqrt (variance_nonneg _ _)⟩

theorem actual_noise_variance_one_hundredth_has_standard_deviation_one_tenth :
    Real.sqrt (1/100:ℝ)=1/10 := by
  rw [show (1/100:ℝ)=(1/10)^2 by norm_num, Real.sqrt_sq (by norm_num : 0≤(1/10:ℝ))]

end SafeLearning.CompleteAppliedCovarianceConsequences
