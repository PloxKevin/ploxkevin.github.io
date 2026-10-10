import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace SafeLearning.CompleteAppliedCovarianceMatrix

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] {μ : Measure Ω} [IsProbabilityMeasure μ]

def covarianceMatrix (X : I → Ω → ℝ) (μ : Measure Ω) : Matrix I I ℝ :=
  fun i j => cov[X i,X j;μ]

def linearCombination (X : I → Ω → ℝ) (v : I → ℝ) (ω : Ω) : ℝ :=
  ∑ i,v i*X i ω

lemma actual_linear_combination_has_finite_second_moment
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) (v : I → ℝ) :
    MemLp (linearCombination X v) 2 μ := by
  exact memLp_finsetSum _ (fun i _ => (hX i).const_mul (v i))

theorem actual_covariance_matrix_is_the_true_expected_centered_outer_product
    (X : I → Ω → ℝ) :
    covarianceMatrix X μ = fun i j =>
      ∫ω,(X i ω-(∫z,X i z ∂μ))*(X j ω-(∫z,X j z ∂μ)) ∂μ := rfl

theorem actual_source_covariance_is_the_true_bilinear_matrix_form
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) (v w : I → ℝ) :
    cov[linearCombination X v,linearCombination X w;μ] =
      v ⬝ᵥ (covarianceMatrix X μ *ᵥ w) := by
  unfold linearCombination
  rw [covariance_fun_sum_fun_sum (fun i => (hX i).const_mul (v i))
    (fun j => (hX j).const_mul (w j))]
  simp only [covariance_const_mul_left,covariance_const_mul_right,
    dotProduct,mulVec,covarianceMatrix,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_covariance_matrix_quadratic_form_is_the_true_variance
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) (v : I → ℝ) :
    v ⬝ᵥ (covarianceMatrix X μ *ᵥ v) = Var[linearCombination X v;μ] := by
  rw [←actual_source_covariance_is_the_true_bilinear_matrix_form X hX v v,
    covariance_self (actual_linear_combination_has_finite_second_moment X hX v).aemeasurable]

theorem actual_covariance_matrix_is_symmetric_and_positive_semidefinite
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) :
    (covarianceMatrix X μ).IsHermitian ∧ (covarianceMatrix X μ).PosSemidef := by
  have hh : (covarianceMatrix X μ).IsHermitian := by
    ext i j
    simp only [conjTranspose_apply,covarianceMatrix,star_trivial]
    exact covariance_comm (X j) (X i)
  refine ⟨hh,PosSemidef.of_dotProduct_mulVec_nonneg hh ?_⟩
  intro v
  simpa only [star_trivial,actual_covariance_matrix_quadratic_form_is_the_true_variance X hX v]
    using (variance_nonneg (linearCombination X v) μ)

theorem actual_finite_second_moment_variance_zero_iff_almost_sure_constant
    (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    Var[Y;μ]=0 ↔ ∃ c : ℝ,Y =ᵐ[μ] fun _ => c := by
  constructor
  · intro h
    exact ⟨∫ω,Y ω ∂μ,ae_eq_integral_of_variance_eq_zero hY h⟩
  · rintro ⟨c,hc⟩
    rw [variance_congr hc,variance_eq_integral (by fun_prop)]
    simp

theorem actual_covariance_matrix_positive_definite_iff_no_nonzero_combination_is_constant
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ) :
    (covarianceMatrix X μ).PosDef ↔
      ∀ v : I → ℝ,v≠0 → ¬∃ c : ℝ,linearCombination X v =ᵐ[μ] fun _ => c := by
  rw [posDef_iff_dotProduct_mulVec]
  have hh := (actual_covariance_matrix_is_symmetric_and_positive_semidefinite X hX).1
  simp only [hh,true_and,star_trivial,
    actual_covariance_matrix_quadratic_form_is_the_true_variance X hX]
  constructor
  · intro h v hv hc
    have hz := (actual_finite_second_moment_variance_zero_iff_almost_sure_constant _
      (actual_linear_combination_has_finite_second_moment X hX v)).2 hc
    exact (ne_of_gt (h hv)) hz
  · intro h v hv
    exact lt_of_le_of_ne (variance_nonneg _ _) (fun hz =>
      h v hv ((actual_finite_second_moment_variance_zero_iff_almost_sure_constant _
        (actual_linear_combination_has_finite_second_moment X hX v)).1 hz.symm))

def affineVector (X : I → Ω → ℝ) (A : Matrix J I ℝ) (b : J → ℝ) (j : J) (ω : Ω) : ℝ :=
  linearCombination X (A j) ω+b j

theorem actual_affine_random_vector_has_the_true_transformed_covariance
    (X : I → Ω → ℝ) (hX : ∀ i,MemLp (X i) 2 μ)
    (A : Matrix J I ℝ) (b : J → ℝ) :
    covarianceMatrix (affineVector X A b) μ=A*covarianceMatrix X μ*Aᵀ := by
  ext k l
  change cov[fun ω => linearCombination X (A k) ω+b k,
    fun ω => linearCombination X (A l) ω+b l;μ]=_
  rw [covariance_add_const_left
    ((actual_linear_combination_has_finite_second_moment X hX (A k)).integrable (by norm_num)),
    covariance_add_const_right
    ((actual_linear_combination_has_finite_second_moment X hX (A l)).integrable (by norm_num)),
    actual_source_covariance_is_the_true_bilinear_matrix_form X hX]
  simp only [dotProduct,mulVec,Matrix.mul_apply,transpose_apply,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end SafeLearning.CompleteAppliedCovarianceMatrix
