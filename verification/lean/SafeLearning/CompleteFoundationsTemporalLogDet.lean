import SafeLearning.CompleteFoundationsSequentialLogDet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsTemporalLogDet

open SafeLearning.CompleteFoundationsSequentialLogDet
open SafeLearning.CompleteFoundationsUniversalMatrices

section TemporalFamily
variable {feature : Type*} [Fintype feature] [DecidableEq feature]

def temporalFeatures (φ : ℕ → feature → ℝ) (t : ℕ) : Matrix (Fin t) feature ℝ :=
  fun i j => φ i j
def temporalCovariance (lambda : ℝ) (φ : ℕ → feature → ℝ) (t : ℕ) :
    Matrix feature feature ℝ :=
  lambda • 1+∑ i∈Finset.range t,Matrix.vecMulVec (φ i) (φ i)
def temporalVariance (lambda : ℝ) (φ : ℕ → feature → ℝ) (t : ℕ) : ℝ :=
  posteriorVariance lambda (temporalFeatures φ t) (φ t)

theorem actual_temporal_feature_gram_is_the_cumulative_outer_sum
    (φ : ℕ → feature → ℝ) (t : ℕ) :
    featureGram (temporalFeatures φ t)=∑ i∈Finset.range t,Matrix.vecMulVec (φ i) (φ i) := by
  ext i j
  simp only [featureGram,temporalFeatures,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.vecMulVec,Matrix.sum_apply,Matrix.of_apply]
  exact Fin.sum_univ_eq_sum_range (fun k => φ k i*φ k j) t

theorem actual_temporal_covariance_is_the_feature_covariance (lambda : ℝ)
    (φ : ℕ → feature → ℝ) (t : ℕ) :
    temporalCovariance lambda φ t=featureCovariance lambda (temporalFeatures φ t) := by
  rw [featureCovariance,actual_temporal_feature_gram_is_the_cumulative_outer_sum]
  rfl

theorem actual_temporal_covariance_update (lambda : ℝ) (φ : ℕ → feature → ℝ) (t : ℕ) :
    temporalCovariance lambda φ (t+1)=
      temporalCovariance lambda φ t+Matrix.vecMulVec (φ t) (φ t) := by
  simp only [temporalCovariance,Finset.sum_range_succ]
  abel

theorem actual_temporal_initial_covariance (lambda : ℝ) (φ : ℕ → feature → ℝ) :
    temporalCovariance lambda φ 0=lambda • 1 := by
  simp [temporalCovariance]

theorem actual_temporal_covariance_positive_and_nonsingular (lambda : ℝ) (hl : 0<lambda)
    (φ : ℕ → feature → ℝ) (t : ℕ) :
    (temporalCovariance lambda φ t).PosDef ∧
      IsUnit (temporalCovariance lambda φ t).det := by
  rw [actual_temporal_covariance_is_the_feature_covariance]
  have h := actual_regularized_feature_and_kernel_invertible lambda hl (temporalFeatures φ t)
  exact ⟨h.1,h.2.1⟩

theorem actual_temporal_determinant_step (lambda : ℝ) (hl : 0<lambda)
    (φ : ℕ → feature → ℝ) (t : ℕ) :
    (temporalCovariance lambda φ (t+1)).det=
      (temporalCovariance lambda φ t).det*(1+temporalVariance lambda φ t/lambda) := by
  rw [actual_temporal_covariance_update,actual_temporal_covariance_is_the_feature_covariance]
  have h := actual_point_update_determinant_ratio lambda hl (temporalFeatures φ t) (φ t)
  have hn := (actual_regularized_feature_and_kernel_invertible lambda hl
    (temporalFeatures φ t)).2.1
  exact (by simpa [temporalVariance,mul_comm] using
    (div_eq_iff (isUnit_iff_ne_zero.mp hn)).mp h)

theorem actual_initial_normalized_determinant (lambda : ℝ) (hl : 0<lambda)
    (φ : ℕ → feature → ℝ) :
    (temporalCovariance lambda φ 0).det/lambda^(Fintype.card feature)=1 := by
  rw [actual_temporal_initial_covariance,Matrix.det_smul,Matrix.det_one,mul_one]
  exact div_self (pow_ne_zero _ hl.ne')

theorem actual_all_horizons_determinant_product (lambda : ℝ) (hl : 0<lambda)
    (φ : ℕ → feature → ℝ) (t : ℕ) :
    (temporalCovariance lambda φ t).det/lambda^(Fintype.card feature)=
      ∏ i∈Finset.range t,(1+temporalVariance lambda φ i/lambda) := by
  induction t with
  | zero => simpa using actual_initial_normalized_determinant lambda hl φ
  | succ t ih =>
      rw [actual_temporal_determinant_step lambda hl φ t,Finset.prod_range_succ,← ih]
      ring

theorem actual_all_horizons_kernel_determinant_product (lambda : ℝ) (hl : 0<lambda)
    (φ : ℕ → feature → ℝ) (t : ℕ) :
    (1+lambda⁻¹ • kernelGram (temporalFeatures φ t)).det=
      ∏ i∈Finset.range t,(1+temporalVariance lambda φ i/lambda) := by
  rw [actual_sylvester_normalized_feature_determinant lambda hl,
    ← actual_temporal_covariance_is_the_feature_covariance,
    actual_all_horizons_determinant_product lambda hl φ t]

end TemporalFamily

def sourceFeature (i : ℕ) : Fin 2 → ℝ :=
  if i=0 then ![1,0] else if i=1 then ![1/2,Real.sqrt 3/2] else 0

theorem actual_two_source_feature_rows :
    temporalFeatures sourceFeature 2=!![(1 : ℝ),0;1/2,Real.sqrt 3/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [temporalFeatures,sourceFeature]

theorem actual_source_kernel_is_the_true_feature_gram :
    kernelGram (temporalFeatures sourceFeature 2)=sourceKernel := by
  rw [actual_two_source_feature_rows]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kernelGram,sourceKernel,Matrix.mul_apply,Fin.sum_univ_succ] <;> nlinarith

theorem actual_source_cross_gram_values :
    sourceFeature 0 ⬝ᵥ sourceFeature 0=1 ∧
    sourceFeature 1 ⬝ᵥ sourceFeature 0=1/2 ∧
    sourceFeature 1 ⬝ᵥ sourceFeature 1=1 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  simp [sourceFeature,dotProduct,Fin.sum_univ_succ]
  nlinarith

theorem actual_first_source_posterior_variance : temporalVariance sourceNoise sourceFeature 0=1 := by
  norm_num [temporalVariance,posteriorVariance,sourceNoise,sourceFeature,Matrix.mulVec,dotProduct]

theorem actual_second_source_posterior_variance :
    temporalVariance sourceNoise sourceFeature 1=sourceVariance := by
  have hf : temporalFeatures sourceFeature 1=!![(1 : ℝ),0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [temporalFeatures,sourceFeature]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  rw [temporalVariance,posteriorVariance,hf]
  norm_num [sourceFeature,noisyKernel,kernelGram,sourceNoise,sourceVariance,sourceKernel,
    Matrix.mulVec,Matrix.mul_apply,Matrix.vecMul,Matrix.inv_def,Matrix.det_fin_one,Matrix.adjugate_fin_one,
    dotProduct,Fin.sum_univ_succ]
  nlinarith

theorem actual_source_product_is_the_instantiated_temporal_identity :
    (1+sourceNoise⁻¹ • sourceKernel).det=
      (1+temporalVariance sourceNoise sourceFeature 0/sourceNoise)*
        (1+temporalVariance sourceNoise sourceFeature 1/sourceNoise) := by
  rw [← actual_source_kernel_is_the_true_feature_gram]
  simpa [Finset.prod_range_succ] using
    actual_all_horizons_kernel_determinant_product sourceNoise (by norm_num [sourceNoise])
      sourceFeature 2

end SafeLearning.CompleteFoundationsTemporalLogDet
