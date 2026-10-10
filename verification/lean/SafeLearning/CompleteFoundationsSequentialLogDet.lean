import SafeLearning.CompleteFoundationsUniversalMatrices
import SafeLearning.CompleteFoundationsGramRegularization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsSequentialLogDet

open SafeLearning.CompleteFoundationsUniversalMatrices
open SafeLearning.CompleteFoundationsGramRegularization

def sourceKernel : Matrix (Fin 2) (Fin 2) ℝ := !![1,1/2;1/2,1]
def sourceNoise : ℝ := 1/2
def sourceVariance : ℝ := sourceKernel 1 1-sourceKernel 1 0^2/(sourceKernel 0 0+sourceNoise)

theorem actual_source_normalized_kernel :
    1+sourceNoise⁻¹ • sourceKernel=!![(3 : ℝ),1;1,3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sourceKernel,sourceNoise]

theorem actual_source_determinant : (1+sourceNoise⁻¹ • sourceKernel).det=8 := by
  rw [actual_source_normalized_kernel]
  norm_num [Matrix.det_fin_two]

theorem actual_source_variance_and_factors : sourceVariance=5/6 ∧
    1+sourceKernel 0 0/sourceNoise=3 ∧ 1+sourceVariance/sourceNoise=8/3 ∧
    (1+sourceKernel 0 0/sourceNoise)*(1+sourceVariance/sourceNoise)=
      (1+sourceNoise⁻¹ • sourceKernel).det := by
  rw [actual_source_determinant]
  norm_num [sourceVariance,sourceKernel,sourceNoise]

theorem actual_source_log_nats_rounding :
    |(1/2 : ℝ)*Real.log ((1+sourceNoise⁻¹ • sourceKernel).det)-1.040|<0.0005 := by
  rw [actual_source_determinant]
  have hlog : Real.log (8 : ℝ)=3*Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 3
    norm_num at h
    simpa [mul_comm] using h
  rw [hlog,abs_lt]
  constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]

section FiniteFeatures
variable {sample feature : Type*} [Fintype sample] [Fintype feature]
  [DecidableEq sample] [DecidableEq feature]

def featureGram (Φ : Matrix sample feature ℝ) : Matrix feature feature ℝ := Φᵀ*Φ
def kernelGram (Φ : Matrix sample feature ℝ) : Matrix sample sample ℝ := Φ*Φᵀ
def featureCovariance (lambda : ℝ) (Φ : Matrix sample feature ℝ) : Matrix feature feature ℝ :=
  lambda • 1+featureGram Φ
def noisyKernel (lambda : ℝ) (Φ : Matrix sample feature ℝ) : Matrix sample sample ℝ :=
  lambda • 1+kernelGram Φ

theorem actual_regularized_feature_and_kernel_invertible (lambda : ℝ) (hlambda : 0<lambda)
    (Φ : Matrix sample feature ℝ) :
    (featureCovariance lambda Φ).PosDef ∧ IsUnit (featureCovariance lambda Φ).det ∧
    (noisyKernel lambda Φ).PosDef ∧ IsUnit (noisyKernel lambda Φ).det := by
  have hF := regularized_gram_strict_quad_and_invertible Φ lambda hlambda
  have hK := regularized_gram_strict_quad_and_invertible Φᵀ lambda hlambda
  refine ⟨hF.1,?_,?_,?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).mp hF.2.1
  · simpa [noisyKernel,kernelGram,Matrix.transpose_transpose] using hK.1
  · simpa [noisyKernel,kernelGram,Matrix.transpose_transpose] using
      (Matrix.isUnit_iff_isUnit_det _).mp hK.2.1

theorem actual_feature_kernel_pushthrough (lambda : ℝ) (Φ : Matrix sample feature ℝ) :
    featureCovariance lambda Φ*Φᵀ=Φᵀ*noisyKernel lambda Φ := by
  simp only [featureCovariance,featureGram,noisyKernel,kernelGram,Matrix.add_mul,
    Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one]
  rw [Matrix.mul_assoc]

theorem actual_feature_inverse_variance_identity (lambda : ℝ) (hlambda : 0<lambda)
    (Φ : Matrix sample feature ℝ) :
    (featureCovariance lambda Φ)⁻¹=
      lambda⁻¹ • (1-Φᵀ*(noisyKernel lambda Φ)⁻¹*Φ) := by
  have hInv := actual_regularized_feature_and_kernel_invertible lambda hlambda Φ
  have hF := Matrix.nonsing_inv_mul _ hInv.2.1
  have hK := Matrix.mul_nonsing_inv _ hInv.2.2.2
  have hprod : featureCovariance lambda Φ*(1-Φᵀ*(noisyKernel lambda Φ)⁻¹*Φ)=lambda • 1 := by
    rw [Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc,← Matrix.mul_assoc,
      actual_feature_kernel_pushthrough,Matrix.mul_assoc Φᵀ,Matrix.mul_assoc Φᵀ,
      hK,Matrix.one_mul]
    simp [featureCovariance,featureGram]
  have he := congrArg (fun M : Matrix feature feature ℝ =>
    (featureCovariance lambda Φ)⁻¹*M) hprod
  rw [← Matrix.mul_assoc,hF,Matrix.one_mul,Matrix.mul_smul,Matrix.mul_one] at he
  have he' := congrArg (fun M : Matrix feature feature ℝ => lambda⁻¹ • M) he
  simpa [smul_smul,inv_mul_cancel₀ hlambda.ne'] using he'.symm

def posteriorVariance (lambda : ℝ) (Φ : Matrix sample feature ℝ) (φ : feature → ℝ) : ℝ :=
  φ ⬝ᵥ φ-(Φ *ᵥ φ) ⬝ᵥ ((noisyKernel lambda Φ)⁻¹ *ᵥ (Φ *ᵥ φ))

theorem actual_posterior_variance_equals_feature_inverse (lambda : ℝ) (hlambda : 0<lambda)
    (Φ : Matrix sample feature ℝ) (φ : feature → ℝ) :
    φ ⬝ᵥ ((featureCovariance lambda Φ)⁻¹ *ᵥ φ)=posteriorVariance lambda Φ φ/lambda := by
  rw [actual_feature_inverse_variance_identity lambda hlambda Φ,Matrix.smul_mulVec,
    dotProduct_smul,Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub]
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,
    dotProduct_comm ((noisyKernel lambda Φ)⁻¹ *ᵥ (Φ *ᵥ φ))]
  simp [posteriorVariance,div_eq_mul_inv,mul_comm]

theorem actual_sylvester_normalized_feature_determinant (lambda : ℝ) (hlambda : 0<lambda)
    (Φ : Matrix sample feature ℝ) :
    (1+lambda⁻¹ • kernelGram Φ).det=
      (featureCovariance lambda Φ).det/lambda^(Fintype.card feature) := by
  have hSyl := actual_sylvester_determinant_identity (lambda⁻¹ • Φ) Φᵀ
  have hscale : featureCovariance lambda Φ=lambda • (1+lambda⁻¹ • featureGram Φ) := by
    simp [featureCovariance,smul_add,smul_smul,mul_inv_cancel₀ hlambda.ne']
  rw [hscale,Matrix.det_smul]
  have hPow : lambda^(Fintype.card feature)≠0 := pow_ne_zero _ hlambda.ne'
  rw [mul_div_cancel_left₀ _ hPow]
  simpa [kernelGram,featureGram,Matrix.smul_mul,Matrix.mul_smul] using hSyl

theorem actual_point_update_determinant_ratio (lambda : ℝ) (hlambda : 0<lambda)
    (Φ : Matrix sample feature ℝ) (φ : feature → ℝ) :
    (featureCovariance lambda Φ+Matrix.vecMulVec φ φ).det/(featureCovariance lambda Φ).det=
      1+posteriorVariance lambda Φ φ/lambda := by
  have hInv := actual_regularized_feature_and_kernel_invertible lambda hlambda Φ
  rw [actual_matrix_determinant_lemma _ hInv.2.1 φ φ,
    mul_div_cancel_left₀ _ (isUnit_iff_ne_zero.mp hInv.2.1),
    actual_posterior_variance_equals_feature_inverse lambda hlambda Φ φ]

end FiniteFeatures

end SafeLearning.CompleteFoundationsSequentialLogDet
