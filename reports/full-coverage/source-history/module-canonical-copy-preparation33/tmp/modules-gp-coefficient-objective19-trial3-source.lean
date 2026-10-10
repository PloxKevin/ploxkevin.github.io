import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPCoefficientObjective
variable {I : Type*} [Fintype I] [DecidableEq I]

def objective (K : Matrix I I ℝ) (y : I → ℝ) (lambda : ℝ) (alpha : I → ℝ) : ℝ :=
  (y-K*ᵥalpha) ⬝ᵥ (y-K*ᵥalpha)+lambda*(alpha ⬝ᵥ (K*ᵥalpha))
def rowCLM (K : Matrix I I ℝ) (i : I) : (I → ℝ) →L[ℝ] ℝ :=
  ∑ j,K i j • ContinuousLinearMap.proj j
def quadraticDerivative (K : Matrix I I ℝ) (alpha : I → ℝ) : (I → ℝ) →L[ℝ] ℝ :=
  ∑ i,((K*ᵥalpha) i • ContinuousLinearMap.proj i+alpha i • rowCLM K i)
def objectiveDerivative (K : Matrix I I ℝ) (y : I → ℝ) (lambda : ℝ)
    (alpha : I → ℝ) : (I → ℝ) →L[ℝ] ℝ :=
  (∑ i,(2*(y i-(K*ᵥalpha) i)) • (-rowCLM K i))+lambda • quadraticDerivative K alpha

theorem actual_row_linear_map_is_the_true_matrix_action (K : Matrix I I ℝ) (i : I) (x : I → ℝ) :
    rowCLM K i x=(K*ᵥx) i := by simp [rowCLM,Matrix.mulVec,dotProduct]

theorem actual_symmetric_gram_coefficient_objective_has_the_printed_expansion
    (K : Matrix I I ℝ) (y alpha : I → ℝ) (lambda : ℝ) (hK : Kᵀ=K) :
    objective K y lambda alpha=y ⬝ᵥ y-2*(alpha ⬝ᵥ (K*ᵥy))+
      alpha ⬝ᵥ ((K*(K+lambda • (1 : Matrix I I ℝ)))*ᵥalpha) := by
  have hcross : y ⬝ᵥ (K*ᵥalpha)=alpha ⬝ᵥ (K*ᵥy) := by
    rw [dotProduct_mulVec,← mulVec_transpose,hK,dotProduct_comm]
  have hquad : (K*ᵥalpha) ⬝ᵥ (K*ᵥalpha)=alpha ⬝ᵥ ((K*K)*ᵥalpha) := by
    rw [dotProduct_mulVec,← mulVec_transpose,hK,Matrix.mulVec_mulVec,dotProduct_comm]
  simp only [objective,sub_dotProduct,dotProduct_sub,Matrix.mul_add,
    Matrix.mul_smul,Matrix.mul_one,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
    dotProduct_smul,smul_eq_mul,hcross,hquad]
  rw [dotProduct_comm (K*ᵥalpha) y,hcross]
  ring

theorem actual_quadratic_matrix_expression_has_its_true_frechet_derivative
    (K : Matrix I I ℝ) (alpha : I → ℝ) :
    HasFDerivAt (fun x : I → ℝ => x ⬝ᵥ (K*ᵥx)) (quadraticDerivative K alpha) alpha := by
  have h : ∀ i,HasFDerivAt (fun x : I → ℝ => x i*(rowCLM K i x))
      ((K*ᵥalpha) i • ContinuousLinearMap.proj i+alpha i • rowCLM K i) alpha := by
    intro i
    have hp : HasFDerivAt (fun x : I → ℝ => x i) (ContinuousLinearMap.proj i) alpha :=
      (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ).hasFDerivAt
    simpa only [actual_row_linear_map_is_the_true_matrix_action] using hp.mul (rowCLM K i).hasFDerivAt
  simpa only [dotProduct,actual_row_linear_map_is_the_true_matrix_action,quadraticDerivative] using
    HasFDerivAt.fun_sum (fun i (_ : i∈Finset.univ) => h i)

theorem actual_coefficient_objective_has_its_true_frechet_derivative
    (K : Matrix I I ℝ) (y alpha : I → ℝ) (lambda : ℝ) :
    HasFDerivAt (objective K y lambda) (objectiveDerivative K y lambda alpha) alpha := by
  have h : ∀ i,HasFDerivAt (fun x : I → ℝ => (y i-(K*ᵥx) i)^2)
      ((2*(y i-(K*ᵥalpha) i)) • (-rowCLM K i)) alpha := by
    intro i
    convert ((hasFDerivAt_const (y i) alpha).sub (rowCLM K i).hasFDerivAt).pow 2 using 1 <;>
      simp [actual_row_linear_map_is_the_true_matrix_action]
  have hs := HasFDerivAt.fun_sum (fun i (_ : i∈Finset.univ) => h i)
  have hp := (actual_quadratic_matrix_expression_has_its_true_frechet_derivative K alpha).const_mul lambda
  convert hs.add hp using 1
  · funext x
    simp only [objective,dotProduct,Pi.sub_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rfl

theorem actual_symmetric_quadratic_derivative_is_twice_the_matrix_gradient_dot_direction
    (K : Matrix I I ℝ) (alpha d : I → ℝ) (hK : Kᵀ=K) :
    quadraticDerivative K alpha d=2*(alpha ⬝ᵥ (K*ᵥd)) := by
  have hcross : (K*ᵥalpha) ⬝ᵥ d=alpha ⬝ᵥ (K*ᵥd) := by
    rw [dotProduct_comm,dotProduct_mulVec,← mulVec_transpose,hK,dotProduct_comm]
  simp only [quadraticDerivative,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
    actual_row_linear_map_is_the_true_matrix_action,Finset.sum_add_distrib]
  change (K*ᵥalpha) ⬝ᵥ d+alpha ⬝ᵥ (K*ᵥd)=_
  rw [hcross]
  ring

theorem actual_coefficient_frechet_derivative_is_the_printed_stationarity_expression
    (K : Matrix I I ℝ) (y alpha d : I → ℝ) (lambda : ℝ) (hK : Kᵀ=K) :
    objectiveDerivative K y lambda alpha d=
      2*((K*ᵥ((K+lambda • (1 : Matrix I I ℝ))*ᵥalpha-y)) ⬝ᵥ d) := by
  have hcross : (K*ᵥalpha) ⬝ᵥ d=alpha ⬝ᵥ (K*ᵥd) := by
    rw [dotProduct_comm,dotProduct_mulVec,← mulVec_transpose,hK,dotProduct_comm]
  have hcross2 : (K*ᵥ(y-K*ᵥalpha)) ⬝ᵥ d=(y-K*ᵥalpha) ⬝ᵥ (K*ᵥd) := by
    rw [dotProduct_comm,dotProduct_mulVec,← mulVec_transpose,hK,dotProduct_comm]
  simp only [objectiveDerivative,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,smul_eq_mul,
    actual_row_linear_map_is_the_true_matrix_action,
    actual_symmetric_quadratic_derivative_is_twice_the_matrix_gradient_dot_direction K alpha d hK]
  have hs : (∑ i,2*(y i-(K*ᵥalpha) i)*(-(K*ᵥd) i))=
      -2*((y-K*ᵥalpha) ⬝ᵥ (K*ᵥd)) := by
    simp only [dotProduct,Pi.sub_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs,← hcross2,← hcross]
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.mulVec_sub,
    Matrix.mulVec_add,Matrix.mulVec_smul,sub_dotProduct,add_dotProduct,smul_dotProduct,smul_eq_mul]
  ring

theorem actual_frechet_stationarity_iff_the_printed_matrix_equation
    (K : Matrix I I ℝ) (y alpha : I → ℝ) (lambda : ℝ) (hK : Kᵀ=K) :
    objectiveDerivative K y lambda alpha=0 ↔
      K*ᵥ((K+lambda • (1 : Matrix I I ℝ))*ᵥalpha-y)=0 := by
  constructor
  · intro hz
    ext i
    have h := congrArg (fun L : (I → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hz
    rw [actual_coefficient_frechet_derivative_is_the_printed_stationarity_expression K y alpha
      (Pi.single i 1) lambda hK] at h
    simp only [dotProduct_single_one,ContinuousLinearMap.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · intro hz
    ext d
    rw [actual_coefficient_frechet_derivative_is_the_printed_stationarity_expression K y alpha d lambda hK,hz]
    simp

theorem actual_inverse_ridge_coefficients_satisfy_the_literal_stationarity_equation
    (K : Matrix I I ℝ) (y : I → ℝ) (lambda : ℝ)
    (hunit : IsUnit (K+lambda • (1 : Matrix I I ℝ))) :
    K*ᵥ((K+lambda • (1 : Matrix I I ℝ))*ᵥ
      ((K+lambda • (1 : Matrix I I ℝ))⁻¹*ᵥy)-y)=0 := by
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    ((K+lambda • (1 : Matrix I I ℝ)).isUnit_iff_isUnit_det.mp hunit),Matrix.one_mulVec]
  simp

theorem actual_psd_gram_times_its_ridge_matrix_is_positive_semidefinite
    (K : Matrix I I ℝ) (lambda : ℝ) (hK : K.PosSemidef) (hlambda : 0≤lambda) :
    (K*(K+lambda • (1 : Matrix I I ℝ))).PosSemidef := by
  have hh : Kᴴ=K := hK.isHermitian.eq
  have hs : (K*K).PosSemidef := by simpa only [hh] using posSemidef_conjTranspose_mul_self K
  simpa only [Matrix.mul_add,Matrix.mul_smul,Matrix.mul_one] using hs.add (hK.smul hlambda)

theorem actual_coefficient_objective_jensen_gap_is_the_true_psd_quadratic
    (K : Matrix I I ℝ) (y x z : I → ℝ) (lambda a b : ℝ)
    (hK : Kᵀ=K) (hab : a+b=1) :
    a*objective K y lambda x+b*objective K y lambda z-
        objective K y lambda (a • x+b • z)=
      a*b*((x-z) ⬝ᵥ ((K*(K+lambda • (1 : Matrix I I ℝ)))*ᵥ(x-z))) := by
  simp only [actual_symmetric_gram_coefficient_objective_has_the_printed_expansion K y _ lambda hK,
    add_dotProduct,smul_dotProduct,dotProduct_add,dotProduct_smul,Matrix.mulVec_add,
    Matrix.mulVec_smul,Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub,smul_eq_mul]
  have hb : b=1-a := by linarith
  rw [hb]
  ring

theorem actual_psd_gram_coefficient_objective_is_genuinely_convex
    (K : Matrix I I ℝ) (y : I → ℝ) (lambda : ℝ)
    (hK : K.PosSemidef) (hlambda : 0≤lambda) :
    ConvexOn ℝ Set.univ (objective K y lambda) := by
  have hs : Kᵀ=K := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  refine ⟨convex_univ,?_⟩
  intro x _ z _ a b ha hb hab
  have hgap := actual_coefficient_objective_jensen_gap_is_the_true_psd_quadratic K y x z lambda a b hs hab
  have hH := actual_psd_gram_times_its_ridge_matrix_is_positive_semidefinite K lambda hK hlambda
  have hnonnegative : 0≤(x-z) ⬝ᵥ ((K*(K+lambda • (1 : Matrix I I ℝ)))*ᵥ(x-z)) := by
    simpa only [star_trivial] using hH.dotProduct_mulVec_nonneg (x-z)
  have hprod := mul_nonneg (mul_nonneg ha hb) hnonnegative
  simpa only [smul_eq_mul] using (show objective K y lambda (a • x+b • z)≤
    a*objective K y lambda x+b*objective K y lambda z by linarith)

end SafeLearning.CompleteModulesGPCoefficientObjective
