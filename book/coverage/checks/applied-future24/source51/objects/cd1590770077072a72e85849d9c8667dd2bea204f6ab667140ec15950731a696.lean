import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesRKHSStructure

variable {H G X I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [RKHS ℝ H X ℝ]

def evaluationFunctional (x : X) : H →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj x).comp (RKHS.coeCLM ℝ)

theorem evaluation_functional_evaluates (function : H) (x : X) :
    evaluationFunctional x function=function x := rfl

theorem evaluation_functional_is_linear (first second : H) (scalar : ℝ) (x : X) :
    evaluationFunctional x (first+scalar • second)=first x+scalar*second x := by
  simp [evaluationFunctional]

theorem evaluation_functional_is_bounded (function : H) (x : X) :
    |evaluationFunctional x function|≤‖function‖*
      Real.sqrt (inner ℝ (RKHS.kerFun H x 1) (RKHS.kerFun H x 1)) := by
  have hr : inner ℝ function (RKHS.kerFun H x 1)=function x := by simp
  rw [evaluation_functional_evaluates,← hr,real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm _ _

theorem rkhs_with_same_kernel_unique [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [CompleteSpace G] [RKHS ℝ G X ℝ] (hkernel : RKHS.kernel H=RKHS.kernel G) :
    ∃ isometry : H ≃ₗᵢ[ℝ] G, ∀ function : H, ∀ x : X, (isometry function) x=function x := by
  refine ⟨RKHS.equiv hkernel,?_⟩
  intro function x
  exact congrFun (RKHS.coe_equiv hkernel function) x

theorem finite_expansion_cross_inner [Fintype I] [Fintype J]
    (firstInput : I → X) (secondInput : J → X) (firstWeight : I → ℝ) (secondWeight : J → ℝ) :
    inner ℝ (∑ i, firstWeight i • RKHS.kerFun H (firstInput i) 1)
      (∑ j, secondWeight j • RKHS.kerFun H (secondInput j) 1) =
      ∑ i, ∑ j, firstWeight i*secondWeight j*(RKHS.kernel H (firstInput i) (secondInput j)) 1 := by
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hinner : inner ℝ (RKHS.kerFun H (firstInput i) 1)
      (RKHS.kerFun H (secondInput j) 1) =
      (RKHS.kernel H (firstInput i) (secondInput j)) 1 := by
    rw [real_inner_comm]
    simp
  rw [hinner]
  ring

@[instance_reducible]
def linearRKHS : RKHS ℝ ℝ ℝ ℝ where
  coeCLM := ContinuousLinearMap.pi (fun x : ℝ => x • ContinuousLinearMap.id ℝ ℝ)
  coeCLM_injective := by
    intro first second he
    have h := congrFun he 1
    simpa using h

def linearFunction (coefficient : ℝ) (input : ℝ) : ℝ :=
  letI : RKHS ℝ ℝ ℝ ℝ := linearRKHS
  (RKHS.coeCLM ℝ) coefficient input

theorem linear_function_evaluation (coefficient input : ℝ) :
    linearFunction coefficient input=coefficient*input := by
  change input*coefficient=coefficient*input
  exact mul_comm _ _

theorem linear_function_norm_and_evaluation (coefficient : ℝ) :
    ‖coefficient‖=|coefficient| ∧ |linearFunction coefficient 2|=2*‖coefficient‖ := by
  simp [linear_function_evaluation,Real.norm_eq_abs,abs_mul,mul_comm]

theorem linear_reproducing_property (coefficient input : ℝ) :
    inner ℝ coefficient input=linearFunction coefficient input := by
  simp [linear_function_evaluation,RCLike.inner_apply,conj_trivial,mul_comm]

theorem linear_representing_function (input query : ℝ) :
    linearFunction input query=input*query := linear_function_evaluation input query

end SafeLearning.CompleteModulesRKHSStructure
