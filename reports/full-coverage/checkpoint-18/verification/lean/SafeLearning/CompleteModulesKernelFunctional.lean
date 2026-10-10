import SafeLearning.CompleteModulesMatrixGP
import SafeLearning.CompleteModulesRKHSStructure

set_option autoImplicit false
noncomputable section
open Matrix Filter Asymptotics
open scoped BigOperators Topology Matrix.Norms.Operator
namespace SafeLearning.CompleteModulesKernelFunctional

open CompleteModulesMatrixGP CompleteModulesRKHSStructure

theorem actual_linear_kernel_section (input : ℝ) :
    letI : RKHS ℝ ℝ ℝ ℝ := linearRKHS
    RKHS.kerFun ℝ input 1=input := by
  letI : RKHS ℝ ℝ ℝ ℝ := linearRKHS
  have h := RKHS.inner_kerFun (𝕜:=ℝ) (H:=ℝ) input 1 (1:ℝ)
  simp only [RCLike.inner_apply,conj_trivial,mul_one,one_mul] at h
  have heval : (1:ℝ) input=input := by
    change input*1=input
    ring
  exact h.trans heval

theorem actual_linear_kernel_formula (input query : ℝ) :
    letI : RKHS ℝ ℝ ℝ ℝ := linearRKHS
    (RKHS.kernel ℝ input query) 1=input*query := by
  letI : RKHS ℝ ℝ ℝ ℝ := linearRKHS
  rw [RKHS.kernel_apply]
  change (RKHS.kerFun ℝ input).adjoint (RKHS.kerFun ℝ query 1)=input*query
  rw [actual_linear_kernel_section,RKHS.adjoint_kerFun]
  change (RKHS.coeCLM ℝ) query input=input*query
  change input*query=input*query
  rfl

variable {I : Type*} [Fintype I] [DecidableEq I]

def posteriorFunctional (query labels : I → ℝ) : Matrix I I ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun matrix => query ⬝ᵥ (matrix *ᵥ labels)
    map_add' := by intro first second; simp [Matrix.add_mulVec,dotProduct_add]
    map_smul' := by intro scalar matrix; simp [Matrix.smul_mulVec,dotProduct_smul] }

theorem posterior_functional_evaluates (query labels : I → ℝ) (matrix : Matrix I I ℝ) :
    posteriorFunctional query labels matrix=query ⬝ᵥ (matrix *ᵥ labels) := rfl

theorem posterior_mean_second_order_remainder (gram : Matrix I I ℝ) (query labels : I → ℝ) :
    (fun regularizer : ℝ => posteriorMean gram query labels regularizer-
      regularizer⁻¹*(query ⬝ᵥ labels)+(regularizer⁻¹)^2*(query ⬝ᵥ (gram *ᵥ labels))) =O[atTop]
      (fun regularizer : ℝ => (regularizer⁻¹)^3) := by
  have hb := inverse_infinite_regularization_second_order_remainder gram
  have hl := (posteriorFunctional query labels).isBigO_comp
    (fun regularizer : ℝ => (ridgeMatrix gram regularizer)⁻¹-
      regularizer⁻¹ • (1 : Matrix I I ℝ)+(regularizer⁻¹)^2 • gram) atTop
  have hm := hl.trans hb
  convert hm using 1
  funext regularizer
  change posteriorMean gram query labels regularizer-regularizer⁻¹*(query ⬝ᵥ labels)+
    (regularizer⁻¹)^2*(query ⬝ᵥ (gram *ᵥ labels))=
    query ⬝ᵥ (((ridgeMatrix gram regularizer)⁻¹-regularizer⁻¹ • (1 : Matrix I I ℝ)+
    (regularizer⁻¹)^2 • gram) *ᵥ labels)
  simp [posteriorMean,Matrix.add_mulVec,Matrix.sub_mulVec,
    Matrix.smul_mulVec,dotProduct_add,dotProduct_sub,dotProduct_smul,smul_eq_mul]

theorem inverse_cube_isBigO_inverse_square :
    (fun regularizer : ℝ => (regularizer⁻¹)^3) =O[atTop]
      (fun regularizer : ℝ => (regularizer⁻¹)^2) := by
  apply isBigO_iff.mpr
  refine ⟨1,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with regularizer hge
  have hpos : 0<regularizer := lt_of_lt_of_le zero_lt_one hge
  have hnonneg : 0≤regularizer⁻¹ := inv_nonneg.mpr hpos.le
  have hle : regularizer⁻¹≤1 := (inv_le_one₀ hpos).mpr hge
  simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hnonneg _),one_mul]
  nlinarith [sq_nonneg (regularizer⁻¹),mul_nonneg (sq_nonneg (regularizer⁻¹)) (sub_nonneg.mpr hle)]

theorem posterior_mean_leading_term (gram : Matrix I I ℝ) (query labels : I → ℝ) :
    (fun regularizer : ℝ => posteriorMean gram query labels regularizer-
      regularizer⁻¹*(query ⬝ᵥ labels)) =O[atTop]
      (fun regularizer : ℝ => (regularizer⁻¹)^2) := by
  have hrem := (posterior_mean_second_order_remainder gram query labels).trans
    inverse_cube_isBigO_inverse_square
  have hterm := (isBigO_refl (fun regularizer : ℝ => (regularizer⁻¹)^2) atTop).const_mul_left (query ⬝ᵥ (gram *ᵥ labels))
  have h := hrem.sub hterm
  convert h using 1
  funext regularizer
  ring

theorem posterior_variance_second_order_remainder (gram : Matrix I I ℝ)
    (query : I → ℝ) (queryDiagonal : ℝ) :
    (fun regularizer : ℝ => posteriorVariance gram query queryDiagonal regularizer-
      queryDiagonal+regularizer⁻¹*(query ⬝ᵥ query)-
      (regularizer⁻¹)^2*(query ⬝ᵥ (gram *ᵥ query))) =O[atTop]
      (fun regularizer : ℝ => (regularizer⁻¹)^3) := by
  have h := (posterior_mean_second_order_remainder gram query query).neg_left
  convert h using 1
  funext regularizer
  simp only [posteriorVariance,posteriorMean]
  ring

end SafeLearning.CompleteModulesKernelFunctional
