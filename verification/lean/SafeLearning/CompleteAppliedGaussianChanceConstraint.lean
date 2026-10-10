import SafeLearning.CompleteAppliedGaussianQuantile

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace SafeLearning.CompleteAppliedGaussianChanceConstraint
open CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile

theorem actual_joint_gaussian_source_projection_has_derived_mean_variance_and_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω→ℝ}
    (hjoint : HasGaussianLaw (fun omega=>(X omega,Y omega)) P)
    (hmeanX : (∫omega,X omega ∂P)=1) (hmeanY : (∫omega,Y omega ∂P)=2)
    (hvarX : Var[X;P]=1) (hvarY : Var[Y;P]=4)
    (hcov : covariance X Y P=1/2) :
    (∫omega,X omega+Y omega ∂P)=3 ∧ Var[fun omega=>X omega+Y omega;P]=6 ∧
      HasLaw (fun omega=>X omega+Y omega) (gaussianReal 3 6) P := by
  haveI : IsProbabilityMeasure P := hjoint.isProbabilityMeasure
  have hx := hjoint.fst
  have hy := hjoint.snd
  have hm : (∫omega,X omega+Y omega ∂P)=3 := by
    rw [integral_add hx.integrable hy.integrable,hmeanX,hmeanY];norm_num
  have hv : Var[fun omega=>X omega+Y omega;P]=6 := by
    rw [variance_fun_add hx.memLp_two hy.memLp_two,hvarX,hvarY,hcov];norm_num
  refine ⟨hm,hv,?_⟩
  refine ⟨hjoint.fun_add.aemeasurable,?_⟩
  rw [hjoint.fun_add.map_eq_gaussianReal,hm,hv]
  norm_num

theorem actual_nondegenerate_gaussian_cdf_is_the_standardized_true_cdf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω→ℝ}
    (mean : ℝ) (variance : ℝ≥0) (hvariance : 0<variance)
    (hlaw : HasLaw Z (gaussianReal mean variance) P) (threshold : ℝ) :
    P.real {omega | Z omega≤threshold}=
      standardCDF ((threshold-mean)/Real.sqrt (variance:ℝ)) := by
  have hs : 0<Real.sqrt (variance:ℝ) := Real.sqrt_pos.mpr hvariance
  have hsq : (Real.sqrt (variance:ℝ))^2=(variance:ℝ) := Real.sq_sqrt variance.coe_nonneg
  have hz := gaussianReal_div_const (gaussianReal_sub_const hlaw mean)
    (Real.sqrt (variance:ℝ))
  have hv : variance/NNReal.mk ((Real.sqrt (variance:ℝ))^2) (sq_nonneg _)=1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_div,NNReal.coe_mk,NNReal.coe_one,hsq]
    exact div_self (ne_of_gt hvariance)
  rw [hv] at hz
  have hm : (mean-mean)/Real.sqrt (variance:ℝ)=0 := by simp
  rw [hm] at hz
  have hp := hz.measureReal_eq (p:=fun point : ℝ=>point≤(threshold-mean)/Real.sqrt (variance:ℝ))
    measurableSet_Iic
  have he : {omega | (Z omega-mean)/Real.sqrt (variance:ℝ)≤(threshold-mean)/Real.sqrt (variance:ℝ)}=
      {omega | Z omega≤threshold} := by
    ext omega
    simp only [mem_setOf_eq,div_le_div_iff_of_pos_right hs]
    exact sub_le_sub_iff_right mean
  rw [he] at hp
  exact hp

theorem actual_gaussian_point_ninety_five_constraint_has_the_true_smallest_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω→ℝ}
    (mean : ℝ) (variance : ℝ≥0) (hvariance : 0<variance)
    (hlaw : HasLaw Z (gaussianReal mean variance) P) :
    (∀threshold:ℝ,(95/100:ℝ)≤P.real {omega | Z omega≤threshold} ↔
      mean+Real.sqrt (variance:ℝ)*truePointNinetyFiveQuantile≤threshold) ∧
    IsLeast {threshold:ℝ | (95/100:ℝ)≤P.real {omega | Z omega≤threshold}}
      (mean+Real.sqrt (variance:ℝ)*truePointNinetyFiveQuantile) := by
  have hq := actual_point_ninety_five_quantile_is_the_unique_cdf_root_and_smallest_threshold
  have hs : 0<Real.sqrt (variance:ℝ) := Real.sqrt_pos.mpr hvariance
  have he (threshold:ℝ) : (95/100:ℝ)≤P.real {omega | Z omega≤threshold} ↔
      mean+Real.sqrt (variance:ℝ)*truePointNinetyFiveQuantile≤threshold := by
    rw [actual_nondegenerate_gaussian_cdf_is_the_standardized_true_cdf mean variance hvariance hlaw,
      hq.2.1,le_div_iff₀ hs]
    constructor <;> intro h <;> nlinarith
  refine ⟨he,?_,?_⟩
  · exact (he _).mpr le_rfl
  · intro threshold ht;exact (he threshold).mp ht

theorem actual_source_threshold_true_rounding_and_rounded_input_proxy_distinction :
    (702905/100000:ℝ)<3+Real.sqrt 6*truePointNinetyFiveQuantile ∧
      3+Real.sqrt 6*truePointNinetyFiveQuantile<(702915/100000:ℝ) ∧
      |(3+Real.sqrt 6*truePointNinetyFiveQuantile)-(70291/10000:ℝ)|<1/20000 ∧
      |(3+(164485/100000:ℝ)*Real.sqrt 6)-(70290/10000:ℝ)|<1/20000 ∧
      3+(164485/100000:ℝ)*Real.sqrt 6<3+Real.sqrt 6*truePointNinetyFiveQuantile := by
  have hr := actual_point_ninety_five_quantile_is_the_unique_cdf_root_and_smallest_threshold
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
  have hp := Real.sqrt_nonneg (6:ℝ)
  have hslo : (2449489742/1000000000:ℝ)<Real.sqrt 6 := by nlinarith
  have hshi : Real.sqrt 6<(2449489743/1000000000:ℝ) := by nlinarith
  have hlo : (702905/100000:ℝ)<3+Real.sqrt 6*truePointNinetyFiveQuantile := by
    nlinarith [hr.2.2.1,hr.2.2.2]
  have hhi : 3+Real.sqrt 6*truePointNinetyFiveQuantile<(702915/100000:ℝ) := by
    nlinarith [hr.2.2.1,hr.2.2.2]
  refine ⟨hlo,hhi,?_,?_,?_⟩
  · rw [abs_lt];constructor <;> linarith
  · rw [abs_lt];constructor <;> nlinarith
  · have hq := actual_supplied_five_decimal_quantile_is_a_rounding_and_not_the_exact_root
    nlinarith [hq.2.1]

end SafeLearning.CompleteAppliedGaussianChanceConstraint
