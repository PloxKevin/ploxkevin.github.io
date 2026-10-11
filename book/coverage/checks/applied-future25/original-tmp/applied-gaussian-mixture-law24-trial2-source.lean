import SafeLearning.CompleteAppliedFiniteMixtureMaterial24
import SafeLearning.CompleteAppliedGaussianStandardization

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace SafeLearning.CompleteAppliedGaussianMixtureLaw24
open CompleteAppliedFiniteMixtureMaterial24 CompleteAppliedGaussianCDF
  CompleteAppliedGaussianStandardization

def componentWeight (b : Bool) : ℝ≥0 := if b then 1/5 else 4/5

def componentLaw (b : Bool) : Measure ℝ :=
  if b then gaussianReal 0 9 else gaussianReal 0 (1/4)

def residualLaw : Measure ℝ := finiteMixture componentWeight componentLaw

def absoluteTail (μ : Measure ℝ) (r : ℝ) : ℝ := μ.real {x | r < |x|}

private theorem normalizedWeights : ∑ b, componentWeight b = 1 := by
  norm_num [componentWeight, Fintype.sum_bool]

private instance componentProbability (b : Bool) : IsProbabilityMeasure (componentLaw b) := by
  cases b <;> dsimp [componentLaw] <;> infer_instance

instance residualProbability : IsProbabilityMeasure residualLaw :=
  actual_finite_mixture_is_a_probability_law componentWeight normalizedWeights componentLaw

theorem actual_source_residual_has_finite_second_moment : MemLp id 2 residualLaw :=
  actual_finite_mixture_has_finite_second_moment componentWeight componentLaw id
    (fun b => by cases b <;> exact memLp_id_gaussianReal 2)

theorem actual_source_residual_mean_and_variance :
    (∫ x, x ∂residualLaw) = 0 ∧ variance id residualLaw = 2 := by
  have hm := actual_finite_mixture_mean componentWeight componentLaw id
    (fun b => by cases b <;> exact memLp_id_gaussianReal 2)
  have hv := actual_finite_mixture_variance componentWeight normalizedWeights componentLaw id
    (fun b => by cases b <;> exact memLp_id_gaussianReal 2)
  change (∫ x, x ∂finiteMixture componentWeight componentLaw) = 0 ∧
    variance id (finiteMixture componentWeight componentLaw) = 2
  norm_num [Fintype.sum_bool, componentLaw, componentWeight,
    integral_id_gaussianReal, variance_id_gaussianReal] at hm hv
  exact ⟨hm, hv⟩

theorem actual_source_residual_tail_is_the_weighted_component_tail (r : ℝ) :
    absoluteTail residualLaw r =
      (4/5:ℝ)*absoluteTail (gaussianReal 0 (1/4)) r +
      (1/5:ℝ)*absoluteTail (gaussianReal 0 9) r := by
  simp only [absoluteTail, residualLaw, finiteMixture, Fintype.sum_bool]
  rw [measureReal_add_apply]
  simp [componentWeight, componentLaw]
  ring

theorem actual_standard_gaussian_absolute_tail (r : ℝ) (hr : 0 ≤ r) :
    absoluteTail (gaussianReal 0 1) r = 2*(1-standardCDF r) := by
  let μ := gaussianReal 0 1
  haveI : NullSingletonClass μ := nullSingletonClass_gaussianReal (by norm_num)
  have hset : Iic r \ Iio (-r) = Icc (-r) r := by ext x; simp
  have hd := measureReal_sdiff (μ:=μ) (s₁:=Iic r) (s₂:=Iio (-r))
    (by intro x hx; change x < -r at hx; change x ≤ r; linarith) measurableSet_Iio
  rw [hset, measureReal_congr (Iio_ae_eq_Iic (μ:=μ))] at hd
  change μ.real (Icc (-r) r) = standardCDF r - standardCDF (-r) at hd
  rw [actual_standard_gaussian_cdf_reflection] at hd
  have hc := measureReal_compl (μ:=μ) (s:=Icc (-r) r) measurableSet_Icc
  have he : (Icc (-r) r)ᶜ = {x : ℝ | r < |x|} := by
    ext x; simp only [mem_compl_iff, mem_Icc, mem_setOf_eq]
    rw [← not_le, abs_le]
  rw [he] at hc
  change absoluteTail μ r = _
  have hu : μ.real univ = 1 := by simp [μ]
  rw [hu] at hc
  linarith

theorem actual_positive_scaled_gaussian_tail (s r : ℝ) (hs : 0 < s) (hr : 0 ≤ r) :
    absoluteTail (gaussianReal 0 (⟨s^2, sq_nonneg s⟩)) r =
      2*(1-standardCDF (r/s)) := by
  have hm := gaussianReal_map_const_mul (μ:=0) (v:=1) s
  simp only [mul_zero, mul_one] at hm
  have he : (fun x : ℝ => s*x) ⁻¹' {x | r < |x|} = {x | r/s < |x|} := by
    ext x; simp only [mem_preimage, mem_setOf_eq, abs_mul, abs_of_pos hs]
    rw [div_lt_iff₀ hs]; rw [mul_comm]
  have hp := map_measureReal_apply (μ:=gaussianReal 0 1)
    (by fun_prop : Measurable (fun x : ℝ => s*x))
    (s:={x | r < |x|}) (measurableSet_lt measurable_const measurable_abs)
  rw [hm, he] at hp
  change absoluteTail (gaussianReal 0 ⟨s^2, sq_nonneg s⟩) r =
    absoluteTail (gaussianReal 0 1) (r/s) at hp
  rw [hp, actual_standard_gaussian_absolute_tail _ (div_nonneg hr hs.le)]

theorem actual_printed_source_tail_formulas :
    absoluteTail residualLaw 5 = (4/5:ℝ)*2*(1-standardCDF 10) +
      (1/5:ℝ)*2*(1-standardCDF (5/3)) ∧
    absoluteTail residualLaw 1 = (4/5:ℝ)*2*(1-standardCDF 2) +
      (1/5:ℝ)*2*(1-standardCDF (1/3)) := by
  have hsmall (r : ℝ) (hr : 0 ≤ r) := actual_positive_scaled_gaussian_tail (1/2) r (by norm_num) hr
  have hlarge (r : ℝ) (hr : 0 ≤ r) := actual_positive_scaled_gaussian_tail 3 r (by norm_num) hr
  have hvs : (⟨(1/2:ℝ)^2, sq_nonneg (1/2:ℝ)⟩ : ℝ≥0) = 1/4 := by ext; norm_num [NNReal.coe_div, NNReal.coe_ofNat]
  have hvl : (⟨(3:ℝ)^2, sq_nonneg (3:ℝ)⟩ : ℝ≥0) = 9 := by ext; norm_num [NNReal.coe_div, NNReal.coe_ofNat]
  constructor <;> rw [actual_source_residual_tail_is_the_weighted_component_tail]
  · have a := hsmall 5 (by norm_num); have b := hlarge 5 (by norm_num)
    rw [hvs] at a; rw [hvl] at b; rw [a,b]; norm_num; ring
  · have a := hsmall 1 (by norm_num); have b := hlarge 1 (by norm_num)
    rw [hvs] at a; rw [hvl] at b; rw [a,b]; norm_num; ring

end SafeLearning.CompleteAppliedGaussianMixtureLaw24
