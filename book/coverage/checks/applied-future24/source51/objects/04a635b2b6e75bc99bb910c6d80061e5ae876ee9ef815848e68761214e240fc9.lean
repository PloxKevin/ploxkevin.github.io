import SafeLearning.CompleteAppliedSequentialCalibrationJoint
import SafeLearning.CompleteAppliedGaussianAlarmQuantile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SafeLearning.CompleteAppliedCalibrationPrediction
open CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile
open CompleteAppliedGaussianGeneralIntegral CompleteAppliedGaussianTailIntegral
open CompleteAppliedGaussianAlarmQuantile

theorem actual_posterior_offset_and_independent_fresh_noise_give_the_predictive_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {offsetError freshNoise : Ω→ℝ}
    (hoffset : HasLaw offsetError (gaussianReal 0 (2/3)) P)
    (hnoise : HasLaw freshNoise (gaussianReal 0 1) P)
    (hindep : IndepFun offsetError freshNoise P) :
    HasLaw (fun omega=>offsetError omega+freshNoise omega) (gaussianReal 0 (5/3)) P ∧
      (∫omega,offsetError omega+freshNoise omega ∂P)=0 ∧
      Var[fun omega=>offsetError omega+freshNoise omega;P]=5/3 := by
  have hsum : HasLaw (fun omega=>offsetError omega+freshNoise omega)
      (gaussianReal 0 (5/3)) P := by
    refine ⟨hoffset.aemeasurable.add hnoise.aemeasurable,?_⟩
    have h := gaussianReal_add_gaussianReal_of_indepFun hindep hoffset hnoise
    norm_num at h
    exact h
  refine ⟨hsum,?_,?_⟩
  · rw [hsum.integral_eq,integral_id_gaussianReal]
  · rw [hsum.variance_eq,variance_id_gaussianReal];norm_num

theorem actual_zero_mean_gaussian_two_millimetre_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {error : Ω→ℝ} (variance : ℝ≥0) (hv : 0<variance)
    (hlaw : HasLaw error (gaussianReal 0 variance) P) :
    P.real {omega | |error omega|≤2}=2*standardCDF (2/Real.sqrt (variance:ℝ))-1 := by
  have hs : 0<Real.sqrt (variance:ℝ) := Real.sqrt_pos.mpr hv
  have hsq : (Real.sqrt (variance:ℝ))^2=(variance:ℝ) := Real.sq_sqrt variance.coe_nonneg
  have hz := gaussianReal_div_const hlaw (Real.sqrt (variance:ℝ))
  have he : variance/NNReal.mk ((Real.sqrt (variance:ℝ))^2) (sq_nonneg _)=1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_div,NNReal.coe_mk,NNReal.coe_one,hsq]
    exact div_self (ne_of_gt hv)
  rw [he] at hz
  norm_num at hz
  have hp := hz.measureReal_eq (p:=fun point:ℝ=>|point|≤2/Real.sqrt (variance:ℝ))
    (by measurability)
  have hset : {omega | |error omega/Real.sqrt (variance:ℝ)|≤2/Real.sqrt (variance:ℝ)}=
      {omega | |error omega|≤2} := by
    ext omega
    simp only [mem_setOf_eq,abs_div,abs_of_pos hs,div_le_div_iff_of_pos_right hs]
  rw [hset] at hp
  have hcompl := measureReal_compl (μ:=gaussianReal 0 1)
    (s:={point:ℝ | |point|≤2/Real.sqrt (variance:ℝ)}) (by measurability)
  have hcs : {point:ℝ | |point|≤2/Real.sqrt (variance:ℝ)}ᶜ=
      {point:ℝ | 2/Real.sqrt (variance:ℝ)< |point|} := by ext point;simp
  rw [hcs,actual_standard_gaussian_two_sided_tail_probability _ (by positivity)] at hcompl
  have hu : (gaussianReal 0 1).real univ=1 := by simp
  rw [hu] at hcompl
  rw [hp]
  linarith

theorem actual_offset_and_predictive_standardized_radii_have_certified_enclosures :
    (244948974/100000000:ℝ)<2/Real.sqrt (2/3) ∧
      2/Real.sqrt (2/3)<244948975/100000000 ∧
      (154919333/100000000:ℝ)<2/Real.sqrt (5/3) ∧
      2/Real.sqrt (5/3)<154919334/100000000 := by
  have hs₂ : (Real.sqrt (2/3:ℝ))^2=2/3 := Real.sq_sqrt (by norm_num)
  have hs₅ : (Real.sqrt (5/3:ℝ))^2=5/3 := Real.sq_sqrt (by norm_num)
  have hp₂ : 0<Real.sqrt (2/3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hp₅ : 0<Real.sqrt (5/3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · rw [lt_div_iff₀ hp₂];nlinarith
  constructor
  · rw [div_lt_iff₀ hp₂];nlinarith
  constructor
  · rw [lt_div_iff₀ hp₅];nlinarith
  · rw [div_lt_iff₀ hp₅];nlinarith

theorem actual_predictive_standard_gaussian_cdf_has_a_certified_rational_enclosure :
    (939330/1000000:ℝ)<standardCDF (2/Real.sqrt (5/3)) ∧
      standardCDF (2/Real.sqrt (5/3))<(9393325/10000000:ℝ) := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha := actual_gaussian_exponential_integral_uniform_rational_error
    (154919333/100000000:ℝ) (by constructor <;> norm_num)
  have hb := actual_gaussian_exponential_integral_uniform_rational_error
    (154919334/100000000:ℝ) (by constructor <;> norm_num)
  have hpa : (110124295013/100000000000:ℝ)<actualPolynomialIntegral
      (154919333/100000000:ℝ) ∧ actualPolynomialIntegral
      (154919333/100000000:ℝ)<110124295014/100000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have hpb : (110124295314/100000000000:ℝ)<actualPolynomialIntegral
      (154919334/100000000:ℝ) ∧ actualPolynomialIntegral
      (154919334/100000000:ℝ)<110124295315/100000000000 := by
    norm_num [actualPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  have hlo : (939330/1000000:ℝ)<standardCDF (154919333/100000000:ℝ) := by
    rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
    nlinarith
  have hhi : standardCDF (154919334/100000000:ℝ)<(9393325/10000000:ℝ) := by
    rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
    nlinarith
  have hr := actual_offset_and_predictive_standardized_radii_have_certified_enclosures
  have hm := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing
  exact ⟨hlo.trans (hm.2 hr.2.2.1),(hm.2 hr.2.2.2).trans hhi⟩

theorem actual_offset_standard_gaussian_cdf_has_a_certified_rational_enclosure :
    (992845/1000000:ℝ)<standardCDF (2/Real.sqrt (2/3)) ∧
      standardCDF (2/Real.sqrt (2/3))<(9928475/10000000:ℝ) := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha := actual_gaussian_exponential_tail_integral_uniform_rational_error
    (244948974/100000000:ℝ) (by constructor <;> norm_num)
  have hb := actual_gaussian_exponential_tail_integral_uniform_rational_error
    (244948975/100000000:ℝ) (by constructor <;> norm_num)
  have hpa : (123538437748/100000000000:ℝ)<actualTailPolynomialIntegral
      (244948974/100000000:ℝ) ∧ actualTailPolynomialIntegral
      (244948974/100000000:ℝ)<123538437749/100000000000 := by
    norm_num [actualTailPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have hpb : (123538437798/100000000000:ℝ)<actualTailPolynomialIntegral
      (244948975/100000000:ℝ) ∧ actualTailPolynomialIntegral
      (244948975/100000000:ℝ)<123538437799/100000000000 := by
    norm_num [actualTailPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  have hlo : (992845/1000000:ℝ)<standardCDF (244948974/100000000:ℝ) := by
    rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
    nlinarith
  have hhi : standardCDF (244948975/100000000:ℝ)<(9928475/10000000:ℝ) := by
    rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
    nlinarith
  have hr := actual_offset_and_predictive_standardized_radii_have_certified_enclosures
  have hm := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing
  exact ⟨hlo.trans (hm.2 hr.1),(hm.2 hr.2.1).trans hhi⟩

theorem actual_offset_and_predictive_two_millimetre_probability_roundings_and_requirement :
    |(2*standardCDF (2/Real.sqrt (2/3))-1)-(98569/100000:ℝ)|<1/200000 ∧
      (98/100:ℝ)<2*standardCDF (2/Real.sqrt (2/3))-1 ∧
      |(2*standardCDF (2/Real.sqrt (5/3))-1)-(87866/100000:ℝ)|<1/200000 ∧
      2*standardCDF (2/Real.sqrt (5/3))-1<(98/100:ℝ) := by
  have ho := actual_offset_standard_gaussian_cdf_has_a_certified_rational_enclosure
  have hp := actual_predictive_standard_gaussian_cdf_has_a_certified_rational_enclosure
  refine ⟨?_,?_,?_,?_⟩
  · rw [abs_lt];constructor <;> linarith
  · linarith
  · rw [abs_lt];constructor <;> linarith
  · linarith

end SafeLearning.CompleteAppliedCalibrationPrediction
