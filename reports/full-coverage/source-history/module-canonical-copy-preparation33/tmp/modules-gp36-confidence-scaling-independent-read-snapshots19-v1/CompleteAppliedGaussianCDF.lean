import SafeLearning.CompleteAppliedGaussianIntegralBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SafeLearning.CompleteAppliedGaussianCDF
open CompleteAppliedGaussianIntegralBounds

def standardCDF (x : ℝ) : ℝ := (gaussianReal 0 1).real (Iic x)

theorem actual_standard_gaussian_cdf_is_its_density_integral (x : ℝ) :
    standardCDF x=∫y in Iic x,gaussianPDFReal 0 1 y := by
  rw [standardCDF,measureReal_def,gaussianReal_apply_eq_integral 0 (by norm_num),
    ENNReal.toReal_ofReal]
  exact integral_nonneg (fun y=>gaussianPDFReal_nonneg _ _ _)

theorem actual_standard_gaussian_symmetry_and_half_mass :
    standardCDF 0=1/2 := by
  let μ := gaussianReal 0 1
  haveI : NullSingletonClass μ := nullSingletonClass_gaussianReal (by norm_num)
  have hm : μ.map (fun x : ℝ=>-x)=μ := by
    simpa [μ] using (gaussianReal_map_neg (μ:=0) (v:=1))
  have hp : (fun x : ℝ=>-x) ⁻¹' Iic (0:ℝ)=Ici 0 := by
    ext x;simp
  have hsym := map_measureReal_apply (μ:=μ)
    (by fun_prop : Measurable (fun x : ℝ=>-x)) (s:=Iic 0) measurableSet_Iic
  rw [hm,hp] at hsym
  have htotal := measureReal_union_add_inter (μ:=μ) (s:=Iic 0) (t:=Ici 0)
    measurableSet_Ici
  simp only [Iic_union_Ici,Iic_inter_Ici,Icc_self] at htotal
  have hu : μ.real univ=1 := by simp [μ]
  have hz : μ.real {0}=0 := by simp [measureReal_def]
  rw [hu,hz,add_zero] at htotal
  change μ.real (Iic 0)=1/2
  linarith

theorem actual_standard_gaussian_cdf_one_is_the_actual_interval_integral :
    standardCDF 1=1/2+(Real.sqrt (2*Real.pi))⁻¹*
      (∫x in (0:ℝ)..1,Real.exp (-x^2/2)) := by
  have hd := intervalIntegral.integral_Iic_sub_Iic
    ((integrable_gaussianPDFReal 0 1).integrableOn (s:=Iic (0:ℝ)))
    ((integrable_gaussianPDFReal 0 1).integrableOn (s:=Iic (1:ℝ)))
  rw [←actual_standard_gaussian_cdf_is_its_density_integral,
    ←actual_standard_gaussian_cdf_is_its_density_integral,
    actual_standard_gaussian_symmetry_and_half_mass] at hd
  have hf : gaussianPDFReal 0 1=
      (fun x : ℝ=>(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/2)) := by
    funext x;simp [gaussianPDFReal]
  rw [hf,intervalIntegral.integral_const_mul] at hd
  linarith

theorem actual_standard_gaussian_normalization_rational_enclosure :
    (3989422/10000000:ℝ)<(Real.sqrt (2*Real.pi))⁻¹ ∧
    (Real.sqrt (2*Real.pi))⁻¹<(3989424/10000000:ℝ) := by
  have hp := Real.pi_gt_d6
  have hq := Real.pi_lt_d6
  have hs : (Real.sqrt (2*Real.pi))^2=2*Real.pi :=
    Real.sq_sqrt (by positivity)
  have hpos : 0<Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · rw [←one_div,lt_div_iff₀ hpos]
    nlinarith [Real.sqrt_nonneg (2*Real.pi)]
  · rw [←one_div,div_lt_iff₀ hpos]
    nlinarith [Real.sqrt_nonneg (2*Real.pi)]

theorem actual_standard_gaussian_cdf_one_certified_probability :
    (8413446/10000000:ℝ)<standardCDF 1 ∧
    standardCDF 1<(8413449/10000000:ℝ) := by
  rw [actual_standard_gaussian_cdf_one_is_the_actual_interval_integral]
  have hc := actual_standard_gaussian_normalization_rational_enclosure
  have hi := actual_gaussian_exponential_integral_rational_enclosure
  constructor <;> nlinarith

end SafeLearning.CompleteAppliedGaussianCDF
