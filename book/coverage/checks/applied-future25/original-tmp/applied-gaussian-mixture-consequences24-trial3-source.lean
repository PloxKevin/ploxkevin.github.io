import SafeLearning.CompleteAppliedGaussianMixtureLaw24
import SafeLearning.CompleteAppliedGaussianMixtureCDFNumbers24
import SafeLearning.CompleteAppliedGaussianSmallTail24
set_option autoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SafeLearning.CompleteAppliedGaussianMixtureConsequences24
open CompleteAppliedGaussianMixtureLaw24 CompleteAppliedGaussianMixtureCDFNumbers24
  CompleteAppliedGaussianSmallTail24 CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile

theorem actual_variance_matched_gaussian_has_the_same_mean_and_variance :
    (∫ x, x ∂gaussianReal 0 2) = (∫ x, x ∂residualLaw) ∧
      variance id (gaussianReal 0 2) = variance id residualLaw := by
  have hv := actual_source_residual_mean_and_variance
  simp only [integral_id_gaussianReal, variance_id_gaussianReal]
  norm_num [hv.1,hv.2]

theorem actual_variance_matched_gaussian_tail_formula (r : ℝ) (hr : 0 ≤ r) :
    absoluteTail (gaussianReal 0 2) r = 2*(1-standardCDF (r/Real.sqrt 2)) := by
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h := actual_positive_scaled_gaussian_tail (Real.sqrt 2) r hs hr
  have hv : (⟨(Real.sqrt (2:ℝ))^2, sq_nonneg _⟩ : NNReal) = (2:NNReal) := by
    apply Subtype.ext
    change (Real.sqrt (2:ℝ))^2 = 2
    exact Real.sq_sqrt (by norm_num)
  rw [hv] at h
  exact h

theorem actual_source_large_tail_enclosure :
    (1911/100000:ℝ) < absoluteTail residualLaw 5 ∧
      absoluteTail residualLaw 5 < 1914/100000 := by
  have hf := actual_printed_source_tail_formulas.1
  have hc := actual_CDF_five_thirds_certified
  have ht := actual_standard_gaussian_absolute_tail_ten_is_small
  change absoluteTail (gaussianReal 0 1) 10 < (1/50000:ℝ) at ht
  have hn : 0 ≤ absoluteTail (gaussianReal 0 1) 10 := measureReal_nonneg
  have he := actual_standard_gaussian_absolute_tail 10 (by norm_num)
  constructor <;> nlinarith

theorem actual_source_near_origin_tail_enclosure :
    (1841/10000:ℝ) < absoluteTail residualLaw 1 ∧
      absoluteTail residualLaw 1 < 1843/10000 := by
  have hf := actual_printed_source_tail_formulas.2
  have h2 := actual_CDF_two_certified
  have h3 := actual_CDF_third_certified
  constructor <;> nlinarith

theorem actual_matched_gaussian_large_tail_enclosure :
    (4068/10000000:ℝ) < absoluteTail (gaussianReal 0 2) 5 ∧
      absoluteTail (gaussianReal 0 2) 5 < 4071/10000000 := by
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hl : (35355/10000:ℝ) < 5/Real.sqrt 2 := by
    rw [lt_div_iff₀ hs]; nlinarith
  have hu : 5/Real.sqrt (2:ℝ) < 35356/10000 := by
    rw [div_lt_iff₀ hs]; nlinarith
  have mono := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
  have hcl := mono hl
  have hcu := mono hu
  have hn := actual_CDF_large_lower_certified
  have hm := actual_CDF_large_upper_certified
  rw [actual_variance_matched_gaussian_tail_formula 5 (by norm_num)]
  constructor <;> linarith

theorem actual_matched_gaussian_near_origin_tail_enclosure :
    (47944/100000:ℝ) < absoluteTail (gaussianReal 0 2) 1 ∧
      absoluteTail (gaussianReal 0 2) 1 < 47951/100000 := by
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hl : (7071/10000:ℝ) < 1/Real.sqrt 2 := by
    rw [lt_div_iff₀ hs]; nlinarith
  have hu : 1/Real.sqrt (2:ℝ) < 7072/10000 := by
    rw [div_lt_iff₀ hs]; nlinarith
  have mono := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2
  have hcl := mono hl
  have hcu := mono hu
  have hn := actual_CDF_small_lower_certified
  have hm := actual_CDF_small_upper_certified
  rw [actual_variance_matched_gaussian_tail_formula 1 (by norm_num)]
  constructor <;> linarith

theorem actual_all_four_printed_tail_numbers_are_correct_roundings :
    |absoluteTail residualLaw 5 - (19/1000:ℝ)| < 1/2000 ∧
    |absoluteTail (gaussianReal 0 2) 5 - (4/10000:ℝ)| < 1/20000 ∧
    |absoluteTail residualLaw 1 - (18/100:ℝ)| < 1/200 ∧
    |absoluteTail (gaussianReal 0 2) 1 - (48/100:ℝ)| < 1/200 := by
  have ha := actual_source_large_tail_enclosure
  have hb := actual_matched_gaussian_large_tail_enclosure
  have hc := actual_source_near_origin_tail_enclosure
  have hd := actual_matched_gaussian_near_origin_tail_enclosure
  refine ⟨?_,?_,?_,?_⟩ <;> rw [abs_lt] <;> constructor <;> linarith

theorem actual_residual_has_heavier_large_tails_and_more_near_origin_mass :
    absoluteTail (gaussianReal 0 2) 5 < absoluteTail residualLaw 5 ∧
      absoluteTail residualLaw 1 < absoluteTail (gaussianReal 0 2) 1 := by
  have ha := actual_source_large_tail_enclosure
  have hb := actual_matched_gaussian_large_tail_enclosure
  have hc := actual_source_near_origin_tail_enclosure
  have hd := actual_matched_gaussian_near_origin_tail_enclosure
  constructor <;> linarith

end SafeLearning.CompleteAppliedGaussianMixtureConsequences24
