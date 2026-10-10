import SafeLearning.CompleteAppliedFractionalTailDual
import SafeLearning.CompleteAppliedGaussianTailMoment
import SafeLearning.CompleteAppliedGaussianNinetyQuantile

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace SafeLearning.CompleteAppliedGaussianCVaR
open CompleteAppliedFractionalTailDual CompleteAppliedGaussianTailMoment
open CompleteAppliedGaussianCDF CompleteAppliedGaussianNinetyQuantile
open CompleteFoundationsHingeExpectations CompleteFoundationsCVaRQuotients

def upperTailSelector (threshold point : ℝ) : ℝ :=
  (Ioi threshold).indicator (fun _:ℝ=>(1:ℝ)) point

def gaussianLoss (mean sigma point : ℝ) : ℝ := mean+sigma*point

theorem actual_standard_gaussian_upper_tail_probability (threshold : ℝ) :
    (gaussianReal 0 1).real (Ioi threshold)=1-standardCDF threshold := by
  have h := measureReal_compl (μ:=gaussianReal 0 1) (s:=Iic threshold) measurableSet_Iic
  simpa [standardCDF] using h

theorem actual_upper_tail_indicator_is_admissible_with_its_true_probability
    (threshold : ℝ) :
    upperTailSelector threshold∈admissibleSelectors (gaussianReal 0 1) (1-standardCDF threshold) := by
  refine ⟨measurable_const.indicator measurableSet_Ioi,?_,?_⟩
  · intro point
    by_cases hp : point∈Ioi threshold <;> simp [upperTailSelector,hp]
  · unfold upperTailSelector
    rw [integral_indicator measurableSet_Ioi]
    simp only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ]
    exact actual_standard_gaussian_upper_tail_probability threshold

theorem actual_affine_standard_gaussian_loss_has_the_requested_gaussian_law
    (mean sigma : ℝ) :
    HasLaw (gaussianLoss mean sigma) (gaussianReal mean (NNReal.mk (sigma^2) (sq_nonneg _))) (gaussianReal 0 1) := by
  have hi : HasLaw (fun point:ℝ=>point) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_id.aemeasurable,by simp⟩
  have h := gaussianReal_const_add (gaussianReal_const_mul hi sigma) mean
  change HasLaw (fun point:ℝ=>mean+sigma*point) _ _
  simpa only [mul_zero,zero_add,mul_one] using h

theorem actual_affine_gaussian_selected_tail_expectation
    (mean sigma threshold : ℝ) :
    (∫point,gaussianLoss mean sigma point*upperTailSelector threshold point ∂gaussianReal 0 1)=
      mean*(1-standardCDF threshold)+sigma*standardPDF threshold := by
  have hi : Integrable (fun point:ℝ=>point) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)
  have he : (fun point:ℝ=>gaussianLoss mean sigma point*upperTailSelector threshold point)=
      (Ioi threshold).indicator (gaussianLoss mean sigma) := by
    funext point
    by_cases hp : point∈Ioi threshold <;> simp [upperTailSelector,hp]
  rw [he,integral_indicator measurableSet_Ioi]
  unfold gaussianLoss
  rw [integral_add (integrable_const mean) (hi.integrableOn.const_mul sigma),integral_const,integral_const_mul,
    actual_standard_gaussian_upper_tail_first_moment]
  simp only [Measure.real,Measure.restrict_apply_univ] at *
  rw [show (gaussianReal 0 1 (Ioi threshold)).toReal=1-standardCDF threshold from
    actual_standard_gaussian_upper_tail_probability threshold]
  simp only [smul_eq_mul]
  ring

theorem actual_gaussian_fractional_worst_tail_and_RU_minimum
    (mean sigma alpha threshold : ℝ) (hsigma : 0<sigma) (halpha : alpha<1)
    (hquantile : standardCDF threshold=alpha) :
    IsGreatest ((fun selector=>actualTailMean (gaussianReal 0 1) (gaussianLoss mean sigma) selector (1-alpha)) ''
      admissibleSelectors (gaussianReal 0 1) (1-alpha))
      (mean+sigma*standardPDF threshold/(1-alpha)) ∧
    IsLeast (Set.range (actualRUObjective (gaussianReal 0 1) (gaussianLoss mean sigma) alpha))
      (mean+sigma*standardPDF threshold/(1-alpha)) ∧
    actualWorstTailMean (gaussianReal 0 1) (gaussianLoss mean sigma) (1-alpha)=
      mean+sigma*standardPDF threshold/(1-alpha) := by
  have hi : Integrable (gaussianLoss mean sigma) (gaussianReal 0 1) :=
    (integrable_const mean).add (((memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)).const_mul sigma)
  have hselect : upperTailSelector threshold∈admissibleSelectors (gaussianReal 0 1) (1-alpha) := by
    rw [←hquantile]
    exact actual_upper_tail_indicator_is_admissible_with_its_true_probability threshold
  have habove : ∀point,mean+sigma*threshold<gaussianLoss mean sigma point→upperTailSelector threshold point=1 := by
    intro point hp
    have hpt : threshold<point := by unfold gaussianLoss at hp; nlinarith
    simp [upperTailSelector,hpt]
  have hbelow : ∀point,gaussianLoss mean sigma point < mean+sigma*threshold→upperTailSelector threshold point=0 := by
    intro point hp
    have hpt : point<threshold := by unfold gaussianLoss at hp; nlinarith
    simp [upperTailSelector,not_lt.mpr hpt.le]
  have h := actual_mass_matched_threshold_selector_is_greatest_tail_and_least_RU_objective
    (gaussianLoss mean sigma) hi alpha (mean+sigma*threshold) halpha (upperTailSelector threshold) hselect habove hbelow
  have hv : actualTailMean (gaussianReal 0 1) (gaussianLoss mean sigma) (upperTailSelector threshold) (1-alpha)=
      mean+sigma*standardPDF threshold/(1-alpha) := by
    unfold actualTailMean
    rw [actual_affine_gaussian_selected_tail_expectation,hquantile]
    field_simp [(sub_pos.mpr halpha).ne']
  have hru := actual_mass_matched_threshold_selector_attains_the_RU_value
    (gaussianLoss mean sigma) hi alpha (mean+sigma*threshold) halpha (upperTailSelector threshold) hselect habove hbelow
  have hrueq : actualRUObjective (gaussianReal 0 1) (gaussianLoss mean sigma) alpha (mean+sigma*threshold)=
      mean+sigma*standardPDF threshold/(1-alpha) := hru.symm.trans hv
  rw [hv] at h
  rw [hrueq] at h
  exact h

theorem actual_source_matched_gaussian_has_true_mean_variance_law_and_CVaR :
    HasLaw (gaussianLoss (4/5) (Real.sqrt (124/25))) (gaussianReal (4/5) (124/25)) (gaussianReal 0 1) ∧
    actualWorstTailMean (gaussianReal 0 1) (gaussianLoss (4/5) (Real.sqrt (124/25))) (1/10)=
      (4/5)+10*Real.sqrt (124/25)*standardPDF truePointNinetyQuantile := by
  have hs : (Real.sqrt (124/25:ℝ))^2=124/25 := Real.sq_sqrt (by norm_num)
  have hl := actual_affine_standard_gaussian_loss_has_the_requested_gaussian_law (4/5) (Real.sqrt (124/25))
  have hv : NNReal.mk ((Real.sqrt (124/25:ℝ))^2) (sq_nonneg _)=(124/25:NNReal) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk]
    exact hs
  rw [hv] at hl
  have hr := actual_gaussian_fractional_worst_tail_and_RU_minimum (4/5) (Real.sqrt (124/25))
    (9/10) truePointNinetyQuantile (by positivity) (by norm_num)
    actual_point_ninety_quantile_is_the_unique_cdf_root_and_smallest_threshold.1
  refine ⟨hl,?_⟩
  have he : (1:ℝ)-9/10=1/10 := by norm_num
  rw [he] at hr
  calc
    _=4/5+Real.sqrt (124/25)*standardPDF truePointNinetyQuantile/(1/10) := hr.2.2
    _=_ := by ring

end SafeLearning.CompleteAppliedGaussianCVaR
