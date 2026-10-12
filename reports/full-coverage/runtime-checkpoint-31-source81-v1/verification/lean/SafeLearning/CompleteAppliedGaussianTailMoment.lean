import SafeLearning.CompleteAppliedGaussianQuantile

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedGaussianTailMoment
open CompleteAppliedGaussianCDF CompleteAppliedGaussianQuantile

def standardPDF (point : ℝ) : ℝ := (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-point^2/2)

theorem actual_standard_gaussian_pdf_is_the_literal_density (point : ℝ) :
    gaussianPDFReal 0 1 point=standardPDF point := by
  simp [gaussianPDFReal_def,standardPDF]

theorem actual_standard_gaussian_density_has_its_true_derivative (point : ℝ) :
    HasDerivAt standardPDF (-point*standardPDF point) point := by
  have hd := (((hasDerivAt_pow 2 point).neg).div_const 2).exp.const_mul (Real.sqrt (2*Real.pi))⁻¹
  convert hd using 1
  · rfl
  · dsimp [standardPDF]
    ring

theorem actual_standard_gaussian_density_tends_to_zero : Tendsto standardPDF atTop (𝓝 0) := by
  have hp : Tendsto (fun point:ℝ=>-(1/2:ℝ)*point^2) atTop atBot :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num)
  have he := (Real.tendsto_exp_atBot.comp hp).const_mul (Real.sqrt (2*Real.pi))⁻¹
  convert he using 1
  · funext point
    unfold standardPDF
    congr 2
    ring
  · simp

theorem actual_standard_gaussian_weighted_density_is_integrable :
    Integrable (fun point:ℝ=>point*standardPDF point) volume := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/2)).const_mul (Real.sqrt (2*Real.pi))⁻¹
  convert hi using 1
  funext point
  unfold standardPDF
  have he : -point^2/2=-(1/2:ℝ)*point^2 := by ring
  rw [he]
  ring

theorem actual_integral_of_the_upper_tail_weighted_density_is_density_at_the_threshold
    (threshold : ℝ) :
    (∫point in Ioi threshold,point*standardPDF point)=standardPDF threshold := by
  have hi : IntegrableOn (fun point:ℝ=>-(point*standardPDF point)) (Ioi threshold) :=
    actual_standard_gaussian_weighted_density_is_integrable.neg.integrableOn
  have hf := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun point (_:point∈Ici threshold)=>actual_standard_gaussian_density_has_its_true_derivative point)
    (by simpa only [neg_mul] using hi) actual_standard_gaussian_density_tends_to_zero
  have he : (fun point:ℝ=>-point*standardPDF point)=(fun point=>-(point*standardPDF point)) := by
    funext point
    ring
  rw [he,integral_neg,zero_sub] at hf
  linarith

theorem actual_standard_gaussian_upper_tail_first_moment
    (threshold : ℝ) :
    (∫point in Ioi threshold,point ∂gaussianReal 0 1)=standardPDF threshold := by
  rw [←integral_indicator measurableSet_Ioi,integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal)≠0)]
  have he : (fun point:ℝ=>gaussianPDFReal 0 1 point • (Ioi threshold).indicator (fun x:ℝ=>x) point)=
      (Ioi threshold).indicator (fun point:ℝ=>point*standardPDF point) := by
    funext point
    by_cases h : point∈Ioi threshold
    · simp [h,actual_standard_gaussian_pdf_is_the_literal_density,mul_comm]
    · simp [h]
  rw [he,integral_indicator measurableSet_Ioi]
  exact actual_integral_of_the_upper_tail_weighted_density_is_density_at_the_threshold threshold

end SafeLearning.CompleteAppliedGaussianTailMoment
