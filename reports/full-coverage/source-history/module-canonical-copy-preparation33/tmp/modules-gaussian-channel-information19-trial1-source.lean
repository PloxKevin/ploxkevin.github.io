import SafeLearning.CompleteAppliedGaussianEntropy
import SafeLearning.CompleteModulesGaussianRegressionScalar
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
namespace SafeLearning.CompleteModulesGaussianChannelInformation
open SafeLearning.CompleteAppliedGaussianEntropy
open SafeLearning.CompleteModulesGaussianRegressionScalar

theorem actual_two_nondegenerate_gaussians_have_the_density_log_likelihood_ratio
    (m n : ℝ) (v w : ℝ≥0) (hv : v ≠ 0) (hw : w ≠ 0) :
    llr (gaussianReal m v) (gaussianReal n w) =ᵐ[volume]
      (fun y => Real.log (gaussianPDFReal m v y)-Real.log (gaussianPDFReal n w y)) := by
  have hr := Measure.rnDeriv_withDensity_right (gaussianReal m v) volume
    (measurable_gaussianPDF n w).aemeasurable
    (ae_of_all _ (fun y => (gaussianPDF_pos n hw y).ne'))
    (ae_of_all _ (fun _ => gaussianPDF_lt_top.ne))
  rw [← gaussianReal_of_var_ne_zero n hw] at hr
  filter_upwards [hr,rnDeriv_gaussianReal m v] with y h1 h2
  rw [llr,h1,h2,ENNReal.toReal_mul,ENNReal.toReal_inv,
    toReal_gaussianPDF,toReal_gaussianPDF,Real.log_mul
      (inv_ne_zero (gaussianPDFReal_pos n w y hw).ne')
      (gaussianPDFReal_pos m v y hv).ne',Real.log_inv]
  ring

def actualJoint (nu : Measure ℝ) (lambda : ℝ≥0) : Measure (ℝ × ℝ) :=
  (nu.prod (gaussianReal 0 lambda)).map (fun p : ℝ × ℝ => (p.1,p.2+p.1))

instance actualJoint_probability (nu : Measure ℝ) [IsProbabilityMeasure nu] (lambda : ℝ≥0) :
    IsProbabilityMeasure (actualJoint nu lambda) := by
  unfold actualJoint
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem actual_channel_joint_is_the_true_conditional_gaussian_composition
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (lambda : ℝ≥0) :
    actualJoint nu lambda=nu ⊗ₘ conditionalKernel 0 1 lambda := by
  simpa only [actualJoint,one_mul] using
    actual_independent_gaussian_residual_product_derives_the_conditional_joint nu 0 1 lambda

theorem actual_channel_joint_has_exact_input_and_noise_marginals
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (lambda : ℝ≥0) :
    (actualJoint nu lambda).map Prod.fst=nu ∧
      (actualJoint nu lambda).map (fun p : ℝ × ℝ => p.2-p.1)=gaussianReal 0 lambda := by
  constructor
  · unfold actualJoint
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp [Function.comp_def]
  · unfold actualJoint
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simpa only [Function.comp_def,add_sub_cancel_right,Measure.map_snd_prod,
      measure_univ,one_smul]

theorem actual_scalar_gaussian_channel_has_the_true_gaussian_output_law
    (m : ℝ) (v lambda : ℝ≥0) :
    (actualJoint (gaussianReal m v) lambda).map Prod.snd=gaussianReal m (v+lambda) := by
  unfold actualJoint
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change ((gaussianReal m v).prod (gaussianReal 0 lambda)).map
    (fun p : ℝ × ℝ => p.2+p.1)=_
  simpa only [Measure.conv,add_comm,add_zero] using
    (gaussianReal_conv_gaussianReal (m₁:=m) (m₂:=0) (v₁:=v) (v₂:=lambda))

theorem actual_positive_noise_channel_joint_is_absolutely_continuous_with_respect_to_input_times_gaussian_output
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (lambda q : ℝ≥0) (hlambda : lambda ≠ 0) (hq : q ≠ 0) (m : ℝ) :
    actualJoint nu lambda ≪ nu.prod (gaussianReal m q) := by
  rw [actual_channel_joint_is_the_true_conditional_gaussian_composition,
    ← Measure.compProd_const]
  apply Measure.AbsolutelyContinuous.compProd_right
  exact ae_of_all _ (fun x =>
    (gaussianReal_absolutelyContinuous (0+1*x) hlambda).trans
      (gaussianReal_absolutelyContinuous' m hq))

theorem actual_positive_noise_joint_log_likelihood_ratio_is_the_true_gaussian_density_ratio
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (lambda q : ℝ≥0) (hlambda : lambda ≠ 0) (hq : q ≠ 0) (m : ℝ) :
    llr (actualJoint nu lambda) (nu.prod (gaussianReal m q)) =ᵐ[actualJoint nu lambda]
      (fun p => Real.log (gaussianPDFReal p.1 lambda p.2)-
        Real.log (gaussianPDFReal m q p.2)) := by
  let k := conditionalKernel 0 1 lambda
  let e := Kernel.const ℝ (gaussianReal m q)
  have hac : nu ⊗ₘ k ≪ nu ⊗ₘ e := by
    simpa only [k,e,Measure.compProd_const,
      ← actual_channel_joint_is_the_true_conditional_gaussian_composition] using
      actual_positive_noise_channel_joint_is_absolutely_continuous_with_respect_to_input_times_gaussian_output
        nu lambda q hlambda hq m
  have hker : (fun p : ℝ × ℝ => Real.log (k.rnDeriv e p.1 p.2).toReal) =ᵐ[nu ⊗ₘ e]
      (fun p => Real.log (gaussianPDFReal p.1 lambda p.2)-
        Real.log (gaussianPDFReal m q p.2)) := by
    apply Measure.ae_compProd_of_ae_ae
    · apply measurableSet_eq_fun
      · exact (Kernel.measurable_rnDeriv k e).ennreal_toReal.log
      · unfold gaussianPDFReal
        fun_prop
    · apply ae_of_all
      intro x
      have hpdf := (gaussianReal_absolutelyContinuous m hq).ae_le
        (actual_two_nondegenerate_gaussians_have_the_density_log_likelihood_ratio
          x m lambda q hlambda hq)
      filter_upwards [k.rnDeriv_eq_rnDeriv_measure (η:=e) (a:=x),hpdf] with y h1 h2
      simpa only [k,e,conditionalKernel,Kernel.const_apply,zero_add,one_mul,llr,h1] using h2
  have hr := rnDeriv_measure_compProd_right nu k e
  rw [actual_channel_joint_is_the_true_conditional_gaussian_composition,
    ← Measure.compProd_const]
  change llr (nu ⊗ₘ k) (nu ⊗ₘ e) =ᵐ[nu ⊗ₘ k] _
  filter_upwards [hac.ae_le hr,hac.ae_le hker] with p h1 h2
  simpa only [llr,h1] using h2

theorem actual_conditional_noise_log_density_is_integrable_and_has_the_noise_entropy_integral
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (lambda : ℝ≥0) (hlambda : lambda ≠ 0) :
    Integrable (fun p : ℝ × ℝ => Real.log (gaussianPDFReal p.1 lambda p.2)) (actualJoint nu lambda) ∧
      (∫ p,Real.log (gaussianPDFReal p.1 lambda p.2) ∂actualJoint nu lambda)=
        -gaussianDifferentialEntropy 0 lambda := by
  have hm := (actual_channel_joint_has_exact_input_and_noise_marginals nu lambda).2
  have hi := actual_gaussian_log_density_integrable 0 lambda hlambda
  have hi' : Integrable (fun z => Real.log (gaussianPDFReal 0 lambda z))
      ((actualJoint nu lambda).map (fun p : ℝ × ℝ => p.2-p.1)) := hm.symm ▸ hi
  have he : (fun p : ℝ × ℝ => Real.log (gaussianPDFReal 0 lambda (p.2-p.1)))=
      (fun p => Real.log (gaussianPDFReal p.1 lambda p.2)) := by
    funext p
    rw [gaussianPDFReal_sub,zero_add]
  constructor
  · simpa only [Function.comp_def,he] using hi'.comp_aemeasurable (by fun_prop)
  · unfold gaussianDifferentialEntropy
    rw [neg_neg,← hm,integral_map (by fun_prop) hi'.aestronglyMeasurable,he]

theorem actual_gaussian_output_log_density_is_integrable_and_has_its_true_entropy_integral
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (lambda q : ℝ≥0) (hq : q ≠ 0) (m : ℝ)
    (houtput : (actualJoint nu lambda).map Prod.snd=gaussianReal m q) :
    Integrable (fun p : ℝ × ℝ => Real.log (gaussianPDFReal m q p.2)) (actualJoint nu lambda) ∧
      (∫ p,Real.log (gaussianPDFReal m q p.2) ∂actualJoint nu lambda)=
        -gaussianDifferentialEntropy m q := by
  have hi := actual_gaussian_log_density_integrable m q hq
  have hi' : Integrable (fun z => Real.log (gaussianPDFReal m q z))
      ((actualJoint nu lambda).map Prod.snd) := houtput.symm ▸ hi
  constructor
  · exact hi'.comp_aemeasurable measurable_snd.aemeasurable
  · unfold gaussianDifferentialEntropy
    rw [neg_neg,← houtput,integral_map measurable_snd.aemeasurable hi'.aestronglyMeasurable]

theorem actual_positive_noise_gaussian_output_channel_KL_is_the_entropy_difference
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (lambda q : ℝ≥0) (hlambda : lambda ≠ 0) (hq : q ≠ 0) (m : ℝ)
    (houtput : (actualJoint nu lambda).map Prod.snd=gaussianReal m q) :
    klDiv (actualJoint nu lambda) (nu.prod (gaussianReal m q)) ≠ ∞ ∧
      (klDiv (actualJoint nu lambda) (nu.prod (gaussianReal m q))).toReal=
        gaussianDifferentialEntropy m q-gaussianDifferentialEntropy 0 lambda := by
  have hac := actual_positive_noise_channel_joint_is_absolutely_continuous_with_respect_to_input_times_gaussian_output
    nu lambda q hlambda hq m
  have hllr := actual_positive_noise_joint_log_likelihood_ratio_is_the_true_gaussian_density_ratio
    nu lambda q hlambda hq m
  have hnoise := actual_conditional_noise_log_density_is_integrable_and_has_the_noise_entropy_integral
    nu lambda hlambda
  have hout := actual_gaussian_output_log_density_is_integrable_and_has_its_true_entropy_integral
    nu lambda q hq m houtput
  have hint : Integrable (llr (actualJoint nu lambda) (nu.prod (gaussianReal m q)))
      (actualJoint nu lambda) := (integrable_congr hllr).mpr (hnoise.1.sub hout.1)
  refine ⟨klDiv_ne_top hac hint,?_⟩
  rw [toReal_klDiv hac hint,probReal_univ,probReal_univ,add_sub_cancel,
    integral_congr_ae hllr,integral_sub hnoise.1 hout.1,hnoise.2,hout.2]
  ring

theorem actual_scalar_gaussian_channel_mutual_information_KL_formula_including_singular_latent
    (m : ℝ) (v lambda : ℝ≥0) (hlambda : lambda ≠ 0) :
    klDiv (actualJoint (gaussianReal m v) lambda)
      ((gaussianReal m v).prod (gaussianReal m (v+lambda))) ≠ ∞ ∧
      (klDiv (actualJoint (gaussianReal m v) lambda)
        ((gaussianReal m v).prod (gaussianReal m (v+lambda)))).toReal=
        (1/2:ℝ)*Real.log (1+(v:ℝ)/(lambda:ℝ)) := by
  have hl : (0:ℝ) < lambda := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hlambda)
  have hq : v+lambda ≠ 0 := by positivity
  have h := actual_positive_noise_gaussian_output_channel_KL_is_the_entropy_difference
    (gaussianReal m v) lambda (v+lambda) hlambda hq m
      (actual_scalar_gaussian_channel_has_the_true_gaussian_output_law m v lambda)
  refine ⟨h.1,?_⟩
  rw [h.2,actual_gaussian_differential_entropy m (v+lambda) hq,
    actual_gaussian_differential_entropy 0 lambda hlambda]
  have hc : 0 < 2*Real.pi*Real.exp 1 := by positivity
  have hq' : (0:ℝ) < (v+lambda:ℝ≥0) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hq)
  rw [Real.log_mul hc.ne' hq'.ne',Real.log_mul hc.ne' hl.ne']
  rw [← Real.log_div hq'.ne' hl.ne']
  congr 1
  push_cast
  field_simp
  ring

end SafeLearning.CompleteModulesGaussianChannelInformation
