import SafeLearning.CompleteAppliedGaussianFourGenerative
import SafeLearning.CompleteAppliedGaussianChanceConstraint
import SafeLearning.CompleteAppliedGaussianStandardization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedGaussianFourSource
open CompleteAppliedGaussianFourUpdate CompleteAppliedGaussianFourJoint
open CompleteAppliedGaussianCDF CompleteAppliedGaussianChanceConstraint

def sourcePosterior : Measure ℝ := gaussianReal (72/85) (1/17)
def sourceSigma : ℝ := Real.sqrt (1/17)
def sourceLower : ℝ := 72/85-2*sourceSigma
def sourceStandardMagnitude : ℝ := 59/(170*sourceSigma)

instance sourcePosterior_probability : IsProbabilityMeasure sourcePosterior := by
  unfold sourcePosterior;infer_instance
instance sourcePosterior_no_atoms : NullSingletonClass sourcePosterior :=
  nullSingletonClass_gaussianReal (by norm_num)

theorem actual_iid_four_noise_average_has_the_literal_gaussian_law_and_variance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (noise : Fin 4→Ω→ℝ) (hindep : iIndepFun noise P)
    (hlaw : ∀i,HasLaw (noise i) (gaussianReal 0 (1/4)) P) :
    HasLaw (fun omega=>(noise 0 omega+noise 1 omega+noise 2 omega+noise 3 omega)/4)
      (gaussianReal 0 (1/16)) P ∧
    Var[fun omega=>(noise 0 omega+noise 1 omega+noise 2 omega+noise 3 omega)/4;P]=1/16 := by
  have hmeas : ∀i,AEMeasurable (noise i) P:=fun i=>(hlaw i).aemeasurable
  have h01 : HasLaw (fun omega=>noise 0 omega+noise 1 omega) (gaussianReal 0 (1/2)) P := by
    refine ⟨(hmeas 0).add (hmeas 1),?_⟩
    have h:=gaussianReal_add_gaussianReal_of_indepFun
      (hindep.indepFun (show (0:Fin 4)≠1 by decide)) (hlaw 0) (hlaw 1)
    norm_num at h
    exact h
  have h23 : HasLaw (fun omega=>noise 2 omega+noise 3 omega) (gaussianReal 0 (1/2)) P := by
    refine ⟨(hmeas 2).add (hmeas 3),?_⟩
    have h:=gaussianReal_add_gaussianReal_of_indepFun
      (hindep.indepFun (show (2:Fin 4)≠3 by decide)) (hlaw 2) (hlaw 3)
    norm_num at h
    exact h
  have hsumIndep : IndepFun (fun omega=>noise 0 omega+noise 1 omega)
      (fun omega=>noise 2 omega+noise 3 omega) P :=
    (hindep.indepFun_prodMk_prodMk₀ hmeas 0 1 2 3
      (by decide) (by decide) (by decide) (by decide)).comp
        (show Measurable (fun pair:ℝ×ℝ=>pair.1+pair.2) by fun_prop)
        (show Measurable (fun pair:ℝ×ℝ=>pair.1+pair.2) by fun_prop)
  have hsum : HasLaw (fun omega=>(noise 0 omega+noise 1 omega)+(noise 2 omega+noise 3 omega))
      (gaussianReal 0 1) P := by
    refine ⟨h01.aemeasurable.add h23.aemeasurable,?_⟩
    have h:=gaussianReal_add_gaussianReal_of_indepFun hsumIndep h01 h23
    norm_num at h
    exact h
  have havg:=gaussianReal_div_const hsum 4
  have hv : (1:ℝ≥0)/NNReal.mk ((4:ℝ)^2) (sq_nonneg _)=1/16 := by ext;norm_num
  rw [hv] at havg
  norm_num at havg
  have he : (fun omega=>(noise 0 omega+noise 1 omega+noise 2 omega+noise 3 omega)/4)=
      (fun omega=>((noise 0 omega+noise 1 omega)+(noise 2 omega+noise 3 omega))/4) := by
    funext omega;ring
  rw [he]
  refine ⟨havg,?_⟩
  rw [havg.variance_eq,variance_id_gaussianReal]
  norm_num

theorem actual_source_posterior_moments_and_precision_addition :
    (∫latent:ℝ,latent ∂sourcePosterior)=72/85 ∧
      Var[fun latent:ℝ=>latent;sourcePosterior]=1/17 ∧
      (1/4:ℝ)/4=1/16 ∧ (1/16:ℝ)⁻¹=16 ∧ (1+16:ℝ)=17 ∧
      (16*(9/10:ℝ))/17=72/85 ∧ sourceSigma^2=1/17 ∧ 0<sourceSigma := by
  rw [sourcePosterior,integral_id_gaussianReal,variance_fun_id_gaussianReal]
  norm_num
  exact ⟨Real.sq_sqrt (by norm_num),Real.sqrt_pos.mpr (by norm_num)⟩

theorem actual_four_data_average_nine_tenths_has_the_literal_source_posterior
    (y : Readings) (hy : readingAverage y=9/10) :
    fullPosteriorKernel y=sourcePosterior ∧
      (readingsEvidence y)⁻¹ • weightedPrior y=sourcePosterior :=
  ⟨actual_average_nine_tenths_selects_the_derived_four_data_gaussian_kernel y hy,
    actual_all_four_readings_with_average_nine_tenths_have_the_literal_posterior y hy⟩

theorem actual_posterior_strict_threshold_probability_is_the_true_standardized_cdf
    (threshold : ℝ) :
    sourcePosterior.real {latent:ℝ | latent<threshold}=
      standardCDF ((threshold-72/85)/sourceSigma) := by
  have hl : HasLaw id sourcePosterior sourcePosterior:=⟨measurable_id.aemeasurable,Measure.map_id⟩
  have h:=actual_nondegenerate_gaussian_cdf_is_the_standardized_true_cdf
    (72/85) (1/17) (by norm_num) hl threshold
  change sourcePosterior.real (Iio threshold)=_
  rw [measureReal_congr (Iio_ae_eq_Iic (μ:=sourcePosterior))]
  exact h

theorem actual_posterior_half_threshold_and_lower_bound_failure_probabilities :
    sourcePosterior.real {latent:ℝ | latent<1/2}=standardCDF (-sourceStandardMagnitude) ∧
      sourcePosterior.real {latent:ℝ | latent<sourceLower}=standardCDF (-2) := by
  have hs : sourceSigma≠0:=ne_of_gt actual_source_posterior_moments_and_precision_addition.2.2.2.2.2.2.2
  constructor
  · rw [actual_posterior_strict_threshold_probability_is_the_true_standardized_cdf]
    congr 1
    unfold sourceStandardMagnitude
    field_simp
    <;> ring
  · rw [actual_posterior_strict_threshold_probability_is_the_true_standardized_cdf]
    congr 1
    unfold sourceLower
    field_simp
    <;> ring

end SafeLearning.CompleteAppliedGaussianFourSource
