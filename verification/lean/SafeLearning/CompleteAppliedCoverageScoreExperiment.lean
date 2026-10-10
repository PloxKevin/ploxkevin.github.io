import SafeLearning.CompleteAppliedCoverageScoreTestMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SafeLearning.CompleteAppliedCoverageScoreExperiment
open CompleteAppliedCoverageBeta CompleteAppliedCoverageContinuousTransform
open CompleteAppliedCoverageOrderStatistic CompleteAppliedCoverageScoreTestMoments

theorem actual_fixed_calibration_fresh_score_coverage_is_its_actual_cdf
    (law : Measure ℝ) [IsProbabilityMeasure law] (calibration : Fin 19→ℝ) :
    law.real {test:ℝ|test≤ secondLargest calibration}=cdf law (secondLargest calibration) :=
  (cdf_eq_real law (secondLargest calibration)).symm

theorem actual_beta_distributed_calibration_coverage_derives_the_raw_test_mean_and_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (threshold : Ω→ℝ) (hthreshold : Measurable threshold)
    (hcov : HasLaw (fun omega=>cdf law (threshold omega)) coverageLaw P) :
    let fraction := fun pair:Ω×(Fin 2000→ℝ)=>rawFraction (threshold pair.1) pair.2
    (∫pair,fraction pair ∂P.prod (rawTestLaw law))=9/10 ∧
      Var[fraction;P.prod (rawTestLaw law)]=303/70000 := by
  let C : Ω→ℝ:=fun omega=>cdf law (threshold omega)
  let fraction := fun pair:Ω×(Fin 2000→ℝ)=>rawFraction (threshold pair.1) pair.2
  have hraw : Measurable (fun pair:ℝ×(Fin 2000→ℝ)=>rawFraction pair.1 pair.2):=
    actual_variable_raw_test_fraction_is_measurable_and_bounded.1
  have hpair : Measurable (fun pair:Ω×(Fin 2000→ℝ)=>(threshold pair.1,pair.2)):=
    (hthreshold.comp measurable_fst).prodMk measurable_snd
  have hfrac : Measurable fraction:=by
    simpa only [Function.comp_def] using hraw.comp hpair
  have hbound : ∀pair:Ω×(Fin 2000→ℝ),fraction pair∈Icc (0:ℝ) 1:=by
    intro pair
    dsimp only [fraction]
    exact actual_variable_raw_test_fraction_is_measurable_and_bounded.2 (threshold pair.1) pair.2
  have hlp : MemLp fraction 2 (P.prod (rawTestLaw law)):=
    memLp_of_bounded (Filter.Eventually.of_forall hbound) hfrac.aestronglyMeasurable 2
  have hmean : (∫pair,fraction pair ∂P.prod (rawTestLaw law))=9/10:=by
    rw [integral_prod _ (hlp.integrable (by norm_num))]
    calc
      (∫omega,(∫tests,rawFraction (threshold omega) tests ∂rawTestLaw law) ∂P)=
          ∫omega,C omega ∂P:=by
        apply integral_congr_ae
        filter_upwards [] with omega
        exact (actual_iid_raw_tests_have_the_derived_conditional_binomial_law_and_moments law (threshold omega)).2.1
      _=∫c:ℝ,c ∂coverageLaw:=hcov.integral_eq
      _=9/10:=actual_beta_coverage_mean_variance_and_test_noise_moment.1
  have hsint : Integrable (fun pair=>(fraction pair)^2) (P.prod (rawTestLaw law)):=
    (memLp_two_iff_integrable_sq hlp.aestronglyMeasurable).mp hlp
  have hcint : Integrable (fun c:ℝ=>c) coverageLaw:=by
    simpa using actual_beta_all_natural_moments_are_integrable 1
  have hc2int:=actual_beta_all_natural_moments_are_integrable 2
  have htint : Integrable (fun c:ℝ=>c*(1-c)) coverageLaw:=by
    have h : (fun c:ℝ=>c*(1-c))=(fun c=>c-c^2):=by funext c;ring
    rw [h];exact hcint.sub hc2int
  have hsecond : (∫pair,(fraction pair)^2 ∂P.prod (rawTestLaw law))=57003/70000:=by
    rw [integral_prod _ hsint]
    calc
      (∫omega,(∫tests,(rawFraction (threshold omega) tests)^2 ∂rawTestLaw law) ∂P)=
          ∫omega,(C omega)^2+C omega*(1-C omega)/2000 ∂P:=by
        apply integral_congr_ae
        filter_upwards [] with omega
        exact (actual_iid_raw_tests_have_the_derived_conditional_binomial_law_and_moments law (threshold omega)).2.2
      _=∫c:ℝ,c^2+c*(1-c)/2000 ∂coverageLaw:=by
        exact hcov.integral_comp (f:=fun c:ℝ=>c^2+c*(1-c)/2000)
          (by fun_prop)
      _=57003/70000:=by
        rw [integral_add hc2int (htint.div_const 2000),integral_div,
          actual_beta_natural_moment_has_its_true_integral_value,
          actual_beta_coverage_mean_variance_and_test_noise_moment.2.2]
        norm_num
  refine ⟨hmean,?_⟩
  rw [variance_eq_sub hlp]
  change (∫pair,(fraction pair)^2 ∂P.prod (rawTestLaw law))-
      (∫pair,fraction pair ∂P.prod (rawTestLaw law))^2=303/70000
  rw [hsecond,hmean]
  norm_num

theorem actual_iid_continuous_calibration_and_fresh_test_measured_coverage_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (law : Measure ℝ) [IsProbabilityMeasure law] (hc : Continuous (cdf law))
    (scores : Fin 19→Ω→ℝ) (hm : ∀i,Measurable (scores i))
    (hind : iIndepFun scores P) (hlaw : ∀i,HasLaw (scores i) law P) :
    let fraction := fun pair:Ω×(Fin 2000→ℝ)=>
      rawFraction (secondLargest (fun i=>scores i pair.1)) pair.2
    (∫pair,fraction pair ∂P.prod (rawTestLaw law))=9/10 ∧
      Var[fraction;P.prod (rawTestLaw law)]=303/70000 := by
  exact actual_beta_distributed_calibration_coverage_derives_the_raw_test_mean_and_variance
    P law (fun omega=>secondLargest (fun i=>scores i omega))
    (actual_second_largest_of_measurable_coordinates_is_measurable scores hm)
    (actual_iid_arbitrary_continuous_score_cdf_coverage_has_the_genuine_beta_law
      P law hc scores hm hind hlaw)

theorem actual_iid_continuous_calibration_and_one_fresh_score_have_point_nine_marginal_coverage
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (law : Measure ℝ) [IsProbabilityMeasure law] (hc : Continuous (cdf law))
    (scores : Fin 19→Ω→ℝ) (hm : ∀i,Measurable (scores i))
    (hind : iIndepFun scores P) (hlaw : ∀i,HasLaw (scores i) law P) :
    (P.prod law).real {pair:Ω×ℝ|pair.2≤ secondLargest (fun i=>scores i pair.1)}=9/10 := by
  let threshold : Ω→ℝ:=fun omega=>secondLargest (fun i=>scores i omega)
  let accept : Set (Ω×ℝ):={pair|pair.2≤threshold pair.1}
  have hthreshold : Measurable threshold:=actual_second_largest_of_measurable_coordinates_is_measurable scores hm
  have ha : MeasurableSet accept:=measurableSet_le measurable_snd (hthreshold.comp measurable_fst)
  have hcov:=actual_iid_arbitrary_continuous_score_cdf_coverage_has_the_genuine_beta_law P law hc scores hm hind hlaw
  have hi : Integrable (accept.indicator (fun _=>(1:ℝ))) (P.prod law):=
    (integrable_const (1:ℝ)).indicator ha
  change (P.prod law).real accept=9/10
  rw [←integral_indicator_one ha]
  change (∫pair:Ω×ℝ,accept.indicator (fun _=>(1:ℝ)) pair ∂P.prod law)=9/10
  rw [integral_prod _ hi]
  calc
    (∫omega,(∫test:ℝ,accept.indicator (fun _=>(1:ℝ)) (omega,test) ∂law) ∂P)=
        ∫omega,cdf law (threshold omega) ∂P:=by
      apply integral_congr_ae
      filter_upwards [] with omega
      change (∫test:ℝ,(Iic (threshold omega)).indicator (fun _=>(1:ℝ)) test ∂law)=_
      exact (integral_indicator_one (μ:=law) (s:=Iic (threshold omega)) measurableSet_Iic).trans
        (cdf_eq_real law (threshold omega)).symm
    _=∫c:ℝ,c ∂coverageLaw:=hcov.integral_eq
    _=9/10:=actual_beta_coverage_mean_variance_and_test_noise_moment.1

end SafeLearning.CompleteAppliedCoverageScoreExperiment
