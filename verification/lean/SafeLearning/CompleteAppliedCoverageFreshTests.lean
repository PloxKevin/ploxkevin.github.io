import SafeLearning.CompleteAppliedCoverageUniformLaw
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedCoverageFreshTests
open CompleteAppliedCoverageBeta CompleteAppliedCoverageUniformLaw
open CompleteAppliedUniformDefinitions CompleteAppliedBinomialModel CompleteAppliedFailureCounts

def unitLaw : Measure ℝ:=actualUniformLaw 0 1
instance unitLaw_probability : IsProbabilityMeasure unitLaw:=
  actual_uniform_law_is_a_probability_measure 0 1 (by norm_num)
def testLaw : Measure (Fin 2000→ℝ):=Measure.pi (fun _=>unitLaw)
instance testLaw_probability : IsProbabilityMeasure testLaw:=by unfold testLaw;infer_instance
def experimentLaw : Measure (ℝ×(Fin 2000→ℝ)):=coverageLaw.prod testLaw
instance experimentLaw_probability : IsProbabilityMeasure experimentLaw:=by unfold experimentLaw;infer_instance

def freshCount (c : ℝ) (tests : Fin 2000→ℝ) : ℕ:=
  failureCount (fun i=>{tests:Fin 2000→ℝ|tests i<c}) tests
def measuredCoverage (pair : ℝ×(Fin 2000→ℝ)) : ℝ:= (freshCount pair.1 pair.2:ℝ)/2000

theorem actual_measured_test_coverage_is_measurable_and_between_zero_and_one :
    Measurable measuredCoverage ∧ ∀pair,measuredCoverage pair∈Icc (0:ℝ) 1 := by
  have hm : Measurable (fun pair:ℝ×(Fin 2000→ℝ)=>freshCount pair.1 pair.2):=
    failure_count_measurable (fun i=>{pair:ℝ×(Fin 2000→ℝ)|pair.2 i<pair.1})
      (fun i=>measurableSet_lt ((measurable_pi_apply i).comp measurable_snd) measurable_fst)
  constructor
  · exact ((show Measurable (fun n:ℕ=>(n:ℝ)) from measurable_of_countable _).comp hm).div_const 2000
  · intro pair
    have hn : freshCount pair.1 pair.2≤2000:=by
      unfold freshCount failureCount failedTrials
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hr : (freshCount pair.1 pair.2:ℝ)≤2000:=by exact_mod_cast hn
    constructor
    · unfold measuredCoverage;positivity
    · unfold measuredCoverage
      exact (div_le_one (by norm_num : (0:ℝ)<2000)).mpr hr

theorem actual_every_fixed_coverage_has_a_derived_binomial_fresh_test_count
    (c : unitInterval) : HasLaw (freshCount c) (binomial 2000 c) testLaw := by
  let below : Fin 2000→Set (Fin 2000→ℝ):=fun i=>{tests|tests i<(c:ℝ)}
  have hm : ∀i,MeasurableSet (below i):=fun i=>measurableSet_lt (measurable_pi_apply i) measurable_const
  have hi : iIndepFun (fun i:Fin 2000=>fun tests:Fin 2000→ℝ=>tests i) testLaw:=
    iIndepFun_pi (μ:=fun _:Fin 2000=>unitLaw) (X:=fun _=>id) (fun _=>measurable_id.aemeasurable)
  have hind : iIndepSet below testLaw:=by
    apply (iIndepSet_iff_meas_biInter hm).mpr
    intro S
    have h:=hi.measure_inter_preimage_eq_mul S (sets:=fun _=>Iio (c:ℝ))
      (fun _ _=>measurableSet_Iio)
    simpa only [below,Set.preimage,Set.mem_Iio] using h
  have hp : ∀i,testLaw.real (below i)=(c:ℝ):=by
    intro i
    have h : HasLaw (fun tests:Fin 2000→ℝ=>tests i) unitLaw testLaw:=
      (measurePreserving_eval (fun _:Fin 2000=>unitLaw) i).hasLaw
    exact (h.measureReal_eq measurableSet_Iio).trans
      (actual_unit_uniform_strict_cdf c c.property)
  exact actual_count_has_binomial_law testLaw 2000 below hm hind c hp

theorem actual_fixed_coverage_test_fraction_has_the_conditional_mean_and_second_moment
    (c : unitInterval) :
    (∫tests,measuredCoverage (c,tests) ∂testLaw)=(c:ℝ) ∧
      (∫tests,(measuredCoverage (c,tests))^2 ∂testLaw)=c^2+c*(1-c)/2000 := by
  let below : Fin 2000→Set (Fin 2000→ℝ):=fun i=>{tests|tests i<(c:ℝ)}
  have hm : ∀i,MeasurableSet (below i):=fun i=>measurableSet_lt (measurable_pi_apply i) measurable_const
  have hi : iIndepFun (fun i:Fin 2000=>fun tests:Fin 2000→ℝ=>tests i) testLaw:=
    iIndepFun_pi (μ:=fun _:Fin 2000=>unitLaw) (X:=fun _=>id) (fun _=>measurable_id.aemeasurable)
  have hind : iIndepSet below testLaw:=by
    apply (iIndepSet_iff_meas_biInter hm).mpr
    intro S
    have h:=hi.measure_inter_preimage_eq_mul S (sets:=fun _=>Iio (c:ℝ))
      (fun _ _=>measurableSet_Iio)
    simpa only [below,Set.preimage,Set.mem_Iio] using h
  have hp : ∀i,testLaw.real (below i)=(c:ℝ):=by
    intro i
    have h : HasLaw (fun tests:Fin 2000→ℝ=>tests i) unitLaw testLaw:=
      (measurePreserving_eval (fun _:Fin 2000=>unitLaw) i).hasLaw
    exact (h.measureReal_eq measurableSet_Iio).trans
      (actual_unit_uniform_strict_cdf c c.property)
  have hcount:=actual_binomial_count_mean_and_variance testLaw 2000 below hm hind c hp
  have hmean : (∫tests,measuredCoverage (c,tests) ∂testLaw)=(c:ℝ):=by
    unfold measuredCoverage
    rw [integral_div]
    change (∫tests,(failureCount below tests:ℝ) ∂testLaw)/2000=(c:ℝ)
    rw [hcount.1]
    norm_num
  have hlp : MemLp (fun tests=>measuredCoverage (c,tests)) 2 testLaw:=
    memLp_of_bounded (Filter.Eventually.of_forall
      (fun tests=>actual_measured_test_coverage_is_measurable_and_between_zero_and_one.2 (c,tests)))
      ((actual_measured_test_coverage_is_measurable_and_between_zero_and_one.1.comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable) 2
  have hvar : Var[fun tests=>measuredCoverage (c,tests);testLaw]=c*(1-c)/2000:=by
    have he : (fun tests=>measuredCoverage (c,tests))=
        (fun tests=>(1/2000:ℝ)*(failureCount below tests:ℝ)):=by
      funext tests
      change (failureCount below tests:ℝ)/2000=(1/2000:ℝ)*(failureCount below tests:ℝ)
      ring
    rw [he,variance_const_mul,hcount.2]
    norm_num
    ring
  have hs:=variance_eq_sub hlp
  change Var[fun tests=>measuredCoverage (c,tests);testLaw]=
    (∫tests,(measuredCoverage (c,tests))^2 ∂testLaw)-
      (∫tests,measuredCoverage (c,tests) ∂testLaw)^2 at hs
  rw [hmean,hvar] at hs
  exact ⟨hmean,by linarith⟩

theorem actual_beta_coverage_is_almost_surely_in_the_unit_interval :
    ∀ᵐc:ℝ∂coverageLaw,c∈Icc (0:ℝ) 1 := by
  unfold coverageLaw betaMeasure
  rw [ae_withDensity_iff (show Measurable (betaPDF 18 2) from (measurable_betaPDFReal 18 2).ennreal_ofReal)]
  apply Filter.Eventually.of_forall
  intro c hn
  by_contra hc
  have hnot : ¬(0<c∧c<1):=fun h=>hc ⟨h.1.le,h.2.le⟩
  simp [betaPDF,betaPDFReal,hnot] at hn

theorem actual_fresh_test_product_experiment_derives_its_mean_and_variance :
    (∫pair,measuredCoverage pair ∂experimentLaw)=9/10 ∧
      Var[measuredCoverage;experimentLaw]=303/70000 := by
  have hlp : MemLp measuredCoverage 2 experimentLaw:=
    memLp_of_bounded (Filter.Eventually.of_forall
      actual_measured_test_coverage_is_measurable_and_between_zero_and_one.2)
      actual_measured_test_coverage_is_measurable_and_between_zero_and_one.1.aestronglyMeasurable 2
  have hm : (∫pair,measuredCoverage pair ∂experimentLaw)=9/10:=by
    rw [experimentLaw,integral_prod _ (hlp.integrable (by norm_num))]
    calc
      (∫c,(∫tests,measuredCoverage (c,tests) ∂testLaw) ∂coverageLaw)=
          ∫c:ℝ,c ∂coverageLaw:=by
        apply integral_congr_ae
        filter_upwards [actual_beta_coverage_is_almost_surely_in_the_unit_interval] with c hc
        exact (actual_fixed_coverage_test_fraction_has_the_conditional_mean_and_second_moment ⟨c,hc⟩).1
      _=9/10:=actual_beta_coverage_mean_variance_and_test_noise_moment.1
  have hsint : Integrable (fun pair=>(measuredCoverage pair)^2) experimentLaw:=
    (memLp_two_iff_integrable_sq hlp.aestronglyMeasurable).mp hlp
  have hcint : Integrable (fun c:ℝ=>c) coverageLaw:=by
    simpa using actual_beta_all_natural_moments_are_integrable 1
  have hc2int:=actual_beta_all_natural_moments_are_integrable 2
  have htint : Integrable (fun c:ℝ=>c*(1-c)) coverageLaw:=by
    have h : (fun c:ℝ=>c*(1-c))=(fun c=>c-c^2):=by funext c;ring
    rw [h];exact hcint.sub hc2int
  have hs : (∫pair,(measuredCoverage pair)^2 ∂experimentLaw)=57003/70000:=by
    rw [experimentLaw,integral_prod _ hsint]
    calc
      (∫c,(∫tests,(measuredCoverage (c,tests))^2 ∂testLaw) ∂coverageLaw)=
          ∫c:ℝ,c^2+c*(1-c)/2000 ∂coverageLaw:=by
        apply integral_congr_ae
        filter_upwards [actual_beta_coverage_is_almost_surely_in_the_unit_interval] with c hc
        exact (actual_fixed_coverage_test_fraction_has_the_conditional_mean_and_second_moment ⟨c,hc⟩).2
      _=57003/70000:=by
        rw [integral_add hc2int (htint.div_const 2000),integral_div,
          actual_beta_natural_moment_has_its_true_integral_value,
          actual_beta_coverage_mean_variance_and_test_noise_moment.2.2]
        norm_num
  refine ⟨hm,?_⟩
  rw [variance_eq_sub hlp]
  change (∫pair,(measuredCoverage pair)^2 ∂experimentLaw)-
      (∫pair,measuredCoverage pair ∂experimentLaw)^2=303/70000
  rw [hs,hm]
  norm_num

end SafeLearning.CompleteAppliedCoverageFreshTests
