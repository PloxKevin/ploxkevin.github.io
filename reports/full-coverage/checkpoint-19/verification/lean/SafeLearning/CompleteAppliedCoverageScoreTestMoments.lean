import SafeLearning.CompleteAppliedCoverageContinuousTransform
import SafeLearning.CompleteAppliedCoverageFreshTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedCoverageScoreTestMoments
open CompleteAppliedBinomialModel CompleteAppliedFailureCounts

def rawTestLaw (law : Measure ℝ) : Measure (Fin 2000→ℝ):=Measure.pi (fun _=>law)
instance rawTestLaw_probability (law : Measure ℝ) [IsProbabilityMeasure law] :
    IsProbabilityMeasure (rawTestLaw law):=by unfold rawTestLaw;infer_instance
def rawCount (threshold : ℝ) (tests : Fin 2000→ℝ) : ℕ:=
  failureCount (fun i=>{tests:Fin 2000→ℝ|tests i≤threshold}) tests
def rawFraction (threshold : ℝ) (tests : Fin 2000→ℝ) : ℝ:=(rawCount threshold tests:ℝ)/2000

theorem actual_variable_raw_test_fraction_is_measurable_and_bounded :
    Measurable (fun pair:ℝ×(Fin 2000→ℝ)=>rawFraction pair.1 pair.2) ∧
      ∀threshold tests,rawFraction threshold tests∈Icc (0:ℝ) 1 := by
  have hm : Measurable (fun pair:ℝ×(Fin 2000→ℝ)=>rawCount pair.1 pair.2):=
    failure_count_measurable (fun i=>{pair:ℝ×(Fin 2000→ℝ)|pair.2 i≤pair.1})
      (fun i=>measurableSet_le ((measurable_pi_apply i).comp measurable_snd) measurable_fst)
  constructor
  · exact ((show Measurable (fun n:ℕ=>(n:ℝ)) from measurable_of_countable _).comp hm).div_const 2000
  · intro threshold tests
    have hn : rawCount threshold tests≤2000:=by
      unfold rawCount failureCount failedTrials
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hr : (rawCount threshold tests:ℝ)≤2000:=by exact_mod_cast hn
    constructor
    · unfold rawFraction;positivity
    · unfold rawFraction
      exact (div_le_one (by norm_num : (0:ℝ)<2000)).mpr hr

theorem actual_iid_raw_tests_have_the_derived_conditional_binomial_law_and_moments
    (law : Measure ℝ) [IsProbabilityMeasure law] (threshold : ℝ) :
    HasLaw (rawCount threshold)
      (binomial 2000 ⟨cdf law threshold,⟨cdf_nonneg law threshold,cdf_le_one law threshold⟩⟩)
      (rawTestLaw law) ∧
    (∫tests,rawFraction threshold tests ∂rawTestLaw law)=cdf law threshold ∧
    (∫tests,(rawFraction threshold tests)^2 ∂rawTestLaw law)=
      (cdf law threshold)^2+cdf law threshold*(1-cdf law threshold)/2000 := by
  let below : Fin 2000→Set (Fin 2000→ℝ):=fun i=>{tests|tests i≤threshold}
  have hm : ∀i,MeasurableSet (below i):=fun i=>measurableSet_le (measurable_pi_apply i) measurable_const
  have hi : iIndepFun (fun i:Fin 2000=>fun tests:Fin 2000→ℝ=>tests i) (rawTestLaw law):=
    iIndepFun_pi (μ:=fun _:Fin 2000=>law) (X:=fun _=>id) (fun _=>measurable_id.aemeasurable)
  have hind : iIndepSet below (rawTestLaw law):=by
    apply (iIndepSet_iff_meas_biInter hm).mpr
    intro S
    have h:=hi.measure_inter_preimage_eq_mul S (sets:=fun _=>Iic threshold)
      (fun _ _=>measurableSet_Iic)
    simpa only [below,Set.preimage,Set.mem_Iic] using h
  have hp : ∀i,(rawTestLaw law).real (below i)=cdf law threshold:=by
    intro i
    have h : HasLaw (fun tests:Fin 2000→ℝ=>tests i) law (rawTestLaw law):=
      (measurePreserving_eval (fun _:Fin 2000=>law) i).hasLaw
    exact (h.measureReal_eq measurableSet_Iic).trans (cdf_eq_real law threshold).symm
  have hcount:=actual_binomial_count_mean_and_variance (rawTestLaw law) 2000 below hm hind
    (cdf law threshold) hp
  refine ⟨actual_count_has_binomial_law (rawTestLaw law) 2000 below hm hind
    ⟨cdf law threshold,⟨cdf_nonneg law threshold,cdf_le_one law threshold⟩⟩ hp,?_⟩
  have hmean : (∫tests,rawFraction threshold tests ∂rawTestLaw law)=cdf law threshold:=by
    unfold rawFraction
    rw [integral_div]
    change (∫tests,(failureCount below tests:ℝ) ∂rawTestLaw law)/2000=cdf law threshold
    rw [hcount.1]
    norm_num
  have hlp : MemLp (rawFraction threshold) 2 (rawTestLaw law):=
    memLp_of_bounded (Filter.Eventually.of_forall
      (fun tests=>actual_variable_raw_test_fraction_is_measurable_and_bounded.2 threshold tests))
      ((actual_variable_raw_test_fraction_is_measurable_and_bounded.1.comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable) 2
  have hvar : Var[rawFraction threshold;rawTestLaw law]=
      cdf law threshold*(1-cdf law threshold)/2000:=by
    have he : rawFraction threshold=
        (fun tests=>(1/2000:ℝ)*(failureCount below tests:ℝ)):=by
      funext tests
      change (failureCount below tests:ℝ)/2000=(1/2000:ℝ)*(failureCount below tests:ℝ)
      ring
    rw [he,variance_const_mul,hcount.2]
    norm_num
    ring
  have hs:=variance_eq_sub hlp
  change Var[rawFraction threshold;rawTestLaw law]=
    (∫tests,(rawFraction threshold tests)^2 ∂rawTestLaw law)-
      (∫tests,rawFraction threshold tests ∂rawTestLaw law)^2 at hs
  rw [hmean,hvar] at hs
  exact ⟨hmean,by linarith⟩

end SafeLearning.CompleteAppliedCoverageScoreTestMoments
