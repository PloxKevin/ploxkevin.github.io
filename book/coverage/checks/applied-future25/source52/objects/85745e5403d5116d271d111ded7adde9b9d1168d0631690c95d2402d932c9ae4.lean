import SafeLearning.CompleteModulesLandscapeFiniteCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
namespace SafeLearning.CompleteModulesLandscapeDiscountedConverse
open CompleteModulesLandscapeFiniteCounts
variable {Ω : Type*} [MeasurableSpace Ω]

def infiniteFailureEvent (events : ℕ→Set Ω) : Set Ω := ⋃ time,events time
def discountedPathCost (gamma : ℝ) (events : ℕ→Set Ω) (ω : Ω) : ℝ :=
  ∑'time : ℕ,gamma^time*stepCost (events time) ω

theorem actual_every_infinite_indicator_path_has_summable_discounted_cost
    (gamma : ℝ) (hgamma : 0<gamma) (hgamma1 : gamma<1) (events : ℕ→Set Ω) (ω : Ω) :
    Summable (fun time : ℕ=>gamma^time*stepCost (events time) ω) := by
  classical
  have geometric : Summable (fun time : ℕ=>gamma^time) :=
    summable_geometric_of_abs_lt_one (by rwa [abs_of_pos hgamma])
  apply Summable.of_nonneg_of_le (f:=fun time : ℕ=>gamma^time) _ _ geometric
  · intro time;by_cases h : ω∈events time <;> simp [stepCost,Set.indicator,h] <;> positivity
  · intro time;by_cases h : ω∈events time <;> simp [stepCost,Set.indicator,h] <;> positivity

theorem actual_discounted_path_cost_is_bounded_by_the_event_indicator_geometric_sum
    (gamma : ℝ) (hgamma : 0<gamma) (hgamma1 : gamma<1) (events : ℕ→Set Ω) (ω : Ω) :
    0≤ discountedPathCost gamma events ω ∧
      discountedPathCost gamma events ω≤ (1/(1-gamma))*stepCost (infiniteFailureEvent events) ω := by
  classical
  have geometric : Summable (fun time : ℕ=>gamma^time) :=
    summable_geometric_of_abs_lt_one (by rwa [abs_of_pos hgamma])
  constructor
  · apply tsum_nonneg
    intro time;by_cases h : ω∈events time <;> simp [stepCost,Set.indicator,h] <;> positivity
  · by_cases h : ω∈infiniteFailureEvent events
    · rw [(actual_step_cost_is_the_zero_one_source_indicator _ _).1 h,mul_one]
      have hd := actual_every_infinite_indicator_path_has_summable_discounted_cost gamma hgamma hgamma1 events ω
      have hc : ∀ time : ℕ,gamma^time*stepCost (events time) ω≤ gamma^time := by
        intro time;by_cases ht : ω∈events time <;> simp [stepCost,Set.indicator,ht] <;> positivity
      have ht := hd.tsum_le_tsum hc geometric
      rw [tsum_geometric_of_abs_lt_one (by rwa [abs_of_pos hgamma])] at ht
      simpa [discountedPathCost,one_div] using ht
    · have he (time : ℕ) : ω∉events time := by
        intro ht;exact h (mem_iUnion.mpr ⟨time,ht⟩)
      simp [discountedPathCost,stepCost,Set.indicator,he,h]

theorem actual_all_horizon_discounted_indicator_sum_is_integrable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (gamma : ℝ) (hgamma : 0<gamma) (hgamma1 : gamma<1)
    (events : ℕ→Set Ω) (hmeas : ∀ time,MeasurableSet (events time)) :
    Integrable (discountedPathCost gamma events) P := by
  have hm : Measurable (discountedPathCost gamma events) :=
    Measurable.tsum (fun time=>measurable_const.mul ((measurable_const (a:=(1:ℝ))).indicator (hmeas time)))
  apply Integrable.mono_nonneg (integrable_const (1/(1-gamma):ℝ)) hm.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω=>(actual_discounted_path_cost_is_bounded_by_the_event_indicator_geometric_sum gamma hgamma hgamma1 events ω).1)
  · apply Filter.Eventually.of_forall
    intro ω
    have hb := (actual_discounted_path_cost_is_bounded_by_the_event_indicator_geometric_sum gamma hgamma hgamma1 events ω).2
    have hi : stepCost (infiniteFailureEvent events) ω≤1 := by
      classical
      by_cases h : ω∈infiniteFailureEvent events <;> simp [stepCost,Set.indicator,h]
    exact hb.trans (by simpa using mul_le_mul_of_nonneg_left hi (by positivity : (0:ℝ)≤1/(1-gamma)))

theorem actual_eventual_failure_chance_budget_bounds_the_true_infinite_discounted_expectation
    (P : Measure Ω) [IsProbabilityMeasure P]
    (gamma delta : ℝ) (hgamma : 0<gamma) (hgamma1 : gamma<1)
    (events : ℕ→Set Ω) (hmeas : ∀ time,MeasurableSet (events time))
    (hchance : P.real (infiniteFailureEvent events)≤ delta) :
    (∫ ω,discountedPathCost gamma events ω ∂P)≤ delta/(1-gamma) := by
  have hs := actual_all_horizon_discounted_indicator_sum_is_integrable P gamma hgamma hgamma1 events hmeas
  have he : Integrable (stepCost (infiniteFailureEvent events)) P :=
    (integrable_const (1:ℝ)).indicator (MeasurableSet.iUnion hmeas)
  have hi := integral_mono hs (he.const_mul (1/(1-gamma):ℝ))
    (fun ω=>(actual_discounted_path_cost_is_bounded_by_the_event_indicator_geometric_sum gamma hgamma hgamma1 events ω).2)
  have hprob : (∫ ω,stepCost (infiniteFailureEvent events) ω ∂P)=P.real (infiniteFailureEvent events) :=
    integral_indicator_one (MeasurableSet.iUnion hmeas)
  rw [integral_const_mul,hprob] at hi
  have hb := mul_le_mul_of_nonneg_left hchance (by positivity : (0:ℝ)≤1/(1-gamma))
  have hmul : (1/(1-gamma):ℝ)*delta=delta/(1-gamma) := by ring
  rw [hmul] at hb
  exact hi.trans hb

end SafeLearning.CompleteModulesLandscapeDiscountedConverse
