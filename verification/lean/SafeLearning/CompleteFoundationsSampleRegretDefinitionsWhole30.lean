import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SafeLearning.CompleteFoundationsSampleRegretDefinitionsWhole30
open Set Filter Asymptotics MeasureTheory
open scoped Topology BigOperators

namespace SelectedRates
-- These definitions and this entire proof are copied from the selected
-- CompleteFoundationsRatesDomain source, read in full before reuse.
def cumulativeRegret (comparator : ℝ) (observations : ℕ→ℝ) (budget : ℕ) : ℝ :=
  ∑ index∈Finset.range budget,(comparator-observations index)

def simpleRegret (comparator recommendation : ℝ) : ℝ := comparator-recommendation

theorem actual_best_query_regret_le_average (comparator : ℝ) (observations : ℕ→ℝ)
    (budget : ℕ) (hb : 0<budget) :
    ∃ index<budget,simpleRegret comparator (observations index)≤
      cumulativeRegret comparator observations budget/budget := by
  classical
  by_contra h
  push Not at h
  have hsum : cumulativeRegret comparator observations budget<
      ∑ index∈Finset.range budget,simpleRegret comparator (observations index) := by
    have he : (∑ _index∈Finset.range budget,
      cumulativeRegret comparator observations budget/budget)=
      cumulativeRegret comparator observations budget := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      field_simp
    rw [←he]
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.nonempty_range_iff.mpr (by omega)
    · intro index hi
      exact h index (Finset.mem_range.mp hi)
  change cumulativeRegret comparator observations budget<cumulativeRegret comparator observations budget at hsum
  exact lt_irrefl _ hsum
end SelectedRates

def accuracyEvent {Ω : Type*} (estimate : ℕ → Ω → ℝ) (truth ε : ℝ) (n : ℕ) : Set Ω :=
  {ω | |estimate n ω-truth|≤ε}

def sampleGuarantee {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (estimate : ℕ → Ω → ℝ) (truth ε δ : ℝ) (n : ℕ) : Prop :=
  ENNReal.ofReal (1-δ)≤μ (accuracyEvent estimate truth ε n)

theorem actual_sample_complexity_guarantee_is_probability_of_accuracy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (estimate : ℕ → Ω → ℝ) (truth ε δ : ℝ) (n : ℕ) :
    sampleGuarantee μ estimate truth ε δ n ↔
      ENNReal.ofReal (1-δ)≤μ {ω | |estimate n ω-truth|≤ε} := Iff.rfl

theorem actual_accuracy_event_is_measurable {Ω : Type*} [MeasurableSpace Ω]
    (estimate : ℕ → Ω → ℝ) (truth ε : ℝ) (n : ℕ)
    (h : Measurable (estimate n)) : MeasurableSet (accuracyEvent estimate truth ε n) := by
  exact measurableSet_le ((h.sub_const truth).abs) measurable_const

theorem actual_sample_guarantee_monotone_in_accuracy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (estimate : ℕ → Ω → ℝ) (truth ε ε' δ : ℝ) (n : ℕ)
    (he : ε≤ε') (h : sampleGuarantee μ estimate truth ε δ n) :
    sampleGuarantee μ estimate truth ε' δ n := by
  apply h.trans (measure_mono ?_)
  intro ω hω
  exact hω.trans he

theorem actual_sample_guarantee_monotone_in_failure_tolerance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (estimate : ℕ → Ω → ℝ)
    (truth ε δ δ' : ℝ) (n : ℕ) (hd : δ≤δ')
    (h : sampleGuarantee μ estimate truth ε δ n) :
    sampleGuarantee μ estimate truth ε δ' n :=
  (ENNReal.ofReal_le_ofReal (by linarith : 1-δ'≤1-δ)).trans h

-- The number satisfying the guarantee is a definition, not an assertion that
-- any algorithm or any finite sample budget necessarily supplies a guarantee.
-- When such a budget exists, the least one below is an optional convention.
def leastSampleBudget {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (estimate : ℕ → Ω → ℝ) (truth ε δ : ℝ)
    (hex : ∃ n, sampleGuarantee μ estimate truth ε δ n) : ℕ := by
  classical
  exact Nat.find hex

theorem actual_existing_least_sample_budget_satisfies_guarantee
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (estimate : ℕ → Ω → ℝ)
    (truth ε δ : ℝ) (hex : ∃ n, sampleGuarantee μ estimate truth ε δ n) :
    sampleGuarantee μ estimate truth ε δ (leastSampleBudget μ estimate truth ε δ hex) := by
  classical
  exact Nat.find_spec hex

theorem actual_existing_least_sample_budget_is_least
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (estimate : ℕ → Ω → ℝ)
    (truth ε δ : ℝ) (hex : ∃ n, sampleGuarantee μ estimate truth ε δ n)
    (n : ℕ) (h : sampleGuarantee μ estimate truth ε δ n) :
    leastSampleBudget μ estimate truth ε δ hex≤n := by
  classical
  exact Nat.find_min' hex h

def sourceCumulativeRegret {X : Type*} (f : X → ℝ) (queries : ℕ → X)
    (comparator : X) (T : ℕ) : ℝ :=
  ∑ t∈Finset.Icc 1 T, (f comparator-f (queries t))

def sourceSimpleRegret {X : Type*} (f : X → ℝ) (comparator recommendation : X) : ℝ :=
  f comparator-f recommendation

theorem actual_literal_cumulative_regret {X : Type*} (f : X → ℝ)
    (queries : ℕ → X) (comparator : X) (T : ℕ) :
    sourceCumulativeRegret f queries comparator T=
      ∑ t∈Finset.Icc 1 T, (f comparator-f (queries t)) := rfl

theorem actual_literal_simple_regret {X : Type*} (f : X → ℝ)
    (comparator recommendation : X) :
    sourceSimpleRegret f comparator recommendation=f comparator-f recommendation := rfl

theorem actual_source_cumulative_regret_equals_selected_range_sum {X : Type*}
    (f : X → ℝ) (queries : ℕ → X) (comparator : X) (T : ℕ) :
    sourceCumulativeRegret f queries comparator T=
      SelectedRates.cumulativeRegret (f comparator) (fun i=>f (queries (i+1))) T := by
  unfold sourceCumulativeRegret SelectedRates.cumulativeRegret
  rw [←Finset.Ico_add_one_right_eq_Icc 1 T,Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

def queryRegretValues {X : Type*} (f : X → ℝ) (queries : ℕ → X)
    (comparator : X) (T : ℕ) : Finset ℝ := by
  classical
  exact (Finset.range T).image (fun i=>f comparator-f (queries (i+1)))

private theorem queryRegretValues_nonempty {X : Type*} (f : X → ℝ) (queries : ℕ → X)
    (comparator : X) (T : ℕ) (hT : 0<T) : (queryRegretValues f queries comparator T).Nonempty := by
  classical
  exact (Finset.nonempty_range_iff.mpr hT.ne').image _

def sourceBestQueryRegret {X : Type*} (f : X → ℝ) (queries : ℕ → X)
    (comparator : X) (T : ℕ) (hT : 0<T) : ℝ :=
  (queryRegretValues f queries comparator T).min' (queryRegretValues_nonempty f queries comparator T hT)

theorem actual_best_query_regret_is_attained_literal_minimum {X : Type*}
    (f : X → ℝ) (queries : ℕ → X) (comparator : X) (T : ℕ) (hT : 0<T) :
    (∃ t∈Finset.Icc 1 T,
      sourceBestQueryRegret f queries comparator T hT=f comparator-f (queries t)) ∧
    (∀ t∈Finset.Icc 1 T,
      sourceBestQueryRegret f queries comparator T hT≤f comparator-f (queries t)) := by
  classical
  constructor
  · have hm := (queryRegretValues f queries comparator T).min'_mem
      (queryRegretValues_nonempty f queries comparator T hT)
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
    refine ⟨i+1,Finset.mem_Icc.mpr ⟨by omega,by have := Finset.mem_range.mp hi;omega⟩,he.symm⟩
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    apply Finset.min'_le
    apply Finset.mem_image.mpr
    refine ⟨t-1,Finset.mem_range.mpr (by omega),?_⟩
    simp only [Nat.sub_add_cancel ht'.1]

theorem actual_literal_minimum_query_regret_le_cumulative_average {X : Type*}
    (f : X → ℝ) (queries : ℕ → X) (comparator : X) (T : ℕ) (hT : 0<T) :
    sourceBestQueryRegret f queries comparator T hT≤ sourceCumulativeRegret f queries comparator T/T := by
  classical
  obtain ⟨i,hi,havg⟩ := SelectedRates.actual_best_query_regret_le_average
    (f comparator) (fun i=>f (queries (i+1))) T hT
  have hmin := (actual_best_query_regret_is_attained_literal_minimum f queries comparator T hT).2
    (i+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  rw [actual_source_cumulative_regret_equals_selected_range_sum]
  exact hmin.trans havg

theorem actual_given_global_maximizer_gives_nonnegative_cumulative_and_simple_regret
    {X : Type*} (f : X → ℝ) (queries : ℕ → X) (comparator recommendation : X)
    (T : ℕ) (hmax : ∀ x, f x≤f comparator) :
    0≤ sourceCumulativeRegret f queries comparator T ∧
      0≤ sourceSimpleRegret f comparator recommendation := by
  constructor
  · exact Finset.sum_nonneg (fun t _=>sub_nonneg.mpr (hmax (queries t)))
  · exact sub_nonneg.mpr (hmax recommendation)

theorem actual_no_regret_little_o_iff_average_limit (R : ℕ → ℝ) :
    IsLittleO atTop R (fun T=>(T:ℝ)) ↔ Tendsto (fun T=>R T/T) atTop (𝓝 0) := by
  apply isLittleO_iff_tendsto'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with T hT
  have hp : (0:ℝ)<T := by exact_mod_cast (by omega : 0<T)
  exact fun hz=>False.elim (hp.ne' hz)

theorem actual_cumulative_no_regret_iff_literal_average_limit {X : Type*}
    (f : X → ℝ) (queries : ℕ → X) (comparator : X) :
    IsLittleO atTop (sourceCumulativeRegret f queries comparator) (fun T=>(T:ℝ)) ↔
      Tendsto (fun T=>sourceCumulativeRegret f queries comparator T/T) atTop (𝓝 0) :=
  actual_no_regret_little_o_iff_average_limit _
end SafeLearning.CompleteFoundationsSampleRegretDefinitionsWhole30
