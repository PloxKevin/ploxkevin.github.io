import SafeLearning.CompleteFoundationsNonnegativeSeriesModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace SafeLearning.CompleteFoundationsTelescopingModels
open CompleteFoundationsNonnegativeSeriesModels

theorem actual_arbitrary_additive_group_sequence_telescopes
    {E : Type*} [AddCommGroup E] (b : ℕ → E) (T : ℕ) :
    (∑ t ∈ Finset.range T, (b (t+1)-b t))=b T-b 0 := by
  induction T with
  | zero => simp
  | succ T ih => rw [Finset.sum_range_succ,ih]; abel

theorem actual_positive_reciprocal_product_is_the_difference
    (r : ℝ) (hr : 0 < r) : 1/(r*(r+1))=1/r-1/(r+1) := by
  field_simp
  ring

def failureShare (delta : ℝ) (n : ℕ) : ℝ :=
  delta/(((n:ℝ)+1)*((n:ℝ)+2))

theorem actual_failure_budget_partial_sum_has_the_exact_formula
    (delta : ℝ) (R : ℕ) :
    (∑ n ∈ Finset.range R, failureShare delta n)=
      delta*(1-1/((R:ℝ)+1)) := by
  have he (n : ℕ) : failureShare delta n=delta*actualTelescopingMajorant n := by
    unfold failureShare actualTelescopingMajorant
    ring
  simp_rw [he]
  rw [← Finset.mul_sum,actual_reciprocal_product_telescopes_at_every_horizon]

theorem actual_all_round_failure_shares_genuinely_sum_to_the_budget
    (delta : ℝ) : HasSum (failureShare delta) delta := by
  have hs := actual_reciprocal_product_series_has_sum_one.mul_left delta
  have he : (fun n => delta*actualTelescopingMajorant n)=failureShare delta := by
    funext n
    unfold failureShare actualTelescopingMajorant
    ring
  rw [he,mul_one] at hs
  exact hs

theorem actual_dependent_countable_failure_union_is_bounded_by_the_split_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (failure : ℕ → Set Ω) (delta : ℝ) (hd : 0 ≤ delta)
    (hbound : ∀ n,P.real (failure n)≤failureShare delta n) :
    P.real (⋃ n,failure n)≤delta := by
  have hs := actual_all_round_failure_shares_genuinely_sum_to_the_budget delta
  have hn (n : ℕ) : 0 ≤ failureShare delta n := by
    unfold failureShare
    positivity
  have hu : P (⋃ n,failure n)≤ENNReal.ofReal delta := by
    calc
      _ ≤ ∑' n,P (failure n) := measure_iUnion_le _
      _ ≤ ∑' n,ENNReal.ofReal (failureShare delta n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (hbound n)
      _ = ENNReal.ofReal delta := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hn hs.summable,hs.tsum_eq]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  simpa [measureReal_def,ENNReal.toReal_ofReal hd] using h

theorem actual_one_event_covering_every_round_has_the_true_probability_guarantee
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (failure : ℕ → Set Ω) (delta : ℝ) (hd : 0 ≤ delta)
    (hm : ∀ n,MeasurableSet (failure n))
    (hbound : ∀ n,P.real (failure n)≤failureShare delta n) :
    1-delta≤P.real (⋂ n,(failure n)ᶜ) := by
  have hb := actual_dependent_countable_failure_union_is_bounded_by_the_split_budget
    P failure delta hd hbound
  rw [← compl_iUnion,probReal_compl_eq_one_sub (MeasurableSet.iUnion hm)]
  linarith

theorem actual_dissipation_telescopes_to_both_literal_finite_horizon_bounds
    {E : Type*} [NormedAddCommGroup E] (state : ℕ → E) (target : E)
    (value : ℕ → ℝ) (epsilon : ℝ)
    (hvalue : ∀ n,0≤value n)
    (hstep : ∀ n,value (n+1)-value n≤ -epsilon*‖state n-target‖^2)
    (T : ℕ) :
    epsilon*(∑ n ∈ Finset.range T,‖state n-target‖^2)≤value 0-value T ∧
      value 0-value T≤value 0 := by
  have hs : value T+epsilon*(∑ n ∈ Finset.range T,‖state n-target‖^2)≤value 0 := by
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ,mul_add]
      linarith [hstep T]
  constructor <;> linarith [hvalue T]

end SafeLearning.CompleteFoundationsTelescopingModels
