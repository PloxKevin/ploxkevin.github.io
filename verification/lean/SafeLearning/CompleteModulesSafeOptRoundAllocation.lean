import SafeLearning.CompleteModulesSafeOptConfidenceIntersections

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace SafeLearning.CompleteModulesSafeOptRoundAllocation

def actualRoundBudget (delta : ℝ) (round : ℕ) : ℝ :=
  delta/(((round:ℝ)+1)*((round:ℝ)+2))

theorem actual_round_budgets_have_the_exact_telescoping_partial_sum
    (delta : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, actualRoundBudget delta k=delta-delta/((n:ℝ)+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    dsimp [actualRoundBudget]
    push_cast
    field_simp
    <;> ring

theorem actual_round_budgets_are_a_genuine_summable_allocation_of_delta
    (delta : ℝ) (hdelta : 0 ≤ delta) : HasSum (actualRoundBudget delta) delta := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by dsimp [actualRoundBudget];positivity) delta).mpr
  simp_rw [actual_round_budgets_have_the_exact_telescoping_partial_sum]
  have hz := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul delta
  simpa [div_eq_mul_inv] using tendsto_const_nhds.sub hz

theorem actual_per_round_bounds_give_one_joint_all_round_failure_bound
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) (bad : ℕ → Set Ω)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hbad : ∀ n, mu (bad n) ≤ ENNReal.ofReal (actualRoundBudget delta n)) :
    mu (⋃ n, bad n) ≤ ENNReal.ofReal delta := by
  have hs := actual_round_budgets_are_a_genuine_summable_allocation_of_delta delta hdelta
  calc
    _ ≤ ∑' n, mu (bad n) := measure_iUnion_le bad
    _ ≤ ∑' n, ENNReal.ofReal (actualRoundBudget delta n) := ENNReal.tsum_le_tsum hbad
    _ = ENNReal.ofReal delta := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => by dsimp [actualRoundBudget];positivity) hs.summable,hs.tsum_eq]

theorem actual_round_allocation_adds_the_exact_two_logarithmic_time_terms
    (delta : ℝ) (hdelta : 0 < delta) (n : ℕ) :
    Real.log (1/actualRoundBudget delta n)=
      Real.log (1/delta)+Real.log ((n:ℝ)+1)+Real.log ((n:ℝ)+2) := by
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  have hn2 : (n:ℝ)+2 ≠ 0 := by positivity
  have he : 1/actualRoundBudget delta n=(1/delta)*((n:ℝ)+1)*((n:ℝ)+2) := by
    dsimp [actualRoundBudget]
    field_simp
  rw [he,Real.log_mul (mul_ne_zero (by positivity) hn1) hn2,
    Real.log_mul (by positivity) hn1]

theorem actual_additional_log_penalty_is_bounded_above_and_below_by_log_time
    (n : ℕ) (hn : 2 ≤ n) :
    Real.log (n:ℝ) ≤ Real.log ((n:ℝ)+1)+Real.log ((n:ℝ)+2) ∧
      Real.log ((n:ℝ)+1)+Real.log ((n:ℝ)+2) ≤ 4*Real.log (n:ℝ) := by
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n:ℝ) := by linarith
  have hlog2 : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hnr
  have hlog1 : Real.log ((n:ℝ)+1) ≤ 2*Real.log (n:ℝ) := by
    have hh := Real.log_le_log (by positivity : 0 < (n:ℝ)+1) (show (n:ℝ)+1 ≤ 2*(n:ℝ) by linarith)
    rw [Real.log_mul (by norm_num) hpos.ne'] at hh
    linarith
  have hlognext : Real.log ((n:ℝ)+2) ≤ 2*Real.log (n:ℝ) := by
    have hh := Real.log_le_log (by positivity : 0 < (n:ℝ)+2) (show (n:ℝ)+2 ≤ 2*(n:ℝ) by linarith)
    rw [Real.log_mul (by norm_num) hpos.ne'] at hh
    linarith
  exact ⟨by
    have h1 := Real.log_le_log hpos (show (n:ℝ) ≤ (n:ℝ)+1 by linarith)
    have h2 := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith)
    linarith,by linarith⟩

theorem actual_tightened_upper_bound_decreases_the_literal_finite_expansion_cardinality
    {X : Type*} [Fintype X] (safe : Set X) (cost : X → X → ℝ)
    (oldUpper newUpper : X → ℝ) (threshold : ℝ) (anchor : X)
    (hu : newUpper anchor ≤ oldUpper anchor) :
    {candidate | candidate ∉ safe ∧ threshold ≤ newUpper anchor-cost anchor candidate}.ncard ≤
      {candidate | candidate ∉ safe ∧ threshold ≤ oldUpper anchor-cost anchor candidate}.ncard := by
  apply Set.ncard_le_ncard (ht := Set.toFinite _)
  rintro candidate ⟨hc,hcert⟩
  exact ⟨hc,by linarith⟩

end SafeLearning.CompleteModulesSafeOptRoundAllocation
