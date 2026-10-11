import SafeLearning.CompleteModulesSafeOptConfidenceIntersections

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteFoundationsMonotoneApplications
open SafeLearning.CompleteModulesSafeOptConfidenceIntersections

theorem actual_successor_decrease_and_nonnegative_storage_derive_a_nonnegative_limit
    {X : Type*} (x : ℕ → X) (V : X → ℝ)
    (h0 : ∀ n, 0 ≤ V (x n)) (hstep : ∀ n, V (x (n+1)) ≤ V (x n)) :
    ∃ value : ℝ, 0 ≤ value ∧
      Antitone (fun n => V (x n)) ∧
      Tendsto (fun n => V (x n)) atTop (𝓝 value) := by
  have ha : Antitone (fun n => V (x n)) := antitone_nat_of_succ_le hstep
  have hb : BddBelow (range (fun n => V (x n))) := by
    refine ⟨0,?_⟩
    rintro v ⟨n,rfl⟩
    exact h0 n
  have ht := tendsto_atTop_ciInf ha hb
  exact ⟨sInf (range (fun n => V (x n))),
    ge_of_tendsto ht (Eventually.of_forall h0),ha,ht⟩

theorem actual_order_preserving_operator_and_a_prefixed_start_derive_decreasing_iterates
    {E : Type*} [Preorder E] (T : E → E) (hT : Monotone T)
    (initial : E) (hstart : T initial ≤ initial) :
    Antitone (fun n : ℕ => T^[n] initial) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => simpa using hstart
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using hT ih

def costBackup {S : Type*} [Fintype S] (P : S → S → ℝ)
    (c : S → ℝ) (W : S → ℝ) (s : S) : ℝ := c s + ∑ next, P s next * W next

theorem actual_nonnegative_transition_cost_backup_is_monotone
    {S : Type*} [Fintype S] (P : S → S → ℝ) (c : S → ℝ)
    (hP : ∀ s next, 0 ≤ P s next) : Monotone (costBackup P c) := by
  intro W Z h s
  change c s + (∑ next, P s next * W next) ≤ c s + (∑ next, P s next * Z next)
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro next _
  exact mul_le_mul_of_nonneg_left (h next) (hP s next)

theorem actual_nonnegative_cost_and_transition_preserve_nonnegative_values
    {S : Type*} [Fintype S] (P : S → S → ℝ) (c W : S → ℝ)
    (hP : ∀ s next, 0 ≤ P s next) (hc : ∀ s, 0 ≤ c s)
    (hW : ∀ s, 0 ≤ W s) : ∀ s, 0 ≤ costBackup P c W s := by
  intro s
  exact add_nonneg (hc s) (Finset.sum_nonneg (fun next _ => mul_nonneg (hP s next) (hW next)))

theorem actual_cost_lyapunov_start_generates_the_literal_decreasing_bellman_chain
    {S : Type*} [Fintype S] (P : S → S → ℝ) (c L : S → ℝ)
    (hP : ∀ s next, 0 ≤ P s next) (hc : ∀ s, 0 ≤ c s)
    (hL : ∀ s, 0 ≤ L s) (hprefixed : costBackup P c L ≤ L) :
    Antitone (fun n : ℕ => (costBackup P c)^[n] L) ∧
      (∀ n s, 0 ≤ ((costBackup P c)^[n] L) s) ∧
      ∀ s, ∃ value : ℝ, 0 ≤ value ∧
        Tendsto (fun n : ℕ => ((costBackup P c)^[n] L) s) atTop (𝓝 value) := by
  have ha := actual_order_preserving_operator_and_a_prefixed_start_derive_decreasing_iterates
    (costBackup P c) (actual_nonnegative_transition_cost_backup_is_monotone P c hP) L hprefixed
  have hnon : ∀ n s, 0 ≤ ((costBackup P c)^[n] L) s := by
    intro n
    induction n with
    | zero => simpa using hL
    | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using
        actual_nonnegative_cost_and_transition_preserve_nonnegative_values P c _ hP hc ih
  refine ⟨ha,hnon,?_⟩
  intro s
  have hb : BddBelow (range (fun n : ℕ => ((costBackup P c)^[n] L) s)) := by
    refine ⟨0,?_⟩
    rintro v ⟨n,rfl⟩
    exact hnon n s
  have ht := tendsto_atTop_ciInf (fun m n h => ha h s) hb
  exact ⟨_,ge_of_tendsto ht (Eventually.of_forall (fun n => hnon n s)),ht⟩

theorem actual_finite_decreasing_bounded_coordinate_family_has_uniform_limits
    {S : Type*} [Fintype S] (W : ℕ → S → ℝ) (lower : S → ℝ)
    (ha : ∀ s, Antitone (fun n => W n s)) (hb : ∀ n s, lower s ≤ W n s) :
    ∃ limit : S → ℝ, (∀ s, lower s ≤ limit s) ∧
      (∀ s, Tendsto (fun n => W n s) atTop (𝓝 (limit s))) ∧
      TendstoUniformly W limit atTop := by
  let limit : S → ℝ := fun s => sInf (range (fun n => W n s))
  have ht (s : S) : Tendsto (fun n => W n s) atTop (𝓝 (limit s)) := by
    apply tendsto_atTop_ciInf (ha s)
    refine ⟨lower s,?_⟩
    rintro v ⟨n,rfl⟩
    exact hb n s
  refine ⟨limit,fun s => ge_of_tendsto (ht s) (Eventually.of_forall (fun n => hb n s)),ht,?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro epsilon he
  have hall : ∀ s, ∀ᶠ n in atTop, dist (W n s) (limit s) < epsilon :=
    fun s => Metric.tendsto_nhds.mp (ht s) epsilon he
  simpa only [dist_comm] using eventually_all.mpr hall

theorem actual_confidence_endpoint_recursions_are_globally_monotone_and_antitone
    (firstLower firstUpper : ℝ) (rawLower rawUpper : ℕ → ℝ) :
    Monotone (actualLower firstLower rawLower) ∧
      Antitone (actualUpper firstUpper rawUpper) := by
  constructor
  · exact monotone_nat_of_le_succ (fun n =>
      (actual_intersected_lower_increases_upper_decreases_and_width_decreases
        firstLower firstUpper rawLower rawUpper n).1)
  · exact antitone_nat_of_succ_le (fun n =>
      (actual_intersected_lower_increases_upper_decreases_and_width_decreases
        firstLower firstUpper rawLower rawUpper n).2.1)

theorem actual_valid_intersections_derive_bounded_endpoint_limits_around_the_true_value
    (firstLower firstUpper value : ℝ) (rawLower rawUpper : ℕ → ℝ)
    (hfirst : firstLower ≤ value ∧ value ≤ firstUpper)
    (hraw : ∀ n, rawLower n ≤ value ∧ value ≤ rawUpper n) :
    ∃ lowerLimit upperLimit : ℝ,
      lowerLimit ≤ value ∧ value ≤ upperLimit ∧
      Tendsto (actualLower firstLower rawLower) atTop (𝓝 lowerLimit) ∧
      Tendsto (actualUpper firstUpper rawUpper) atTop (𝓝 upperLimit) := by
  have hbounds : ∀ n, actualLower firstLower rawLower n ≤ value ∧
      value ≤ actualUpper firstUpper rawUpper n := by
    intro n
    induction n with
    | zero => exact hfirst
    | succ n ih => exact ⟨max_le ih.1 (hraw n).1,le_min ih.2 (hraw n).2⟩
  obtain ⟨hm,ha⟩ := actual_confidence_endpoint_recursions_are_globally_monotone_and_antitone
    firstLower firstUpper rawLower rawUpper
  have hl := tendsto_atTop_ciSup hm
    (show BddAbove (range (actualLower firstLower rawLower)) from
      ⟨value,by rintro v ⟨n,rfl⟩;exact (hbounds n).1⟩)
  have hu := tendsto_atTop_ciInf ha
    (show BddBelow (range (actualUpper firstUpper rawUpper)) from
      ⟨value,by rintro v ⟨n,rfl⟩;exact (hbounds n).2⟩)
  exact ⟨_,_,le_of_tendsto hl (Eventually.of_forall (fun n => (hbounds n).1)),
    ge_of_tendsto hu (Eventually.of_forall (fun n => (hbounds n).2)),hl,hu⟩

end SafeLearning.CompleteFoundationsMonotoneApplications
