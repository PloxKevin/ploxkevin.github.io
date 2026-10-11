import SafeLearning.CompleteFoundationsIndependentTrials

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SafeLearning.CompleteLyapunovScenarioSupport23

def sampleMaximum {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty s

def sampledFeasible {ι : Type*} (s : ι → ℝ) : Set ℝ := {x | ∀ i, s i ≤ x}

/-- Removing this constraint genuinely permits a smaller objective value. -/
def supporting {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ) (i : ι) : Prop :=
  ∃ x : ℝ, (∀ j, j ≠ i → s j ≤ x) ∧ x < sampleMaximum s

theorem actual_scalar_scenario_optimizer_is_the_sample_maximum
    {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ) :
    IsLeast (sampledFeasible s) (sampleMaximum s) := by
  classical
  constructor
  · intro i
    exact Finset.le_sup' s (Finset.mem_univ i)
  · intro x hx
    exact (Finset.sup'_le_iff Finset.univ_nonempty s).mpr (fun i _ => hx i)

theorem actual_scalar_scenario_optimizer_is_unique
    {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ) (x : ℝ)
    (hx : IsLeast (sampledFeasible s) x) : x = sampleMaximum s :=
  hx.unique (actual_scalar_scenario_optimizer_is_the_sample_maximum s)

theorem actual_sample_maximum_is_attained_by_a_sample
    {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ) :
    ∃ i, sampleMaximum s = s i := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty s
  exact ⟨i, hi⟩

theorem actual_support_constraint_is_a_strict_unique_maximum
    {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ) (i : ι)
    (hi : supporting s i) : sampleMaximum s = s i ∧ ∀ j, j ≠ i → s j < s i := by
  obtain ⟨x, hx, hxm⟩ := hi
  obtain ⟨k, hk⟩ := actual_sample_maximum_is_attained_by_a_sample s
  have hki : k = i := by
    by_contra h
    have hle := hx k h
    rw [← hk] at hle
    exact (not_le_of_gt hxm) hle
  have he : sampleMaximum s = s i := hki ▸ hk
  refine ⟨he, ?_⟩
  intro j hj
  have hl := hx j hj
  rw [he] at hxm
  exact hl.trans_lt hxm

theorem actual_strict_unique_maximum_is_a_support_constraint
    {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ) (i : ι)
    (hi : ∀ j, j ≠ i → s j < s i) : supporting s i := by
  classical
  have hm : sampleMaximum s = s i := by
    apply le_antisymm
    · exact (Finset.sup'_le_iff Finset.univ_nonempty s).mpr (fun j _ => by
        by_cases hji : j = i
        · exact hji ▸ le_rfl
        · exact (hi j hji).le)
    · exact (actual_scalar_scenario_optimizer_is_the_sample_maximum s).1 i
  by_cases he : (Finset.univ.erase i : Finset ι).Nonempty
  · refine ⟨(Finset.univ.erase i).sup' he s, ?_, ?_⟩
    · intro j hj
      exact Finset.le_sup' s (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    · rw [hm]
      exact (Finset.sup'_lt_iff he).mpr (fun j hj => hi j (Finset.mem_erase.mp hj).1)
  · refine ⟨s i - 1, ?_, ?_⟩
    · intro j hj
      exact False.elim (he ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩)
    · rw [hm]
      linarith

theorem actual_at_most_one_sample_constraint_is_supporting
    {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ) :
    Set.Subsingleton {i | supporting s i} := by
  intro i hi j hj
  by_contra hij
  have hji := (actual_support_constraint_is_a_strict_unique_maximum s i hi).2 j (Ne.symm hij)
  have hij' := (actual_support_constraint_is_a_strict_unique_maximum s j hj).2 i hij
  exact (not_lt_of_ge hij'.le) hji

theorem actual_support_sample_count_is_at_most_one
    {ι : Type*} [Fintype ι] [Nonempty ι] (s : ι → ℝ)
    [DecidablePred (supporting s)] :
    (Finset.univ.filter (supporting s)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact actual_at_most_one_sample_constraint_is_supporting s
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem actual_sample_maximum_threshold_event_is_exactly_all_misses
    {Ω ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ) (q : ℝ) :
    {w | sampleMaximum (fun i => X i w) ≤ q} = ⋂ i, {w | q < X i w}ᶜ := by
  classical
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, not_lt,
    sampleMaximum, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

theorem actual_independent_scalar_scenario_threshold_failure_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) [NeZero n] (X : Fin n → Ω → ℝ) (q epsilon : ℝ)
    (hX : ∀ i, MeasurableSet {w | q < X i w})
    (hind : iIndepSet (fun i => {w | q < X i w}) P)
    (he : ∀ i, P.real {w | q < X i w} = epsilon)
    (hepsilon : epsilon ∈ Icc (0 : ℝ) 1) :
    P.real {w | sampleMaximum (fun i => X i w) ≤ q} = (1-epsilon)^n ∧
      P.real {w | sampleMaximum (fun i => X i w) ≤ q} ≤ Real.exp (-epsilon*n) := by
  rw [actual_sample_maximum_threshold_event_is_exactly_all_misses X q]
  exact CompleteFoundationsIndependentTrials.actual_independent_events_have_the_true_all_miss_probability_and_exponential_bound
    P n (fun i => {w | q < X i w}) epsilon hX hind hepsilon he

end SafeLearning.CompleteLyapunovScenarioSupport23
