import SafeLearning.CompleteModulesSafeOptPracticeNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesSafeOptConfidenceIntersections
open SafeLearning.CompleteModulesSafeOptPracticeNumbers

def actualConfidence {X : Type*} (seed : Set X) (threshold : ℝ)
    (raw : ℕ → X → Set ℝ) (n : ℕ) (x : X) : Set ℝ := by
  classical
  exact (if x ∈ seed then Ici threshold else univ) ∩ {value | ∀ i<n, value ∈ raw (i+1) x}

theorem actual_one_joint_confidence_event_and_seed_safety_preserve_every_intersection
    {X : Type*} (f : X → ℝ) (seed : Set X) (threshold : ℝ)
    (raw : ℕ → X → Set ℝ) (hraw : ∀ i x, f x ∈ raw (i+1) x)
    (hseed : ∀ x ∈ seed, threshold ≤ f x) :
    ∀ n x, f x ∈ actualConfidence seed threshold raw n x := by
  classical
  intro n x
  constructor
  · by_cases hx : x ∈ seed
    · simpa [hx] using hseed x hx
    · simp [hx]
  · exact fun i _ => hraw i x

theorem actual_next_confidence_set_is_exactly_the_previous_set_intersected_with_the_new_band
    {X : Type*} (seed : Set X) (threshold : ℝ) (raw : ℕ → X → Set ℝ)
    (n : ℕ) (x : X) :
    actualConfidence seed threshold raw (n+1) x=actualConfidence seed threshold raw n x ∩ raw (n+1) x := by
  classical
  ext value
  simp only [actualConfidence,mem_inter_iff,mem_setOf_eq]
  constructor
  · intro h
    exact ⟨⟨h.1,fun i hi => h.2 i (Nat.lt_succ_of_lt hi)⟩,h.2 n (Nat.lt_succ_self n)⟩
  · intro h
    refine ⟨h.1.1,?_⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact h.1.2 i hi
    · simpa [hi] using h.2

def actualLower (first : ℝ) (rawLower : ℕ → ℝ) : ℕ → ℝ
  | 0 => first
  | n+1 => max (actualLower first rawLower n) (rawLower n)
def actualUpper (first : ℝ) (rawUpper : ℕ → ℝ) : ℕ → ℝ
  | 0 => first
  | n+1 => min (actualUpper first rawUpper n) (rawUpper n)
def actualInterval (firstLower firstUpper : ℝ) (rawLower rawUpper : ℕ → ℝ) : ℕ → Set ℝ
  | 0 => Icc firstLower firstUpper
  | n+1 => actualInterval firstLower firstUpper rawLower rawUpper n ∩ Icc (rawLower n) (rawUpper n)

theorem actual_finite_confidence_intersection_has_the_literal_max_lower_min_upper_endpoints
    (firstLower firstUpper : ℝ) (rawLower rawUpper : ℕ → ℝ) :
    ∀ n, actualInterval firstLower firstUpper rawLower rawUpper n=
      Icc (actualLower firstLower rawLower n) (actualUpper firstUpper rawUpper n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change actualInterval firstLower firstUpper rawLower rawUpper n ∩ Icc (rawLower n) (rawUpper n)=_
    rw [ih,actual_closed_interval_intersection_is_the_max_min_endpoint_interval]
    rfl

theorem actual_intersected_lower_increases_upper_decreases_and_width_decreases
    (firstLower firstUpper : ℝ) (rawLower rawUpper : ℕ → ℝ) (n : ℕ) :
    actualLower firstLower rawLower n ≤ actualLower firstLower rawLower (n+1) ∧
      actualUpper firstUpper rawUpper (n+1) ≤ actualUpper firstUpper rawUpper n ∧
      actualUpper firstUpper rawUpper (n+1)-actualLower firstLower rawLower (n+1) ≤
        actualUpper firstUpper rawUpper n-actualLower firstLower rawLower n := by
  have hl := le_max_left (actualLower firstLower rawLower n) (rawLower n)
  have hu := min_le_left (actualUpper firstUpper rawUpper n) (rawUpper n)
  exact ⟨hl,hu,by change min _ _-max _ _≤_; linarith⟩

def actualMaximizers {X : Type*} (safe : Set X) (lower upper : X → ℝ) : Set X :=
  {x | x ∈ safe ∧ ∀ y ∈ safe, lower y ≤ upper x}
def actualExpanders {X : Type*} (safe : Set X) (upper : X → ℝ)
    (cost : X → X → ℝ) (threshold : ℝ) : Set X :=
  {x | x ∈ safe ∧ ∃ y ∉ safe, threshold ≤ upper x-cost x y}

theorem actual_source_maximizer_condition_is_equivalent_to_the_actual_attained_best_lower_bound
    {X : Type*} (safe : Set X) (lower upper : X → ℝ) (best : ℝ)
    (hbest : IsGreatest (lower '' safe) best) (x : X) :
    x ∈ actualMaximizers safe lower upper ↔ x ∈ safe ∧ best ≤ upper x := by
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := hbest.1
    exact ⟨h.1,he ▸ h.2 y hy⟩
  · intro h
    exact ⟨h.1,fun y hy => (hbest.2 ⟨y,hy,rfl⟩).trans h.2⟩

theorem actual_constant_safe_stage_candidates_shrink_when_intersected_endpoints_tighten
    {X : Type*} (safe : Set X) (oldLower oldUpper newLower newUpper : X → ℝ)
    (cost : X → X → ℝ) (threshold : ℝ)
    (hl : ∀ x, oldLower x ≤ newLower x) (hu : ∀ x, newUpper x ≤ oldUpper x) :
    actualMaximizers safe newLower newUpper ⊆ actualMaximizers safe oldLower oldUpper ∧
      actualExpanders safe newUpper cost threshold ⊆ actualExpanders safe oldUpper cost threshold ∧
      actualExpanders safe newUpper cost threshold ∪ actualMaximizers safe newLower newUpper ⊆
        actualExpanders safe oldUpper cost threshold ∪ actualMaximizers safe oldLower oldUpper := by
  have hm : actualMaximizers safe newLower newUpper ⊆ actualMaximizers safe oldLower oldUpper := by
    intro x hx
    exact ⟨hx.1,fun y hy => (hl y).trans ((hx.2 y hy).trans (hu x))⟩
  have hg : actualExpanders safe newUpper cost threshold ⊆ actualExpanders safe oldUpper cost threshold := by
    rintro x ⟨hx,y,hy,hc⟩
    refine ⟨hx,y,hy,?_⟩
    have h := hu x
    linarith
  exact ⟨hm,hg,union_subset_union hg hm⟩

theorem actual_next_maximum_width_query_cannot_exceed_the_current_maximum_width_within_a_stage
    {X : Type*} (oldCandidates newCandidates : Set X) (oldWidth newWidth : X → ℝ)
    (oldQuery newQuery : X) (hsub : newCandidates ⊆ oldCandidates)
    (hw : ∀ x, newWidth x ≤ oldWidth x) (hq : newQuery ∈ newCandidates)
    (hmax : ∀ x ∈ oldCandidates, oldWidth x ≤ oldWidth oldQuery) :
    newWidth newQuery ≤ oldWidth oldQuery := (hw newQuery).trans (hmax newQuery (hsub hq))

def sourceLower (round : Fin 3) (point : Fin 2) : ℝ :=
  if round=0 then (1/5) else if round=1 then ![9/10,1/5] point else ![3/4,1/5] point
def sourceUpper (round : Fin 3) (point : Fin 2) : ℝ :=
  if round=0 then (6/5) else if round=1 then ![6/5,4/5] point else ![1,4/5] point
def sourceIntersectedLower (point : Fin 2) : ℝ := max (sourceLower 1 point) (sourceLower 2 point)
def sourceIntersectedUpper (point : Fin 2) : ℝ := min (sourceUpper 1 point) (sourceUpper 2 point)
def sourceTrueValue (point : Fin 2) : ℝ := ![19/20,1/2] point

theorem actual_source_raw_band_example_contains_the_same_true_values_at_every_round :
    ∀ round point, sourceLower round point ≤ sourceTrueValue point ∧ sourceTrueValue point ≤ sourceUpper round point := by
  intro round point
  fin_cases round <;> fin_cases point <;> norm_num [sourceLower,sourceUpper,sourceTrueValue]

theorem actual_source_without_intersection_b_leaves_and_reenters_but_intersection_keeps_it_out :
    (1:Fin 2) ∈ actualMaximizers univ (sourceLower 0) (sourceUpper 0) ∧
      (1:Fin 2) ∉ actualMaximizers univ (sourceLower 1) (sourceUpper 1) ∧
      (1:Fin 2) ∈ actualMaximizers univ (sourceLower 2) (sourceUpper 2) ∧
      (1:Fin 2) ∉ actualMaximizers univ sourceIntersectedLower sourceIntersectedUpper := by
  norm_num [actualMaximizers,sourceLower,sourceUpper,sourceIntersectedLower,sourceIntersectedUpper,Fin.forall_fin_succ]

theorem actual_source_band_means_and_decreasing_spreads_and_failing_stage_square_sum_bound :
    ((9/10:ℝ)+6/5)/2=21/20 ∧ ((6/5:ℝ)-9/10)/2=3/20 ∧
      ((3/4:ℝ)+1)/2=7/8 ∧ ((1:ℝ)-3/4)/2=1/8 ∧ (1/8:ℝ)<3/20 ∧
      sourceUpper 1 0-sourceLower 1 0=3/10 ∧ sourceUpper 2 1-sourceLower 2 1=3/5 ∧
      (sourceUpper 1 0-sourceLower 1 0)^2+(sourceUpper 2 1-sourceLower 2 1)^2 <
        2*(sourceUpper 2 1-sourceLower 2 1)^2 := by norm_num [sourceUpper,sourceLower]

theorem actual_nonincreasing_nonnegative_stage_widths_imply_the_literal_square_sum_bound
    (width : ℕ → ℝ) (n : ℕ) (hnon : 0 ≤ width n) (hstage : ∀ j<n, width n ≤ width j) :
    (n:ℝ)*(width n)^2 ≤ ∑ j∈Finset.range n, (width j)^2 := by
  have hs : ∑ _j∈Finset.range n, (width n)^2 ≤ ∑ j∈Finset.range n, (width j)^2 := by
    apply Finset.sum_le_sum
    intro j hj
    have h := hstage j (Finset.mem_range.mp hj)
    exact pow_le_pow_left₀ hnon h 2
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hs

end SafeLearning.CompleteModulesSafeOptConfidenceIntersections
