import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedConformalRanks
open Set Filter MeasureTheory
open scoped BigOperators Topology

variable {n : ℕ}

/-- Zero-based strict rank of an actual coordinate among all finite scores. -/
def rankNat (scores : Fin n → ℝ) (index : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => scores j < scores index)).card

theorem actual_rank_is_less_than_sample_size (scores : Fin n → ℝ) (index : Fin n) :
    rankNat scores index < n := by
  have hs : Finset.univ.filter (fun j => scores j < scores index) ⊂ Finset.univ := by
    refine ⟨Finset.filter_subset _ _,?_⟩
    intro hall
    have h := hall (Finset.mem_univ index)
    simp at h
  simpa [rankNat] using Finset.card_lt_card hs

def rankFin (scores : Fin n → ℝ) (index : Fin n) : Fin n :=
  ⟨rankNat scores index,actual_rank_is_less_than_sample_size scores index⟩

theorem actual_strict_score_order_gives_strict_rank_order
    (scores : Fin n → ℝ) (first second : Fin n) (h : scores first < scores second) :
    rankNat scores first < rankNat scores second := by
  have hs : Finset.univ.filter (fun j => scores j < scores first) ⊂
      Finset.univ.filter (fun j => scores j < scores second) := by
    constructor
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_trans (Finset.mem_filter.mp hj).2 h⟩
    · intro hall
      have hi := hall (Finset.mem_filter.mpr ⟨Finset.mem_univ first,h⟩)
      simp at hi
  exact Finset.card_lt_card hs

theorem actual_distinct_scores_have_bijective_ranks (scores : Fin n → ℝ)
    (h : Function.Injective scores) : Function.Bijective (rankFin scores) := by
  have hi : Function.Injective (rankFin scores) := by
    intro i j he
    have hv : rankNat scores i=rankNat scores j := congrArg Fin.val he
    by_contra hij
    have hs : scores i ≠ scores j := fun he => hij (h he)
    rcases lt_or_gt_of_ne hs with hs|hs
    · exact (ne_of_lt (actual_strict_score_order_gives_strict_rank_order scores i j hs)) hv
    · exact (ne_of_lt (actual_strict_score_order_gives_strict_rank_order scores j i hs)) hv.symm
  exact ⟨hi,(Finite.injective_iff_surjective).mp hi⟩

theorem actual_each_rank_occurs_exactly_once (scores : Fin n → ℝ)
    (h : Function.Injective scores) (rank : Fin n) :
    (∑ i : Fin n,if rankNat scores i=rank.val then (1:ℝ) else 0)=1 := by
  obtain ⟨index,hi⟩ := (actual_distinct_scores_have_bijective_ranks scores h).2 rank
  have he : ∀ i : Fin n,rankNat scores i=rank.val ↔ i=index := by
    intro i
    constructor
    · intro ht
      apply (actual_distinct_scores_have_bijective_ranks scores h).1
      apply Fin.ext
      exact ht.trans (congrArg Fin.val hi).symm
    · intro ht
      subst i
      exact congrArg Fin.val hi
  simp_rw [he]
  simp

theorem actual_rank_is_measurable (index : Fin n) :
    Measurable (fun scores : Fin n → ℝ => rankNat scores index) := by
  have he : (fun scores : Fin n → ℝ => rankNat scores index)=
      (fun scores => ∑ j : Fin n,if scores j<scores index then (1:ℕ) else 0) := by
    funext scores
    simp [rankNat]
  rw [he]
  exact Finset.measurable_fun_sum Finset.univ (fun j _ =>
    Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply index))
      measurable_const measurable_const)

def permutedScores (permutation : Equiv.Perm (Fin n)) (scores : Fin n → ℝ) : Fin n → ℝ :=
  fun i => scores (permutation i)

theorem actual_permuted_scores_are_measurable (permutation : Equiv.Perm (Fin n)) :
    Measurable (permutedScores permutation) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply (permutation i))

theorem actual_relabeling_preserves_the_corresponding_rank
    (permutation : Equiv.Perm (Fin n)) (scores : Fin n → ℝ) (index : Fin n) :
    rankNat (permutedScores permutation scores) index=rankNat scores (permutation index) := by
  have hl : rankNat (permutedScores permutation scores) index=
      ∑ j : Fin n,if scores (permutation j)<scores (permutation index) then (1:ℕ) else 0 := by
    simp [rankNat,permutedScores]
    rfl
  rw [hl]
  calc
    _ = ∑ j : Fin n,if scores j<scores (permutation index) then (1:ℕ) else 0 :=
      Fintype.sum_equiv permutation _ _ (fun _ => rfl)
    _ = _ := by simp [rankNat]

def rankEvent (index : Fin n) (rank : Fin n) : Set (Fin n → ℝ) :=
  {scores | rankNat scores index=rank.val}

theorem actual_rank_event_measurable (index rank : Fin n) : MeasurableSet (rankEvent index rank) :=
  (actual_rank_is_measurable index) (measurableSet_singleton rank.val)

/-- Exchangeability is invariance of the genuine joint score law under every
coordinate permutation, rather than an assumed uniform-rank conclusion. -/
def exchangeable (law : Measure (Fin n → ℝ)) : Prop :=
  ∀ permutation : Equiv.Perm (Fin n),law.map (permutedScores permutation)=law

theorem actual_exchangeability_gives_equal_coordinate_rank_probabilities
    (law : Measure (Fin n → ℝ)) (h : exchangeable law) (first second rank : Fin n) :
    law.real (rankEvent first rank)=law.real (rankEvent second rank) := by
  have hm := actual_permuted_scores_are_measurable (Equiv.swap first second)
  rw [←h (Equiv.swap first second),map_measureReal_apply hm (actual_rank_event_measurable first rank)]
  have he : permutedScores (Equiv.swap first second) ⁻¹' rankEvent first rank=rankEvent second rank := by
    ext scores
    simp only [Set.mem_preimage,rankEvent,Set.mem_ofPred_eq]
    rw [actual_relabeling_preserves_the_corresponding_rank,Equiv.swap_apply_left]
  rw [he,h (Equiv.swap first second)]

theorem actual_tie_free_exchangeable_rank_is_uniform
    (law : Measure (Fin n → ℝ)) [IsProbabilityMeasure law]
    (hex : exchangeable law) (hties : ∀ᵐ scores ∂law,Function.Injective scores)
    (index rank : Fin n) : law.real (rankEvent index rank)=1/(n:ℝ) := by
  have hs : ∑ i : Fin n,law.real (rankEvent i rank)=1 := by
    calc
      _ = ∑ i : Fin n,∫ scores,(rankEvent i rank).indicator (fun _ => (1:ℝ)) scores ∂law := by
        apply Finset.sum_congr rfl
        intro i hi
        symm
        simpa only [smul_eq_mul,mul_one] using
          integral_indicator_const (1:ℝ) (actual_rank_event_measurable i rank)
      _ = ∫ scores,∑ i : Fin n,(rankEvent i rank).indicator (fun _ => (1:ℝ)) scores ∂law := by
        symm
        apply integral_finsetSum
        intro i hi
        exact (integrable_const (1:ℝ)).indicator (actual_rank_event_measurable i rank)
      _ = ∫ _scores,1 ∂law := by
        apply integral_congr_ae
        filter_upwards [hties] with scores hscore
        calc
          _ = ∑ i : Fin n,if rankNat scores i=rank.val then (1:ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h : rankNat scores i=rank.val <;> simp [rankEvent,Set.indicator,h]
          _ = 1 := actual_each_rank_occurs_exactly_once scores hscore rank
      _ = 1 := by simp
  have he : ∑ i : Fin n,law.real (rankEvent i rank)=
      (n:ℝ)*law.real (rankEvent index rank) := by
    simp_rw [actual_exchangeability_gives_equal_coordinate_rank_probabilities law hex _ index rank]
    simp
  rw [he] at hs
  have hn : (n:ℝ)≠0 := by
    have hp : 0<n := Nat.zero_lt_of_lt index.isLt
    exact_mod_cast hp.ne'
  apply (eq_div_iff hn).mpr
  nlinarith

end SafeLearning.CompleteAppliedConformalRanks
