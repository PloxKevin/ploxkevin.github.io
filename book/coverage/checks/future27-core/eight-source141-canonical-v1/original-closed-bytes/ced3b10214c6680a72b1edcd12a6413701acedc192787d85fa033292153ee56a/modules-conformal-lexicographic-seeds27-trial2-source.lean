import Mathlib
import SafeLearning.CompleteAppliedConformalRanks
import SafeLearning.CompleteConformal

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesConformalLexicographic27
open Set Filter MeasureTheory
open scoped BigOperators Topology

variable {n : ℕ}

abbrev PairScore := ℝ ×ₗ ℝ
instance : MeasurableSpace PairScore := inferInstanceAs (MeasurableSpace (ℝ × ℝ))
instance : MeasurableEq PairScore := inferInstanceAs (MeasurableEq (ℝ × ℝ))

theorem actual_lexicographic_comparison_is_measurable (j index : Fin n) :
    MeasurableSet {scores : Fin n → PairScore | scores j < scores index} := by
  have hf (i : Fin n) : Measurable (fun scores : Fin n → PairScore => (scores i).1) :=
    measurable_fst.comp (measurable_pi_apply i)
  have hs (i : Fin n) : Measurable (fun scores : Fin n → PairScore => (scores i).2) :=
    measurable_snd.comp (measurable_pi_apply i)
  simp only [Prod.Lex.lt_iff]
  exact (measurableSet_lt (hf j) (hf index)).union
    ((measurableSet_eq_fun (hf j) (hf index)).inter
      (measurableSet_lt (hs j) (hs index)))

/-- Zero-based strict rank of an actual coordinate among all finite scores. -/
def rankNat (scores : Fin n → PairScore) (index : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => scores j < scores index)).card

theorem actual_rank_is_less_than_sample_size (scores : Fin n → PairScore) (index : Fin n) :
    rankNat scores index < n := by
  have hs : Finset.univ.filter (fun j => scores j < scores index) ⊂ Finset.univ := by
    refine ⟨Finset.filter_subset _ _,?_⟩
    intro hall
    have h := hall (Finset.mem_univ index)
    simp at h
  simpa [rankNat] using Finset.card_lt_card hs

def rankFin (scores : Fin n → PairScore) (index : Fin n) : Fin n :=
  ⟨rankNat scores index,actual_rank_is_less_than_sample_size scores index⟩

theorem actual_strict_score_order_gives_strict_rank_order
    (scores : Fin n → PairScore) (first second : Fin n) (h : scores first < scores second) :
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

theorem actual_distinct_scores_have_bijective_ranks (scores : Fin n → PairScore)
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

theorem actual_each_rank_occurs_exactly_once (scores : Fin n → PairScore)
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
    Measurable (fun scores : Fin n → PairScore => rankNat scores index) := by
  have he : (fun scores : Fin n → PairScore => rankNat scores index)=
      (fun scores => ∑ j : Fin n,if scores j<scores index then (1:ℕ) else 0) := by
    funext scores
    simp [rankNat]
  rw [he]
  exact Finset.measurable_fun_sum Finset.univ (fun j _ =>
    Measurable.ite (actual_lexicographic_comparison_is_measurable j index)
      measurable_const measurable_const)

def permutedScores (permutation : Equiv.Perm (Fin n)) (scores : Fin n → PairScore) : Fin n → PairScore :=
  fun i => scores (permutation i)

theorem actual_permuted_scores_are_measurable (permutation : Equiv.Perm (Fin n)) :
    Measurable (permutedScores permutation) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply (permutation i))

theorem actual_relabeling_preserves_the_corresponding_rank
    (permutation : Equiv.Perm (Fin n)) (scores : Fin n → PairScore) (index : Fin n) :
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

def rankEvent (index : Fin n) (rank : Fin n) : Set (Fin n → PairScore) :=
  {scores | rankNat scores index=rank.val}

theorem actual_rank_event_measurable (index rank : Fin n) : MeasurableSet (rankEvent index rank) :=
  (actual_rank_is_measurable index) (measurableSet_singleton rank.val)

/-- Exchangeability is invariance of the genuine joint score law under every
coordinate permutation, rather than an assumed uniform-rank conclusion. -/
def exchangeable (law : Measure (Fin n → PairScore)) : Prop :=
  ∀ permutation : Equiv.Perm (Fin n),law.map (permutedScores permutation)=law

theorem actual_exchangeability_gives_equal_coordinate_rank_probabilities
    (law : Measure (Fin n → PairScore)) (h : exchangeable law) (first second rank : Fin n) :
    law.real (rankEvent first rank)=law.real (rankEvent second rank) := by
  have hm := actual_permuted_scores_are_measurable (Equiv.swap first second)
  rw [←h (Equiv.swap first second),map_measureReal_apply hm (actual_rank_event_measurable first rank)]
  have he : permutedScores (Equiv.swap first second) ⁻¹' rankEvent first rank=rankEvent second rank := by
    ext scores
    simp only [Set.mem_preimage,rankEvent,Set.mem_ofPred_eq]
    rw [actual_relabeling_preserves_the_corresponding_rank,Equiv.swap_apply_left]
  rw [he,h (Equiv.swap first second)]

theorem actual_tie_free_exchangeable_rank_is_uniform
    (law : Measure (Fin n → PairScore)) [IsProbabilityMeasure law]
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


open ProbabilityTheory

def uniformUnitSeed : Measure ℝ := volume.restrict (Icc 0 1)

instance actual_unit_uniform_seed_probability : IsProbabilityMeasure uniformUnitSeed := by
  apply isProbabilityMeasure_iff.mpr
  rw [uniformUnitSeed,Measure.restrict_apply_univ]
  norm_num

instance actual_unit_uniform_seed_has_no_atoms : NullSingletonClass uniformUnitSeed := by
  unfold uniformUnitSeed
  infer_instance

def independentSeedLaw (nu : Measure ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => nu)

instance actual_independent_seed_probability (nu : Measure ℝ) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (independentSeedLaw (n := n) nu) := by
  unfold independentSeedLaw
  infer_instance

def attachSeeds (data : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → PairScore :=
  fun i => (data.1 i,data.2 i)

theorem actual_attached_seed_pairs_are_measurable :
    Measurable (attachSeeds (n := n)) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((measurable_pi_apply i).comp measurable_snd)

theorem actual_iid_seed_law_is_invariant_under_permutations
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (permutation : Equiv.Perm (Fin n)) :
    (independentSeedLaw nu).map
      (CompleteAppliedConformalRanks.permutedScores permutation) = independentSeedLaw nu := by
  have hp := measurePreserving_piCongrLeft (α := fun _ : Fin n => ℝ)
    (fun _ : Fin n => nu) permutation.symm
  simpa [independentSeedLaw,CompleteAppliedConformalRanks.permutedScores,
    MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft'] using hp.map_eq

theorem actual_two_independent_atomless_seed_coordinates_cannot_tie
    (nu : Measure ℝ) [IsProbabilityMeasure nu] [NullSingletonClass nu]
    (i j : Fin n) (hij : i ≠ j) :
    independentSeedLaw nu {seeds | seeds i = seeds j} = 0 := by
  have hi : iIndepFun (fun i : Fin n => fun seeds : Fin n → ℝ => seeds i)
      (independentSeedLaw nu) := by
    exact iIndepFun_pi (fun _ : Fin n => (measurable_id : Measurable (id : ℝ → ℝ)).aemeasurable)
  have hm := (hi.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  change (Measure.pi (fun _ : Fin n => nu)).map (fun seeds => (seeds i,seeds j)) = _ at hm
  change _ = ((Measure.pi (fun _ : Fin n => nu)).map (Function.eval i)).prod
    ((Measure.pi (fun _ : Fin n => nu)).map (Function.eval j)) at hm
  rw [(measurePreserving_eval (fun _ : Fin n => nu) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => nu) j).map_eq] at hm
  have hd : (nu.prod nu) {pair : ℝ × ℝ | pair.1 = pair.2} = 0 := by
    apply (measure_prod_null (measurableSet_eq_fun measurable_fst measurable_snd)).2
    filter_upwards [] with x
    simp
  calc
    independentSeedLaw nu {seeds | seeds i = seeds j} =
        ((independentSeedLaw nu).map (fun seeds => (seeds i,seeds j)))
          {pair : ℝ × ℝ | pair.1 = pair.2} := by
      rw [Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
        (measurableSet_eq_fun measurable_fst measurable_snd)]
      rfl
    _ = _ := by rw [hm,hd]

theorem actual_all_independent_atomless_seed_coordinates_are_distinct
    (nu : Measure ℝ) [IsProbabilityMeasure nu] [NullSingletonClass nu] :
    ∀ᵐ seeds ∂independentSeedLaw (n := n) nu, Function.Injective seeds := by
  have hpair : ∀ i j : Fin n, ∀ᵐ seeds ∂independentSeedLaw nu,
      i ≠ j → seeds i ≠ seeds j := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · have hn := actual_two_independent_atomless_seed_coordinates_cannot_tie nu i j hij
      have ha : ∀ᵐ seeds ∂independentSeedLaw nu, seeds i ≠ seeds j := by
        exact (compl_mem_ae_iff).2 hn
      filter_upwards [ha] with seeds hs
      exact fun _ => hs
  have hall : ∀ᵐ seeds ∂independentSeedLaw nu, ∀ i j : Fin n,
      i ≠ j → seeds i ≠ seeds j :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpair i))
  filter_upwards [hall] with seeds hs
  intro i j he
  by_contra hij
  exact hs i j hij he

def actualSeededPairLaw (law : Measure (Fin n → ℝ)) (nu : Measure ℝ) :
    Measure (Fin n → PairScore) := (law.prod (independentSeedLaw nu)).map attachSeeds

theorem actual_independent_seed_attachment_preserves_joint_exchangeability
    (law : Measure (Fin n → ℝ)) (nu : Measure ℝ)
    [IsProbabilityMeasure law] [IsProbabilityMeasure nu]
    (hex : CompleteAppliedConformalRanks.exchangeable law) :
    exchangeable (actualSeededPairLaw law nu) := by
  intro permutation
  let perm := CompleteAppliedConformalRanks.permutedScores permutation
  have hm : Measurable perm := CompleteAppliedConformalRanks.actual_permuted_scores_are_measurable permutation
  have hp : (law.prod (independentSeedLaw nu)).map (Prod.map perm perm) =
      law.prod (independentSeedLaw nu) := by
    rw [← Measure.map_prod_map law (independentSeedLaw nu) hm hm]
    rw [hex permutation,actual_iid_seed_law_is_invariant_under_permutations nu permutation]
  have commute : permutedScores permutation ∘ attachSeeds = attachSeeds ∘ Prod.map perm perm := by
    funext data i
    rfl
  unfold actualSeededPairLaw
  rw [Measure.map_map (actual_permuted_scores_are_measurable permutation) actual_attached_seed_pairs_are_measurable]
  rw [commute,← Measure.map_map actual_attached_seed_pairs_are_measurable (hm.prodMap hm),hp]

theorem actual_independent_atomless_seed_attachment_is_almost_surely_tie_free
    (law : Measure (Fin n → ℝ)) (nu : Measure ℝ)
    [IsProbabilityMeasure law] [IsProbabilityMeasure nu] [NullSingletonClass nu] :
    ∀ᵐ pairs ∂actualSeededPairLaw law nu, Function.Injective pairs := by
  have hs := actual_all_independent_atomless_seed_coordinates_are_distinct (n := n) nu
  have joint : ∀ᵐ data ∂law.prod (independentSeedLaw nu), Function.Injective data.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := law) (ν := independentSeedLaw nu)).ae hs
  have hp : MeasurableSet {pairs : Fin n → PairScore | Function.Injective pairs} := by
    change MeasurableSet (⋂ i : Fin n, ⋂ j : Fin n, {pairs : Fin n → PairScore | pairs i = pairs j → i = j})
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i = j
    · simp [hij]
    · simpa only [hij,imp_false] using
        (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl
  unfold actualSeededPairLaw
  apply (ae_map_iff actual_attached_seed_pairs_are_measurable.aemeasurable hp).2
  filter_upwards [joint] with data hd
  intro i j he
  apply hd
  exact congrArg Prod.snd he

end SafeLearning.CompleteModulesConformalLexicographic27
