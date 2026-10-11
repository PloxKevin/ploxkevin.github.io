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
  change (Measure.pi (fun _ : Fin n => nu)).map (fun f i => f (permutation i)) =
    Measure.pi (fun _ : Fin n => nu)
  simpa [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft'] using hp.map_eq

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
    apply (Measure.measure_prod_null (measurableSet_eq_fun measurable_fst measurable_snd)).2
    filter_upwards [] with x
    simp
  calc
    independentSeedLaw nu {seeds | seeds i = seeds j} =
        ((independentSeedLaw nu).map (fun seeds => (seeds i,seeds j)))
          {pair : ℝ × ℝ | pair.1 = pair.2} := by
      rw [Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
        (measurableSet_eq_fun measurable_fst measurable_snd)]
      rfl
    _ = _ := by unfold independentSeedLaw;rw [hm,hd]

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
    have he : {pairs : Fin n → PairScore | Function.Injective pairs} =
        ⋂ i : Fin n, ⋂ j : Fin n, {pairs : Fin n → PairScore | pairs i = pairs j → i = j} := by
      ext pairs
      simp [Function.Injective]
    rw [he]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i = j
    · simp [hij]
    · have hc : MeasurableSet {pairs : Fin n → PairScore | ¬pairs i = pairs j} := by
        change MeasurableSet ({pairs : Fin n → PairScore | pairs i = pairs j}ᶜ)
        exact (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl
      simpa only [hij,imp_false] using hc
  unfold actualSeededPairLaw
  apply (ae_map_iff actual_attached_seed_pairs_are_measurable.aemeasurable hp).2
  filter_upwards [joint] with data hd
  intro i j he
  apply hd
  exact congrArg Prod.snd he


instance actual_seeded_pair_law_probability (law : Measure (Fin n → ℝ))
    (nu : Measure ℝ) [IsProbabilityMeasure law] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (actualSeededPairLaw law nu) := by
  unfold actualSeededPairLaw
  infer_instance

theorem actual_lexicographic_joint_exchangeability_gives_every_rank_cdf
    (n : ℕ) (law : Measure (Fin (n+1) → PairScore)) [IsProbabilityMeasure law]
    (hex : exchangeable law) (hties : ∀ᵐ scores ∂law, Function.Injective scores)
    (test : Fin (n+1)) (k : ℕ) (hk : k ≤ n) :
    law.real {scores | rankNat scores test < k} = (k : ℝ)/(n+1) := by
  classical
  let top : Fin (n+1) := ⟨k,by omega⟩
  let ranks : Finset (Fin (n+1)) := Finset.Iio top
  have he : {scores | rankNat scores test < k} =
      ⋃ r ∈ ranks, rankEvent test r := by
    ext scores
    constructor
    · intro hs
      refine Set.mem_iUnion.mpr ⟨rankFin scores test,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
      · simpa [ranks,top,Fin.lt_def,rankFin] using hs
      · rfl
    · intro hs
      obtain ⟨r,hs⟩ := Set.mem_iUnion.mp hs
      obtain ⟨hr,he⟩ := Set.mem_iUnion.mp hs
      have hlt : r.val < k := by simpa [ranks,top,Fin.lt_def] using hr
      change rankNat scores test = r.val at he
      change rankNat scores test < k
      rw [he]
      exact hlt
  have hd : Set.PairwiseDisjoint (↑ranks) (rankEvent test) := by
    intro r hr s hs hne
    apply Set.disjoint_left.mpr
    intro scores h1 h2
    apply hne
    apply Fin.ext
    change rankNat scores test = r.val at h1
    change rankNat scores test = s.val at h2
    exact h1.symm.trans h2
  rw [he,measureReal_biUnion_finset hd (fun r _ => actual_rank_event_measurable test r)]
  simp_rw [actual_tie_free_exchangeable_rank_is_uniform law hex hties test]
  simp [ranks,top,Fin.card_Iio,div_eq_mul_inv]


def forgetSeeds (pairs : Fin n → PairScore) : Fin n → ℝ := fun i => (pairs i).1

theorem actual_forgetting_independent_seeds_is_measurable : Measurable (forgetSeeds (n := n)) := by
  exact Measurable.of_eval (fun i => measurable_fst.comp (measurable_pi_apply i))

theorem actual_forgetting_independent_seeds_recovers_the_original_score_law
    (law : Measure (Fin n → ℝ)) (nu : Measure ℝ)
    [IsProbabilityMeasure law] [IsProbabilityMeasure nu] :
    (actualSeededPairLaw law nu).map forgetSeeds=law := by
  have he : forgetSeeds ∘ attachSeeds = (Prod.fst : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)) := by
    funext data i
    rfl
  unfold actualSeededPairLaw
  rw [Measure.map_map actual_forgetting_independent_seeds_is_measurable
    actual_attached_seed_pairs_are_measurable,he,Measure.map_fst_prod,measure_univ,one_smul]

theorem actual_original_strict_score_count_is_bounded_by_lexicographic_pair_count
    (pairs : Fin n → PairScore) (test : Fin n) :
    CompleteConformal.strictRank (forgetSeeds pairs) test ≤ rankNat pairs test := by
  classical
  apply Finset.card_le_card
  intro j hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ j,?_⟩
  apply Prod.Lex.lt_iff.mpr
  exact Or.inl (Finset.mem_filter.mp hj).2

theorem actual_small_lexicographic_rank_implies_original_calibration_membership
    (pairs : Fin n → PairScore) (test : Fin n) (k : ℕ)
    (h : rankNat pairs test < k) :
    ((forgetSeeds pairs) test : EReal) ≤ CompleteConformal.calibrationThreshold (forgetSeeds pairs) test k := by
  rw [←not_lt,CompleteConformal.calibration_failure_iff,not_le]
  exact lt_of_le_of_lt (actual_original_strict_score_count_is_bounded_by_lexicographic_pair_count pairs test) h

theorem actual_independent_uniform_seed_lexicographic_membership_has_exact_probability
    (n : ℕ) (law : Measure (Fin (n+1) → ℝ)) [IsProbabilityMeasure law]
    (hex : CompleteAppliedConformalRanks.exchangeable law)
    (test : Fin (n+1)) (k : ℕ) (hk : k ≤ n) :
    (actualSeededPairLaw law uniformUnitSeed).real {pairs | rankNat pairs test < k} = (k:ℝ)/(n+1) := by
  exact actual_lexicographic_joint_exchangeability_gives_every_rank_cdf n
    (actualSeededPairLaw law uniformUnitSeed)
    (actual_independent_seed_attachment_preserves_joint_exchangeability law uniformUnitSeed hex)
    (actual_independent_atomless_seed_attachment_is_almost_surely_tie_free law uniformUnitSeed)
    test k hk

theorem actual_independent_uniform_seed_construction_proves_the_tied_lower_coverage_bound
    (n : ℕ) (law : Measure (Fin (n+1) → ℝ)) [IsProbabilityMeasure law]
    (hex : CompleteAppliedConformalRanks.exchangeable law)
    (test : Fin (n+1)) (k : ℕ) (hk : k ≤ n) :
    (k:ℝ)/(n+1) ≤ law.real {scores | (scores test : EReal) ≤ CompleteConformal.calibrationThreshold scores test k} := by
  have hm : MeasurableSet {scores : Fin (n+1) → ℝ | (scores test : EReal) ≤ CompleteConformal.calibrationThreshold scores test k} := by
    have he : {scores : Fin (n+1) → ℝ | (scores test : EReal) ≤ CompleteConformal.calibrationThreshold scores test k} =
      {scores | CompleteConformal.strictRank scores test < k} := by
      ext scores
      change (scores test : EReal) ≤ CompleteConformal.calibrationThreshold scores test k ↔
        CompleteConformal.strictRank scores test < k
      rw [←not_lt,CompleteConformal.calibration_failure_iff,not_le]
    rw [he]
    exact measurableSet_lt (CompleteConformal.measurable_strictRank test) measurable_const
  have hsub : {pairs : Fin (n+1) → PairScore | rankNat pairs test < k} ⊆
      forgetSeeds ⁻¹' {scores | (scores test : EReal) ≤ CompleteConformal.calibrationThreshold scores test k} := by
    intro pairs hp
    exact actual_small_lexicographic_rank_implies_original_calibration_membership pairs test k hp
  have h := measureReal_mono (μ := actualSeededPairLaw law uniformUnitSeed) hsub
  rw [actual_independent_uniform_seed_lexicographic_membership_has_exact_probability n law hex test k hk] at h
  have he := map_measureReal_apply actual_forgetting_independent_seeds_is_measurable hm
    (μ := actualSeededPairLaw law uniformUnitSeed)
  rw [actual_forgetting_independent_seeds_recovers_the_original_score_law] at he
  exact h.trans_eq he.symm


/-- Prediction membership compares the test score-seed pair only with the
calibration pairs; it is not a presumed rank distribution. -/
def randomizedCalibrationMembership (pairs : Fin n → PairScore) (test : Fin n) (k : ℕ) : Prop :=
  ((Finset.univ.erase test).filter (fun j => pairs j < pairs test)).card < k

theorem actual_lexicographic_rank_counts_only_the_other_calibration_pairs
    (pairs : Fin n → PairScore) (test : Fin n) :
    rankNat pairs test = ((Finset.univ.erase test).filter (fun j => pairs j < pairs test)).card := by
  classical
  have he : Finset.univ.filter (fun j => pairs j < pairs test) =
      (Finset.univ.erase test).filter (fun j => pairs j < pairs test) := by
    ext j
    by_cases hj : j=test
    · subst j
      simp
    · simp [hj]
  rw [rankNat,he]

theorem actual_seeded_ceiling_rank_has_both_literal_coverage_arithmetic_bounds
    (n : ℕ) (alpha : ℝ) (ha : alpha ≤ 1) :
    1-alpha ≤ (CompleteConformal.conformalRank n alpha : ℝ)/(n+1) ∧
      (CompleteConformal.conformalRank n alpha : ℝ)/(n+1) < 1-alpha+1/(n+1) := by
  have hp : (0 : ℝ)<n+1 := by positivity
  simp only [CompleteConformal.conformalRank,Nat.cast_add,Nat.cast_one]
  have hlo := Nat.le_ceil (((n+1 : ℕ) : ℝ)*(1-alpha))
  have hhi := Nat.ceil_lt_add_one (mul_nonneg (show (0 : ℝ)≤((n+1 : ℕ) : ℝ) by positivity) (sub_nonneg.mpr ha))
  simp only [Nat.cast_add,Nat.cast_one] at hlo hhi
  constructor
  · apply (le_div_iff₀ hp).mpr
    change (1-alpha)*(n+1) ≤ (Nat.ceil ((n+1 : ℝ)*(1-alpha)) : ℝ)
    nlinarith
  · apply (div_lt_iff₀ hp).mpr
    have hdiv : (1/(n+1 : ℝ))*(n+1)=1 := by field_simp [hp.ne']
    change (Nat.ceil ((n+1 : ℝ)*(1-alpha)) : ℝ)<(1-alpha+1/(n+1))*(n+1)
    nlinarith


theorem actual_consistently_seeded_calibration_and_prediction_membership_has_both_bounds
    (n : ℕ) (law : Measure (Fin (n+1) → ℝ)) [IsProbabilityMeasure law]
    (hex : CompleteAppliedConformalRanks.exchangeable law) (test : Fin (n+1))
    (alpha : ℝ) (ha : alpha ≤ 1) (hk : CompleteConformal.conformalRank n alpha ≤ n) :
    1-alpha ≤ (actualSeededPairLaw law uniformUnitSeed).real
      {pairs | randomizedCalibrationMembership pairs test (CompleteConformal.conformalRank n alpha)} ∧
    (actualSeededPairLaw law uniformUnitSeed).real
      {pairs | randomizedCalibrationMembership pairs test (CompleteConformal.conformalRank n alpha)} <
      1-alpha+1/(n+1) := by
  have he : {pairs : Fin (n+1) → PairScore | randomizedCalibrationMembership pairs test
      (CompleteConformal.conformalRank n alpha)} =
      {pairs | rankNat pairs test < CompleteConformal.conformalRank n alpha} := by
    ext pairs
    change ((Finset.univ.erase test).filter (fun j => pairs j < pairs test)).card <
        CompleteConformal.conformalRank n alpha ↔ rankNat pairs test < CompleteConformal.conformalRank n alpha
    rw [actual_lexicographic_rank_counts_only_the_other_calibration_pairs]
  rw [he,actual_independent_uniform_seed_lexicographic_membership_has_exact_probability n law hex test _ hk]
  exact actual_seeded_ceiling_rank_has_both_literal_coverage_arithmetic_bounds n alpha ha

theorem actual_ties_preserve_the_one_minus_alpha_original_calibration_guarantee
    (n : ℕ) (law : Measure (Fin (n+1) → ℝ)) [IsProbabilityMeasure law]
    (hex : CompleteAppliedConformalRanks.exchangeable law) (test : Fin (n+1))
    (alpha : ℝ) (ha : alpha ≤ 1) (hk : CompleteConformal.conformalRank n alpha ≤ n) :
    1-alpha ≤ law.real {scores | (scores test : EReal) ≤
      CompleteConformal.calibrationThreshold scores test (CompleteConformal.conformalRank n alpha)} := by
  exact (actual_seeded_ceiling_rank_has_both_literal_coverage_arithmetic_bounds n alpha ha).1.trans
    (actual_independent_uniform_seed_construction_proves_the_tied_lower_coverage_bound n law hex test _ hk)

end SafeLearning.CompleteModulesConformalLexicographic27
