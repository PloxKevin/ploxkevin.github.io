import SafeLearning.CompleteAppliedBinomialModel
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedCoverageOrderStatistic
open CompleteAppliedFailureCounts CompleteAppliedBinomialModel

abbrev DistinctPairs := {pair:Fin 19×Fin 19 // pair.1≠pair.2}
instance distinctPairs_nonempty : Nonempty DistinctPairs := ⟨⟨(0,1),by decide⟩⟩

def secondLargest (scores : Fin 19→ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun pair:DistinctPairs=>min (scores pair.1.1) (scores pair.1.2))

theorem actual_second_largest_strict_threshold_is_the_all_distinct_pairs_test
    (scores : Fin 19→ℝ) (c : ℝ) :
    secondLargest scores<c ↔ ∀i j,i≠j→min (scores i) (scores j)<c := by
  classical
  rw [secondLargest,Finset.sup'_lt_iff]
  constructor
  · intro h i j hij
    exact h ⟨(i,j),hij⟩ (Finset.mem_univ _)
  · intro h pair _
    exact h pair.1.1 pair.1.2 pair.2

theorem actual_second_largest_strict_threshold_is_at_least_eighteen_below
    (scores : Fin 19→ℝ) (c : ℝ) :
    secondLargest scores<c ↔
      (Finset.univ.filter (fun i:Fin 19=>scores i<c)).card=18 ∨
      (Finset.univ.filter (fun i:Fin 19=>scores i<c)).card=19 := by
  classical
  rw [actual_second_largest_strict_threshold_is_the_all_distinct_pairs_test]
  let low : Finset (Fin 19):=Finset.univ.filter (fun i:Fin 19=>scores i<c)
  let high : Finset (Fin 19):=Finset.univ\low
  have hc : high.card=19-low.card := by
    simp [high,Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hlow : low.card≤19 := by
    simpa using Finset.card_le_card (Finset.subset_univ low)
  constructor
  · intro h
    have hhi : high.card≤1 := by
      by_cases he : high.Nonempty
      · obtain ⟨i,hi⟩:=he
        have hs : high⊆{i} := by
          intro j hj
          by_contra hneq
          have hjne : j≠i := by simpa using hneq
          have hi' : c ≤ scores i := by simpa [high,low] using hi
          have hj' : c ≤ scores j := by simpa [high,low] using hj
          have hb:=h j i hjne
          exact (not_lt_of_ge (le_min hj' hi')) hb
        simpa using Finset.card_le_card hs
      · have hz : high=∅ := Finset.not_nonempty_iff_eq_empty.mp he
        simp [hz]
    change low.card=18∨low.card=19
    omega
  · intro h i j hij
    change low.card=18∨low.card=19 at h
    by_contra hb
    have hv : c ≤ min (scores i) (scores j) := le_of_not_gt hb
    have hs : {i,j}⊆high := by
      intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl|rfl
      · simpa [high,low] using le_min_iff.mp hv |>.1
      · simpa [high,low] using le_min_iff.mp hv |>.2
    have hcard:=Finset.card_le_card hs
    have hp : ({i,j}:Finset (Fin 19)).card=2 := by simp [hij]
    omega

theorem actual_second_largest_of_measurable_coordinates_is_measurable
    {Ω : Type*} [MeasurableSpace Ω] (scores : Fin 19→Ω→ℝ)
    (hm : ∀i,Measurable (scores i)) : Measurable (fun omega=>secondLargest (fun i=>scores i omega)) := by
  apply measurable_of_Iio
  intro c
  have he : (fun omega=>secondLargest (fun i=>scores i omega)) ⁻¹' Iio c=
      ⋂pair:DistinctPairs,{omega| min (scores pair.1.1 omega) (scores pair.1.2 omega)<c} := by
    ext omega
    simp only [mem_preimage,mem_Iio,secondLargest,Finset.sup'_lt_iff,Finset.mem_univ,forall_true_left,
      mem_iInter,mem_ofPred_eq]
  rw [he]
  exact MeasurableSet.iInter (fun pair=>measurableSet_lt ((hm _).min (hm _)) measurable_const)

theorem actual_iid_continuous_uniform_coordinate_count_gives_the_second_largest_cdf
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (scores : Fin 19→Ω→ℝ) (hm : ∀i,Measurable (scores i))
    (hind : iIndepFun scores P) (c : ℝ)
    (hprob : ∀i,P.real {omega|scores i omega<c}=c) :
    P.real {omega|secondLargest (fun i=>scores i omega)<c}=
      19*c^18*(1-c)+c^19 := by
  classical
  let below : Fin 19→Set Ω:=fun i=>{omega|scores i omega<c}
  have hbmeas : ∀i,MeasurableSet (below i) :=
    fun i=>measurableSet_lt (hm i) measurable_const
  have hbind : iIndepSet below P := by
    apply (iIndepSet_iff_meas_biInter hbmeas).mpr
    intro S
    have h:=hind.measure_inter_preimage_eq_mul S (sets:=fun _=>Iio c)
      (fun _ _=>measurableSet_Iio)
    simpa only [below,Set.preimage,Set.mem_Iio] using h
  have he : {omega|secondLargest (fun i=>scores i omega)<c}=
      {omega|failureCount below omega=18}∪{omega|failureCount below omega=19} := by
    ext omega
    simp only [mem_ofPred_eq,mem_union]
    exact actual_second_largest_strict_threshold_is_at_least_eighteen_below _ c
  have hcount:=failure_count_measurable below hbmeas
  have h18 := actual_binomial_count_mass P 19 below hbmeas hbind c hprob 18
  have h19 := actual_binomial_count_mass P 19 below hbmeas hbind c hprob 19
  have hm19 : MeasurableSet {omega|failureCount below omega=19} :=
    hcount (measurableSet_singleton 19)
  rw [he,measureReal_union
    (by apply disjoint_left.mpr;intro omega h h';simp only [mem_ofPred_eq] at h h';omega)
    hm19,h18,h19]
  norm_num

end SafeLearning.CompleteAppliedCoverageOrderStatistic
