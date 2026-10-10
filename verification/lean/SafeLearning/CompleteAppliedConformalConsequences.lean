import SafeLearning.CompleteAppliedConformalRanks

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedConformalConsequences
open Set Filter MeasureTheory Function
open scoped BigOperators Topology
open SafeLearning.CompleteAppliedConformalRanks

def calibrationScores (scores : Fin 20 → ℝ) : Fin 19 → ℝ :=
  fun i => scores i.castSucc

def calibrationThreshold (scores : Fin 20 → ℝ) : ℝ :=
  if h : Function.Injective (calibrationScores scores) then
    calibrationScores scores ((Equiv.ofBijective (rankFin (calibrationScores scores))
      (actual_distinct_scores_have_bijective_ranks _ h)).symm (17 : Fin 19))
  else 0

def calibrationThresholdIndex (scores : Fin 20 → ℝ)
    (h : Function.Injective (calibrationScores scores)) : Fin 19 :=
  (Equiv.ofBijective (rankFin (calibrationScores scores))
    (actual_distinct_scores_have_bijective_ranks _ h)).symm (17 : Fin 19)

theorem actual_calibration_scores_are_distinct (scores : Fin 20 → ℝ)
    (h : Function.Injective scores) : Function.Injective (calibrationScores scores) := by
  intro i j he
  exact Fin.castSucc_injective 19 (h he)

theorem actual_threshold_is_the_eighteenth_calibration_order_statistic
    (scores : Fin 20 → ℝ) (h : Function.Injective (calibrationScores scores)) :
    rankNat (calibrationScores scores) (calibrationThresholdIndex scores h)=17 ∧
    calibrationThreshold scores=calibrationScores scores (calibrationThresholdIndex scores h) := by
  constructor
  · have he := (Equiv.ofBijective (rankFin (calibrationScores scores))
      (actual_distinct_scores_have_bijective_ranks _ h)).apply_symm_apply (17 : Fin 19)
    exact congrArg Fin.val he
  · simp [calibrationThreshold,calibrationThresholdIndex,h]

theorem actual_full_rank_is_calibration_rank_plus_the_future_comparison
    (scores : Fin 20 → ℝ) (i : Fin 19) :
    rankNat scores i.castSucc=rankNat (calibrationScores scores) i+
      if scores (Fin.last 19)<scores i.castSucc then 1 else 0 := by
  have hfull : rankNat scores i.castSucc=
      ∑ j : Fin 20,if scores j<scores i.castSucc then (1:ℕ) else 0 := by simp [rankNat]
  have hcal : rankNat (calibrationScores scores) i=
      ∑ j : Fin 19,if calibrationScores scores j<calibrationScores scores i then (1:ℕ) else 0 := by simp [rankNat]
  rw [hfull,hcal,Fin.sum_univ_castSucc]
  rfl

theorem actual_acceptance_is_exactly_overall_rank_at_most_eighteen
    (scores : Fin 20 → ℝ) (h : Function.Injective scores) :
    scores (Fin.last 19) ≤ calibrationThreshold scores ↔
      rankNat scores (Fin.last 19)<18 := by
  let hc := actual_calibration_scores_are_distinct scores h
  let i := calibrationThresholdIndex scores hc
  have ht := actual_threshold_is_the_eighteenth_calibration_order_statistic scores hc
  have hr : rankNat (calibrationScores scores) i=17 := ht.1
  have hv : calibrationThreshold scores=scores i.castSucc := ht.2
  have hn : scores (Fin.last 19) ≠ scores i.castSucc := by
    intro he
    have hh := congrArg Fin.val (h he)
    simp only [Fin.val_last,Fin.val_castSucc] at hh
    omega
  rw [hv]
  rcases lt_or_gt_of_ne hn with hp|hp
  · have hf : rankNat scores i.castSucc=18 := by
      rw [actual_full_rank_is_calibration_rank_plus_the_future_comparison,hr,ite_eq_left hp]
    have hb := actual_strict_score_order_gives_strict_rank_order scores (Fin.last 19) i.castSucc hp
    rw [hf] at hb
    exact ⟨fun _ => hb,fun _ => hp.le⟩
  · have hf : rankNat scores i.castSucc=17 := by
      rw [actual_full_rank_is_calibration_rank_plus_the_future_comparison,hr,ite_eq_right (not_lt_of_gt hp)]
    have hb := actual_strict_score_order_gives_strict_rank_order scores i.castSucc (Fin.last 19) hp
    rw [hf] at hb
    constructor
    · intro hl;exfalso;exact (not_le_of_gt hp) hl
    · intro hl;omega


def rankBelowEvent (index : Fin 20) (cutoff : ℕ) : Set (Fin 20 → ℝ) :=
  {scores | rankNat scores index<cutoff}

theorem actual_rank_below_event_probability
    (law : Measure (Fin 20 → ℝ)) [IsProbabilityMeasure law]
    (hex : exchangeable law) (hties : ∀ᵐ scores ∂law,Function.Injective scores)
    (index : Fin 20) (cutoff : ℕ) (hcutoff : cutoff ≤ 20) :
    law.real (rankBelowEvent index cutoff)=(cutoff:ℝ)/20 := by
  have he : rankBelowEvent index cutoff=⋃ i : Fin cutoff,
      rankEvent index ⟨i.val,lt_of_lt_of_le i.isLt hcutoff⟩ := by
    ext scores
    simp only [rankBelowEvent,Set.mem_ofPred_eq,Set.mem_iUnion,rankEvent]
    constructor
    · intro hs
      exact ⟨⟨rankNat scores index,hs⟩,rfl⟩
    · rintro ⟨i,hi⟩
      rw [hi]
      exact i.isLt
  have hd : Pairwise (Disjoint on (fun i : Fin cutoff =>
      rankEvent index ⟨i.val,lt_of_lt_of_le i.isLt hcutoff⟩)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro scores hi hj
    apply hij
    apply Fin.ext
    exact hi.symm.trans hj
  rw [he,measureReal_iUnion_fintype hd (fun _ => actual_rank_event_measurable _ _)]
  simp_rw [actual_tie_free_exchangeable_rank_is_uniform law hex hties]
  simp [div_eq_mul_inv]

def actualAcceptance : Set (Fin 20 → ℝ) :=
  {scores | scores (Fin.last 19) ≤ calibrationThreshold scores}

theorem actual_nineteen_calibration_eighteenth_threshold_accepts_with_probability_point_nine
    (law : Measure (Fin 20 → ℝ)) [IsProbabilityMeasure law]
    (hex : exchangeable law) (hties : ∀ᵐ scores ∂law,Function.Injective scores) :
    law.real actualAcceptance=(0.9:ℝ) := by
  have he : actualAcceptance=ᵐ[law]rankBelowEvent (Fin.last 19) 18 := by
    filter_upwards [hties] with scores hs
    exact propext (actual_acceptance_is_exactly_overall_rank_at_most_eighteen scores hs)
  rw [measureReal_congr he,actual_rank_below_event_probability law hex hties _ _ (by norm_num)]
  norm_num

end SafeLearning.CompleteAppliedConformalConsequences
