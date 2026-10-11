import SafeLearning.CompleteAppliedConformalRanks
import SafeLearning.CompleteConformal

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SafeLearning.CompleteModulesConformalContinuous27
open CompleteAppliedConformalRanks CompleteConformal

theorem actual_tie_free_joint_exchangeability_gives_every_rank_cdf
    (n : ℕ) (law : Measure (Fin (n+1) → ℝ)) [IsProbabilityMeasure law]
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

theorem actual_calibration_success_is_the_strict_rank_cdf
    {n : ℕ} (scores : Fin (n+1) → ℝ) (test : Fin (n+1)) (k : ℕ) :
    (scores test : EReal) ≤ calibrationThreshold scores test k ↔
      rankNat scores test < k := by
  rw [←not_lt,calibration_failure_iff,not_le]
  rfl

theorem actual_tie_free_split_calibration_coverage_is_exact
    (n : ℕ) (law : Measure (Fin (n+1) → ℝ)) [IsProbabilityMeasure law]
    (hex : exchangeable law) (hties : ∀ᵐ scores ∂law,Function.Injective scores)
    (test : Fin (n+1)) (k : ℕ) (hk : k ≤ n) :
    law.real {scores | (scores test : EReal) ≤ calibrationThreshold scores test k} =
      (k : ℝ)/(n+1) := by
  have he : {scores | (scores test : EReal) ≤ calibrationThreshold scores test k} =
      {scores | rankNat scores test < k} := by
    ext scores
    exact actual_calibration_success_is_the_strict_rank_cdf scores test k
  rw [he]
  exact actual_tie_free_joint_exchangeability_gives_every_rank_cdf n law hex hties test k hk

theorem actual_ceiling_rank_has_the_literal_two_sided_coverage_arithmetic
    (n : ℕ) (alpha : ℝ) (ha : alpha ≤ 1) :
    1-alpha ≤ (conformalRank n alpha : ℝ)/(n+1) ∧
      (conformalRank n alpha : ℝ)/(n+1) < 1-alpha+1/(n+1) := by
  have hp : (0 : ℝ)<n+1 := by positivity
  simp only [conformalRank,Nat.cast_add,Nat.cast_one]
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

theorem actual_nine_and_ten_calibration_ranks_and_exact_ratios :
    conformalRank 9 (1/10)=9 ∧ conformalRank 10 (1/10)=10 ∧
      (9 : ℝ)/10=9/10 ∧ (10 : ℝ)/11>9/10 ∧
      |(10 : ℝ)/11-909/1000| < 1/1000 := by
  norm_num [conformalRank,Nat.ceil_eq_iff]



theorem actual_nine_calibration_threshold_is_an_attained_real_maximum
    (scores : Fin 10 → ℝ) (test : Fin 10) :
    ∃ i : Fin 10, i ≠ test ∧
      IsGreatest (scores '' {j | j ≠ test}) (scores i) ∧
      calibrationThreshold scores test 9 = (scores i : EReal) := by
  classical
  letI : DecidableEq (Fin 10) := Classical.decEq (Fin 10)
  let s : Finset (Fin 10) := Finset.univ.erase test
  have hc : s.card = 9 := by simp [s]
  have hn : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i,hi,hm⟩ := Finset.exists_mem_eq_sup s hn (fun j => (scores j : EReal))
  have hit : i ≠ test := (Finset.mem_erase.mp hi).1
  refine ⟨i,hit,⟨⟨i,hit,rfl⟩,?_⟩,?_⟩
  · rintro y ⟨j,hjt,rfl⟩
    have hj : j ∈ s := Finset.mem_erase.mpr ⟨hjt,Finset.mem_univ _⟩
    have hle := Finset.le_sup (f := fun j => (scores j : EReal)) hj
    rw [hm] at hle
    exact EReal.coe_le_coe_iff.mp hle
  · unfold calibrationThreshold
    change ((Finset.univ.erase test).powersetCard 9).inf
      (fun subset => subset.sup (fun j => (scores j : EReal))) = (scores i : EReal)
    rw [←hc,Finset.powersetCard_self,Finset.inf_singleton]
    exact hm

theorem actual_tie_free_split_calibration_has_both_literal_coverage_bounds
    (n : ℕ) (law : Measure (Fin (n+1) → ℝ)) [IsProbabilityMeasure law]
    (hex : exchangeable law) (hties : ∀ᵐ scores ∂law,Function.Injective scores)
    (test : Fin (n+1)) (alpha : ℝ) (ha : alpha ≤ 1)
    (hk : conformalRank n alpha ≤ n) :
    1-alpha ≤ law.real {scores | (scores test : EReal) ≤
      calibrationThreshold scores test (conformalRank n alpha)} ∧
    law.real {scores | (scores test : EReal) ≤
      calibrationThreshold scores test (conformalRank n alpha)} <
        1-alpha+1/(n+1) := by
  rw [actual_tie_free_split_calibration_coverage_is_exact n law hex hties test
    (conformalRank n alpha) hk]
  exact actual_ceiling_rank_has_the_literal_two_sided_coverage_arithmetic n alpha ha

theorem actual_constant_nine_calibration_scores_are_always_covered_and_break_the_strict_upper
    (law : Measure (Fin 10 → ℝ)) [IsProbabilityMeasure law] (test : Fin 10) :
    law.real {scores | ((0 : ℝ) : EReal) ≤
      calibrationThreshold (fun _ : Fin 10 => (0 : ℝ)) test 9} = 1 ∧
    ¬ (law.real {scores | ((0 : ℝ) : EReal) ≤
      calibrationThreshold (fun _ : Fin 10 => (0 : ℝ)) test 9} <
        1-(1/10 : ℝ)+1/10) := by
  obtain ⟨i,hi,hgreat,hthreshold⟩ :=
    actual_nine_calibration_threshold_is_an_attained_real_maximum (fun _ => 0) test
  have he : calibrationThreshold (fun _ : Fin 10 => (0 : ℝ)) test 9 = (0 : ℝ) := by
    simpa using hthreshold
  simp [he]

end SafeLearning.CompleteModulesConformalContinuous27
