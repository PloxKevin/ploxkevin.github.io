import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SafeLearning.CompleteConformal

def strictRank {ι : Type*} [Fintype ι] (scores : ι → ℝ) (i : ι) : ℕ :=
  (Finset.univ.filter fun j => scores j < scores i).card

def badIndices {ι : Type*} [Fintype ι] (scores : ι → ℝ) (rank : ℕ) : Finset ι :=
  Finset.univ.filter fun i => rank ≤ strictRank scores i

theorem strictRank_permute {ι : Type*} [Fintype ι]
    (scores : ι → ℝ) (p : Equiv.Perm ι) (i : ι) :
    strictRank (fun j => scores (p j)) i = strictRank scores (p i) := by
  classical
  unfold strictRank
  apply Finset.card_bij (fun j _ => p j)
  · intro j hj
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hj
  · intro a _ b _ h
    exact p.injective h
  · intro b hb
    refine ⟨p.symm b,?_,by simp⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,p.apply_symm_apply] using hb

theorem badIndices_card_bound {ι : Type*} [Fintype ι]
    (scores : ι → ℝ) (rank : ℕ) :
    (badIndices scores rank).card ≤ Fintype.card ι-rank := by
  classical
  by_cases he : (badIndices scores rank).Nonempty
  · obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image (badIndices scores rank) scores he
    have hk : rank ≤ strictRank scores i := (Finset.mem_filter.mp hi).2
    have hs : (Finset.univ.filter fun j => scores j < scores i) ⊆
        Finset.univ \ badIndices scores rank := by
      intro j hj
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ j,?_⟩
      intro hb
      have hji := (Finset.mem_filter.mp hj).2
      have hij := hmin j hb
      linarith
    have hc := Finset.card_le_card hs
    have heq := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (badIndices scores rank))
    rw [Finset.card_univ] at heq
    unfold strictRank at hk
    omega
  · have hz := Finset.not_nonempty_iff_eq_empty.mp he
    simp [hz]

theorem measurable_strictRank {ι : Type*} [Fintype ι] (i : ι) :
    Measurable (fun scores : ι → ℝ => strictRank scores i) := by
  classical
  unfold strictRank
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))
    measurable_const measurable_const

theorem measurableSet_bad_rank {ι : Type*} [Fintype ι] (i : ι) (rank : ℕ) :
    MeasurableSet {scores : ι → ℝ | rank ≤ strictRank scores i} :=
  measurableSet_le measurable_const (measurable_strictRank i)

theorem exchangeable_bad_rank_equal {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (scores : Ω → ι → ℝ)
    (hex : ∀ p : Equiv.Perm ι,
      IdentDistrib (fun ω i => scores ω (p i)) scores μ μ)
    (p : Equiv.Perm ι) (i : ι) (rank : ℕ) :
    μ {ω | rank ≤ strictRank (scores ω) (p i)} =
      μ {ω | rank ≤ strictRank (scores ω) i} := by
  have h := (hex p).measure_mem_eq (measurableSet_bad_rank i rank)
  simpa only [preimage_ofPred_eq,strictRank_permute] using h

def badEvent {Ω ι : Type*} [Fintype ι] (scores : Ω → ι → ℝ)
    (rank : ℕ) (i : ι) : Set Ω := {ω | rank ≤ strictRank (scores ω) i}

theorem measurableSet_badEvent {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (scores : Ω → ι → ℝ) (hm : Measurable scores) (rank : ℕ) (i : ι) :
    MeasurableSet (badEvent scores rank i) :=
  (measurableSet_bad_rank i rank).preimage hm

theorem bad_indicator_count {Ω ι : Type*} [Fintype ι]
    (scores : Ω → ι → ℝ) (rank : ℕ) (ω : Ω) :
    (∑ i, (badEvent scores rank i).indicator (fun _ => (1 : ℝ)) ω) =
      ((badIndices (scores ω) rank).card : ℝ) := by
  classical
  simp only [badEvent,badIndices,Finset.card_eq_sum_ones,Nat.cast_sum,
    Finset.sum_filter,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Set.indicator,mem_ofPred_eq]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : rank ≤ strictRank (scores ω) i <;> simp only [h,if_true,if_false]

theorem sum_bad_probabilities_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (scores : Ω → ι → ℝ) (hm : Measurable scores) (rank : ℕ) :
    (∑ i, μ.real (badEvent scores rank i)) ≤ (Fintype.card ι-rank : ℕ) := by
  classical
  have hInt : ∀ i, Integrable ((badEvent scores rank i).indicator (fun _ => (1 : ℝ))) μ :=
    fun i => (integrable_const (1 : ℝ)).indicator (measurableSet_badEvent scores hm rank i)
  have hsum : (∫ ω, ∑ i, (badEvent scores rank i).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      ∑ i, μ.real (badEvent scores rank i) := by
    rw [integral_finsetSum Finset.univ (fun i _ => hInt i)]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [smul_eq_mul,mul_one] using
      (integral_indicator_const (μ := μ) (1 : ℝ) (measurableSet_badEvent scores hm rank i))
  rw [← hsum]
  calc
    (∫ ω, ∑ i, (badEvent scores rank i).indicator (fun _ => (1 : ℝ)) ω ∂μ)
        ≤ ∫ _ω : Ω, ((Fintype.card ι-rank : ℕ) : ℝ) ∂μ := by
      apply integral_mono (integrable_finsetSum Finset.univ (fun i _ => hInt i)) (integrable_const _)
      intro ω
      change (∑ i, (badEvent scores rank i).indicator (fun _ => (1 : ℝ)) ω) ≤
        ((Fintype.card ι-rank : ℕ) : ℝ)
      rw [bad_indicator_count]
      exact_mod_cast badIndices_card_bound (scores ω) rank
    _ = _ := by simp

theorem exchangeable_rank_failure_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (scores : Ω → ι → ℝ) (hm : Measurable scores)
    (hex : ∀ p : Equiv.Perm ι,
      IdentDistrib (fun ω i => scores ω (p i)) scores μ μ)
    (rank : ℕ) (i : ι) :
    μ.real (badEvent scores rank i) ≤
      ((Fintype.card ι-rank : ℕ) : ℝ)/(Fintype.card ι : ℝ) := by
  classical
  have heach : ∀ j, μ.real (badEvent scores rank j)=μ.real (badEvent scores rank i) := by
    intro j
    have h := exchangeable_bad_rank_equal μ scores hex (Equiv.swap i j) i rank
    simpa only [Equiv.swap_apply_left,badEvent,Measure.real] using congrArg ENNReal.toReal h
  have hsum := sum_bad_probabilities_le μ scores hm rank
  simp only [heach,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  exact (le_div_iff₀ (by exact_mod_cast Fintype.card_pos)).mpr (by simpa [mul_comm] using hsum)

/-- The kth calibration order statistic, retaining ties and adding infinity
when k exceeds the available calibration sample. The minimum of maxima of
k-element index subsets is the kth value, without deleting duplicate scores. -/
def calibrationThreshold {ι : Type*} [Fintype ι]
    (scores : ι → ℝ) (test : ι) (rank : ℕ) : EReal := by
  classical
  exact ((Finset.univ.erase test).powersetCard rank).inf
    (fun subset => subset.sup (fun j => (scores j : EReal)))

theorem calibration_failure_iff {ι : Type*} [Fintype ι]
    (scores : ι → ℝ) (test : ι) (rank : ℕ) :
    calibrationThreshold scores test rank < (scores test : EReal) ↔
      rank ≤ strictRank scores test := by
  classical
  unfold calibrationThreshold
  rw [Finset.inf_lt_iff]
  constructor
  · rintro ⟨subset,hsub,hmax⟩
    have hcard := (Finset.mem_powersetCard.mp hsub).2
    have hs : subset ⊆ Finset.univ.filter (fun j => scores j < scores test) := by
      intro j hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ j,?_⟩
      exact EReal.coe_lt_coe_iff.mp
        (lt_of_le_of_lt (Finset.le_sup (f := fun j => (scores j : EReal)) hj) hmax)
    have hc := Finset.card_le_card hs
    simpa only [hcard,strictRank] using hc
  · intro h
    obtain ⟨subset,hsub,hcard⟩ := Finset.exists_subset_card_eq h
    refine ⟨subset,Finset.mem_powersetCard.mpr ⟨?_,hcard⟩,?_⟩
    · intro j hj
      have hjlt := (Finset.mem_filter.mp (hsub hj)).2
      have hne : j ≠ test := by intro he;rw [he] at hjlt;exact (lt_irrefl _) hjlt
      exact Finset.mem_erase.mpr ⟨hne,Finset.mem_univ j⟩
    · apply (Finset.sup_lt_iff (EReal.bot_lt_coe _)).mpr
      intro j hj
      exact EReal.coe_lt_coe_iff.mpr ((Finset.mem_filter.mp (hsub hj)).2)

theorem unavailable_calibration_rank {ι : Type*} [Fintype ι]
    (scores : ι → ℝ) (test : ι) (rank : ℕ) (h : Fintype.card ι-1 < rank) :
    calibrationThreshold scores test rank = ⊤ := by
  classical
  unfold calibrationThreshold
  have he : (Finset.univ.erase test).powersetCard rank=∅ := by
    rw [Finset.powersetCard_eq_empty,Finset.card_erase_of_mem (Finset.mem_univ test),Finset.card_univ]
    exact h
  rw [he,Finset.inf_empty]

theorem conformal_failure_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (scores : Ω → ι → ℝ) (hm : Measurable scores)
    (hex : ∀ p : Equiv.Perm ι,
      IdentDistrib (fun ω i => scores ω (p i)) scores μ μ)
    (rank : ℕ) (test : ι) :
    μ.real {ω | calibrationThreshold (scores ω) test rank < (scores ω test : EReal)} ≤
      ((Fintype.card ι-rank : ℕ) : ℝ)/(Fintype.card ι : ℝ) := by
  have he : {ω | calibrationThreshold (scores ω) test rank < (scores ω test : EReal)} =
      badEvent scores rank test := by
    ext ω
    exact calibration_failure_iff (scores ω) test rank
  rw [he]
  exact exchangeable_rank_failure_bound μ scores hm hex rank test

theorem conformal_success_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (scores : Ω → ι → ℝ) (hm : Measurable scores)
    (hex : ∀ p : Equiv.Perm ι,
      IdentDistrib (fun ω i => scores ω (p i)) scores μ μ)
    (rank : ℕ) (test : ι) :
    1-((Fintype.card ι-rank : ℕ) : ℝ)/(Fintype.card ι : ℝ) ≤
      μ.real {ω | (scores ω test : EReal) ≤ calibrationThreshold (scores ω) test rank} := by
  have he : {ω | (scores ω test : EReal) ≤ calibrationThreshold (scores ω) test rank} =
      (badEvent scores rank test)ᶜ := by
    ext ω
    simp only [mem_ofPred_eq,mem_compl_iff,badEvent]
    rw [← calibration_failure_iff]
    exact not_lt.symm
  rw [he,probReal_compl_eq_one_sub (measurableSet_badEvent scores hm rank test)]
  linarith [exchangeable_rank_failure_bound μ scores hm hex rank test]

def conformalRank (sampleCount : ℕ) (alpha : ℝ) : ℕ :=
  Nat.ceil (((sampleCount+1 : ℕ) : ℝ)*(1-alpha))

theorem conformalRank_le (n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) :
    conformalRank n alpha ≤ n+1 := by
  unfold conformalRank
  apply Nat.ceil_le.mpr
  have hn : (0 : ℝ) ≤ n+1 := by positivity
  push_cast
  nlinarith

theorem conformalRank_coverage_arithmetic (n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) :
    1-alpha ≤ 1-(((n+1-conformalRank n alpha : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)) := by
  have hle := conformalRank_le n alpha ha
  have hceil := Nat.le_ceil (((n+1 : ℕ) : ℝ)*(1-alpha))
  have hpos : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  rw [Nat.cast_sub hle]
  apply sub_le_sub_left
  apply (div_le_iff₀ hpos).mpr
  change ((n+1 : ℕ) : ℝ)-conformalRank n alpha ≤ alpha*((n+1 : ℕ) : ℝ)
  unfold conformalRank
  nlinarith

theorem split_conformal_coverage {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (scores : Ω → Fin (n+1) → ℝ) (hm : Measurable scores)
    (hex : ∀ p : Equiv.Perm (Fin (n+1)),
      IdentDistrib (fun ω i => scores ω (p i)) scores μ μ)
    (alpha : ℝ) (ha : 0 ≤ alpha) (test : Fin (n+1)) :
    1-alpha ≤ μ.real {ω | (scores ω test : EReal) ≤
      calibrationThreshold (scores ω) test (conformalRank n alpha)} := by
  have h := conformal_success_bound μ scores hm hex (conformalRank n alpha) test
  simp only [Fintype.card_fin] at h
  exact (conformalRank_coverage_arithmetic n alpha ha).trans h

theorem rank_nineteen_ten_percent : conformalRank 19 (1/10) = 18 := by
  norm_num [conformalRank,Nat.ceil_eq_iff]

theorem rank_nineteen_one_percent : conformalRank 19 (1/100) = 20 := by
  norm_num [conformalRank,Nat.ceil_eq_iff]

theorem nineteen_calibration_coverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (scores : Ω → Fin 20 → ℝ) (hm : Measurable scores)
    (hex : ∀ p : Equiv.Perm (Fin 20),
      IdentDistrib (fun ω i => scores ω (p i)) scores μ μ) (test : Fin 20) :
    (9/10 : ℝ) ≤ μ.real {ω | (scores ω test : EReal) ≤
      calibrationThreshold (scores ω) test 18} := by
  have h := split_conformal_coverage 19 μ scores hm hex (1/10) (by norm_num) test
  norm_num only [rank_nineteen_ten_percent] at h
  exact h

theorem nineteen_one_percent_infinite (scores : Fin 20 → ℝ) (test : Fin 20) :
    calibrationThreshold scores test (conformalRank 19 (1/100)) = ⊤ := by
  rw [rank_nineteen_one_percent]
  exact unavailable_calibration_rank scores test 20 (by simp)

end SafeLearning.CompleteConformal
