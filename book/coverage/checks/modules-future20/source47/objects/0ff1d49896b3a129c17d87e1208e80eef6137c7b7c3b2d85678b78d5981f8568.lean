import SafeLearning.CompleteModulesConformal
import SafeLearning.CompleteModulesTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SafeLearning.CompleteModulesVerificationFinitePractices20
open CompleteConformal CompleteModulesConformal CompleteModulesTheory

def firstLogit (x : ℝ) : ℝ := 2*x+1
def secondLogit (x : ℝ) : ℝ := -x+2
def labelViolation (x : ℝ) : ℝ := secondLogit x-firstLogit x

theorem actual_source_label_objective_and_greatest_violation :
    (∀ x : ℝ, labelViolation x=1-3*x) ∧
      IsGreatest (labelViolation '' Icc (0 : ℝ) 1) 1 ∧
      firstLogit 0=1 ∧ secondLogit 0=2 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x; unfold labelViolation firstLogit secondLogit; ring
  · constructor
    · refine ⟨0,by norm_num,?_⟩
      norm_num [labelViolation,firstLogit,secondLogit]
    · rintro y ⟨x,hx,rfl⟩
      dsimp [labelViolation,firstLogit,secondLogit]
      linarith [hx.1]
  · norm_num [firstLogit]
  · norm_num [secondLogit]

theorem actual_positive_relaxation_upper_bound_alone_cannot_prove_failure :
    (∀ x ∈ Icc (0 : ℝ) 1, (-1 : ℝ) ≤ 7/5) ∧
      ¬(∃ x ∈ Icc (0 : ℝ) 1, (0 : ℝ)< -1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, labelViolation x ≤ 7/5) ∧
      0 < labelViolation 0 := by
  refine ⟨by norm_num,by norm_num,?_,?_⟩
  · intro x hx
    have h := (actual_source_label_objective_and_greatest_violation.2.1.2
      (show labelViolation x ∈ labelViolation '' Icc (0 : ℝ) 1 from ⟨x,hx,rfl⟩))
    linarith
  · norm_num [labelViolation,firstLogit,secondLogit]

def relu (x : ℝ) : ℝ := max x 0
def duplicateActivation (x : ℝ) : ℝ×ℝ := (relu x,relu x)
def duplicateOutput (x : ℝ) : ℝ := (duplicateActivation x).1-(duplicateActivation x).2

theorem actual_duplicate_relu_coordinate_ranges_are_the_closed_unit_interval :
    relu '' Icc (-1 : ℝ) 1=Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨le_max_right _ _,max_le hx.2 (by norm_num)⟩
  · intro hy
    refine ⟨y,⟨by linarith [hy.1],hy.2⟩,?_⟩
    exact max_eq_left hy.1

theorem actual_independent_activation_rectangle_has_interval_minus_one_one :
    (fun a : ℝ×ℝ => a.1-a.2) ''
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)=Icc (-1 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨by linarith [ha.1.1,ha.2.2],by linarith [ha.1.2,ha.2.1]⟩
  · intro hy
    by_cases hp : 0 ≤ y
    · refine ⟨(y,0),?_,by simp⟩
      exact ⟨⟨hp,hy.2⟩,by norm_num⟩
    · refine ⟨(0,-y),?_,by simp⟩
      exact ⟨by norm_num,⟨by linarith,by linarith [hy.1]⟩⟩

theorem actual_duplicate_relu_output_set_and_preserved_equality :
    (∀ x : ℝ, (duplicateActivation x).1=(duplicateActivation x).2) ∧
      duplicateOutput '' Icc (-1 : ℝ) 1={0} ∧
      ({0} : Set ℝ) ⊆ Icc (-1 : ℝ) 1 := by
  refine ⟨fun _ => rfl,?_,?_⟩
  · ext y
    constructor
    · rintro ⟨x,hx,rfl⟩; simp [duplicateOutput,duplicateActivation]
    · intro hy
      have h : y=0 := hy
      subst y
      refine ⟨0,by norm_num,?_⟩
      simp [duplicateOutput,duplicateActivation]
  · intro x hx
    have h : x=0 := hx
    subst x; norm_num

def nineSortedScores (i : Fin 10) : ℝ := (i.val+1 : ℝ)/10
def firstEight : Finset (Fin 10) := Finset.univ.filter (fun i => i.val<8)
def firstSeven : Finset (Fin 10) := Finset.univ.filter (fun i => i.val<7)

theorem actual_eighth_calibration_statistic_equals_point_eight :
    calibrationThreshold nineSortedScores 9 8=(4/5 : ℝ) := by
  classical
  letI : DecidableEq (Fin 10) := Classical.decEq _
  unfold calibrationThreshold
  apply le_antisymm
  · have hs : firstEight ∈ (Finset.univ.erase (9 : Fin 10)).powersetCard 8 := by
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro i hi
        have hlt : i.val<8 := (Finset.mem_filter.mp hi).2
        apply Finset.mem_erase.mpr
        refine ⟨?_,Finset.mem_univ _⟩
        intro h;subst i;norm_num at hlt
      · decide
    calc
      _ ≤ firstEight.sup (fun i => (nineSortedScores i : EReal)) :=
        Finset.inf_le (f := fun s : Finset (Fin 10) =>
          s.sup (fun i => (nineSortedScores i : EReal))) hs
      _ ≤ (4/5 : ℝ) := by
        apply Finset.sup_le
        intro i hi
        have hlt : i.val<8 := (Finset.mem_filter.mp hi).2
        apply EReal.coe_le_coe_iff.mpr
        unfold nineSortedScores
        have hv : (i.val : ℝ) ≤ 7 := by exact_mod_cast (show i.val≤7 by omega)
        linarith
  · refine Finset.le_inf (f := fun s : Finset (Fin 10) =>
        s.sup (fun i => (nineSortedScores i : EReal))) ?_
    intro s hs
    have hc : s.card=8 := (Finset.mem_powersetCard.mp hs).2
    have hsome : ∃ (i : Fin 10), i ∈ s ∧ (7 : ℕ) ≤ i.val := by
      by_contra hn
      push Not at hn
      have hsub : s ⊆ firstSeven := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn i hi⟩
      have hle := Finset.card_le_card hsub
      have hseven : firstSeven.card=7 := by decide
      omega
    obtain ⟨i,hi,hv⟩ := hsome
    apply Finset.le_sup_of_le hi
    apply EReal.coe_le_coe_iff.mpr
    unfold nineSortedScores
    have hr : (7 : ℝ) ≤ i.val := by exact_mod_cast hv
    linarith

theorem actual_sorted_scores_and_interval_endpoints :
    StrictMono nineSortedScores ∧ nineSortedScores 7=4/5 ∧
      {y : ℝ | |y-2|≤4/5}=Icc (6/5 : ℝ) (14/5) := by
  refine ⟨?_,by norm_num [nineSortedScores],?_⟩
  · intro i j hij
    unfold nineSortedScores
    have hr : (i.val : ℝ)<j.val := by exact_mod_cast hij
    linarith
  · ext y
    simp only [Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem actual_nine_score_marginal_coverage_retains_whole_exchangeability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (scores : Ω→Fin 10→ℝ) (hm : Measurable scores)
    (hex : ∀ p : Equiv.Perm (Fin 10),
      IdentDistrib (fun ω i => scores ω (p i)) scores P P) (test : Fin 10) :
    (4/5 : ℝ) ≤ P.real {ω | (scores ω test : EReal)≤
      calibrationThreshold (scores ω) test 8} := by
  have h := split_conformal_coverage 9 P scores hm hex (1/5) (by norm_num) test
  rw [nine_calibration_rank] at h
  norm_num at h ⊢
  exact h

theorem actual_joint_trajectory_exchangeability_gives_each_time_score_exchangeability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (scores : Ω→Fin 40→Fin 4→ℝ)
    (hex : ∀ p : Equiv.Perm (Fin 40),
      IdentDistrib (fun ω i => scores ω (p i)) scores P P)
    (time : Fin 4) (p : Equiv.Perm (Fin 40)) :
    IdentDistrib (fun ω i => scores ω (p i) time)
      (fun ω i => scores ω i time) P P := by
  let evaluation : (Fin 40→Fin 4→ℝ)→(Fin 40→ℝ) := fun v i => v i time
  have hm : Measurable evaluation := Measurable.of_eval
    (fun i => (measurable_pi_apply time).comp (measurable_pi_apply i))
  exact (hex p).comp hm

theorem actual_four_time_conformal_failure_budget_from_whole_trajectories
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (scores : Ω→Fin 40→Fin 4→ℝ) (hm : Measurable scores)
    (hex : ∀ p : Equiv.Perm (Fin 40),
      IdentDistrib (fun ω i => scores ω (p i)) scores P P) (test : Fin 40) :
    (9/10 : ℝ) ≤ P.real
      (⋂ time : Fin 4, {ω | (scores ω test time : EReal)≤
        calibrationThreshold (fun i => scores ω i time) test 39}) := by
  let family : Fin 4→Ω→Fin 40→ℝ := fun time ω i => scores ω i time
  have hmf : ∀ time,Measurable (family time) := fun time =>
    Measurable.of_eval (fun i =>
      (measurable_pi_apply time).comp ((measurable_pi_apply i).comp hm))
  have hbound : ∀ time,P.real (badEvent (family time) 39 test) ≤ (1/40 : ℝ) := by
    intro time
    have h := exchangeable_rank_failure_bound P (family time) (hmf time)
      (fun p => actual_joint_trajectory_exchangeability_gives_each_time_score_exchangeability
        P scores hex time p) 39 test
    norm_num at h ⊢
    exact h
  have h := simultaneous_success P (fun time => badEvent (family time) 39 test)
    (fun _ => (1/40 : ℝ)) (fun time => measurableSet_badEvent (family time) (hmf time) 39 test) hbound
  have he : ∀ time : Fin 4,(badEvent (family time) 39 test)ᶜ=
      {ω | (scores ω test time : EReal)≤calibrationThreshold (fun i => scores ω i time) test 39} := by
    intro time
    ext ω
    simp only [Set.mem_compl_iff,badEvent,Set.mem_ofPred_eq]
    rw [←calibration_failure_iff]
    exact not_lt
  simp_rw [he] at h
  norm_num at h ⊢
  exact h

theorem actual_twenty_trajectory_rank_is_unavailable (scores : Fin 20→ℝ)
    (test : Fin 20) : calibrationThreshold scores test (conformalRank 19 (1/40))=⊤ := by
  rw [thirty_nine_calibration_rank.2]
  exact unavailable_calibration_rank scores test 20 (by simp)

theorem actual_four_marginal_point_nine_events_give_only_the_union_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (failure : Fin 4→Set Ω) (hm : ∀ i,MeasurableSet (failure i))
    (hb : ∀ i,P.real (failure i)≤(1/10 : ℝ)) :
    (3/5 : ℝ) ≤ P.real (⋂ i,(failure i)ᶜ) := by
  have h := simultaneous_success P failure (fun _ => (1/10 : ℝ)) hm hb
  norm_num at h ⊢
  exact h

theorem actual_independent_four_point_nine_events_have_probability_point_six_five_six_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (safe : Fin 4→Set Ω) (hi : iIndepSet safe P)
    (hp : ∀ i,P.real (safe i)=(9/10 : ℝ)) :
    P.real (⋂ i,safe i)=(6561/10000 : ℝ) ∧ P.real (⋂ i,safe i)<9/10 := by
  rw [independent_success_product P safe hi]
  simp_rw [hp]
  norm_num

end SafeLearning.CompleteModulesVerificationFinitePractices20
