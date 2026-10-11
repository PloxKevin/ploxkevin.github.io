import SafeLearning.Modules
import SafeLearning.CompleteAppliedBinomialModel
import SafeLearning.CompleteModulesGPNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 1000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace SafeLearning.CompleteModulesVerificationScenarioThree20

def sourceTail (n : ℕ) : ℝ :=
  (9/10 : ℝ)^n + (n : ℝ)*(1/10)*(9/10)^(n-1) +
    (n.choose 2 : ℝ)*(1/10)^2*(9/10)^(n-2)

theorem actual_independent_count_lower_tail_is_the_source_polynomial
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (A : Fin n → Set Ω) (hm : ∀ i,MeasurableSet (A i))
    (hi : iIndepSet A P) (hp : ∀ i,P.real (A i)=(1/10 : ℝ)) :
    P.real {w | CompleteAppliedFailureCounts.failureCount A w ≤ 2} = sourceTail n := by
  let count := CompleteAppliedFailureCounts.failureCount A
  have hcount : Measurable count := CompleteAppliedBinomialModel.failure_count_measurable A hm
  have hmeas (k : ℕ) : MeasurableSet {w | count w=k} := by
    exact hcount (measurableSet_singleton k)
  have he : {w | count w ≤ 2} = ({w | count w=0} ∪ {w | count w=1}) ∪ {w | count w=2} := by
    ext w;simp only [mem_ofPred_eq,mem_union];omega
  have h01 : Disjoint {w | count w=0} {w | count w=1} := by
    apply Set.disjoint_left.mpr;intro w h0 h1;dsimp at h0 h1;omega
  have h012 : Disjoint ({w | count w=0} ∪ {w | count w=1}) {w | count w=2} := by
    apply Set.disjoint_left.mpr;intro w h01 h2;rcases h01 with h0|h1 <;> dsimp at * <;> omega
  change P.real {w | count w ≤ 2} = _
  rw [he,measureReal_union h012 (hmeas 2),measureReal_union h01 (hmeas 1)]
  change P.real {w | CompleteAppliedFailureCounts.failureCount A w=0}+
    P.real {w | CompleteAppliedFailureCounts.failureCount A w=1}+
    P.real {w | CompleteAppliedFailureCounts.failureCount A w=2} = _
  rw [CompleteAppliedBinomialModel.actual_binomial_count_mass P n A hm hi (1/10) hp 0,
    CompleteAppliedBinomialModel.actual_binomial_count_mass P n A hm hi (1/10) hp 1,
    CompleteAppliedBinomialModel.actual_binomial_count_mass P n A hm hi (1/10) hp 2]
  norm_num [sourceTail]

theorem actual_tail_is_nonincreasing_in_all_sample_counts : Antitone sourceTail := by
  apply antitone_nat_of_succ_le
  intro n
  rcases n with _|n
  · norm_num [sourceTail]
  rcases n with _|k
  · norm_num [sourceTail]
  have h := Modules.scenario_tail_step k (1/10) (by norm_num) (by norm_num)
  change sourceTail (k+3) ≤ sourceTail (k+2)
  norm_num at h
  convert h using 1 <;>
    simp [sourceTail,Nat.cast_choose_two,Nat.cast_add,
      show (k+3-1 : ℕ)=k+2 by omega,show (k+3-2 : ℕ)=k+1 by omega,
      show (k+2-1 : ℕ)=k+1 by omega,show (k+2-2 : ℕ)=k by omega] <;> ring

theorem actual_sixty_and_sixty_one_source_eight_decimal_enclosures :
    |sourceTail 60-(5304508/100000000 : ℝ)|<1/200000000 ∧
    |sourceTail 61-(4911828/100000000 : ℝ)|<1/200000000 ∧
    (1/20 : ℝ)<sourceTail 60 ∧ sourceTail 61≤1/20 := by
  rw [sourceTail,sourceTail,Modules.scenario_choose_60,Modules.scenario_choose_61]
  norm_num

theorem actual_least_sample_count_for_the_exact_tail_is_sixty_one (n : ℕ) :
    sourceTail n≤(1/20 : ℝ) ↔ 61≤n := by
  obtain ⟨_,_,h60,h61⟩ := actual_sixty_and_sixty_one_source_eight_decimal_enclosures
  constructor
  · intro h
    by_contra hn
    have hn60 : n≤60 := by omega
    have hm := actual_tail_is_nonincreasing_in_all_sample_counts hn60
    linarith
  · intro hn
    exact (actual_tail_is_nonincreasing_in_all_sample_counts hn).trans h61

theorem actual_explicit_logarithmic_rule_and_least_integer (n : ℕ) :
    |20*(Real.log 20+3)-(11991465/100000 : ℝ)|<1/200000 ∧
      (20*(Real.log 20+3)≤(n : ℝ) ↔ 120≤n) := by
  obtain ⟨hl,hu⟩ := CompleteModulesGPNumerics.log_twenty_enclosure
  have h119 : (119 : ℝ)<20*(Real.log 20+3) := by linarith
  have h120 : 20*(Real.log 20+3)<(120 : ℝ) := by linarith
  constructor
  · rw [abs_lt];constructor <;> linarith
  · constructor
    · intro h
      have h' : (119 : ℝ)<n := h119.trans_le h
      have hh : 119<n := by exact_mod_cast h'
      omega
    · intro hn
      have h' : (120 : ℝ)≤n := by exact_mod_cast hn
      exact h120.le.trans h'

theorem actual_design_confidence_interprets_a_violation_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (populationViolation : Ω → ℝ) (hm : Measurable populationViolation)
    (n : ℕ) (hn : 61≤n)
    (givenScenarioTheoremBound : P.real {sample | (1/10 : ℝ)<populationViolation sample} ≤ sourceTail n) :
    (19/20 : ℝ)≤P.real {sample | populationViolation sample≤(1/10 : ℝ)} := by
  have hb := givenScenarioTheoremBound.trans ((actual_least_sample_count_for_the_exact_tail_is_sixty_one n).mpr hn)
  have he : {sample | (1/10 : ℝ)<populationViolation sample}ᶜ =
      {sample | populationViolation sample≤(1/10 : ℝ)} := by ext sample;simp
  have hmeas : MeasurableSet {sample | (1/10 : ℝ)<populationViolation sample} :=
    measurableSet_lt measurable_const hm
  have hc := probReal_compl_eq_one_sub (μ := P) hmeas
  rw [he] at hc;linarith

end SafeLearning.CompleteModulesVerificationScenarioThree20
