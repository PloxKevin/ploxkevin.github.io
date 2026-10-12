import SafeLearning.CompleteLyapunovScenarioNumbers23
import SafeLearning.CompleteModulesGPNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 3000
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace SafeLearning.CompleteModulesScenarioSamplesExact30

open CompleteLyapunovScenarioNumbers23

def oldSupportUnionBound (n d : ℕ) (epsilon : ℝ) : ℝ :=
  (n.choose d : ℝ) * (1-epsilon)^(n-d)

theorem actual_binomial_tail_antitone_after_support_dimension
    (s : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Antitone (fun k : ℕ => lowerTail (k+s) (s+1) p) := by
  apply antitone_nat_of_succ_le
  intro k
  simpa only [Nat.add_assoc, Nat.add_comm 1 s] using
    actual_binomial_tail_nonincrease (k+s) s p (by omega) hp hp1

theorem actual_zero_success_mass_is_a_lower_bound_for_the_tail
    (n s : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-p)^n ≤ lowerTail n (s+1) p := by
  have h := Finset.single_le_sum (f := fun i => binomialMass n i p)
    (fun i _ => by unfold binomialMass; positivity)
    (show 0 ∈ Finset.range (s+1) by simp)
  simpa [binomialMass, lowerTail] using h

theorem actual_adjacent_tail_crossing_determines_the_least_integer
    (s N : ℕ) (p beta : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hN : s ≤ N) (hsmall : beta < (1-p)^s)
    (hbefore : beta < lowerTail N (s+1) p)
    (hafter : lowerTail (N+1) (s+1) p ≤ beta) (n : ℕ) :
    lowerTail n (s+1) p ≤ beta ↔ N+1 ≤ n := by
  have hm := actual_binomial_tail_antitone_after_support_dimension s p hp hp1
  constructor
  · intro h
    by_contra hn
    have hnN : n ≤ N := by omega
    by_cases hs : s ≤ n
    · have hmono := hm (show n-s ≤ N-s by omega)
      have hn' : n-s+s=n := by omega
      have hN' : N-s+s=N := by omega
      dsimp only at hmono
      dsimp only at hmono
    rw [hn',hN'] at hmono
      exact not_le_of_gt hbefore (hmono.trans h)
    · have hns : n ≤ s := by omega
      have hpow := pow_le_pow_of_le_one (sub_nonneg.mpr hp1)
        (show 1-p ≤ (1:ℝ) by linarith) hns
      exact not_le_of_gt hsmall (hpow.trans
        ((actual_zero_success_mass_is_a_lower_bound_for_the_tail n s p hp hp1).trans h))
  · intro hn
    have hmono := hm (show N+1-s ≤ n-s by omega)
    have hn' : n-s+s=n := by omega
    have hN' : N+1-s+s=N+1 := by omega
    dsimp only at hmono
    rw [hn',hN'] at hmono
    exact hmono.trans hafter

theorem actual_ten_variable_one_millionth_tail_adjacent_crossing :
    (1/1000000:ℝ) < lowerTail 642 10 (1/20) ∧
      lowerTail 643 10 (1/20) < 1/1000000 := by
  norm_num [lowerTail,binomialMass,Finset.sum_range_succ,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem actual_exact_least_ten_variable_one_millionth_size (n : ℕ) :
    lowerTail n 10 (1/20) ≤ 1/1000000 ↔ 643 ≤ n := by
  apply actual_adjacent_tail_crossing_determines_the_least_integer 9 642 (1/20)
    (1/1000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    actual_ten_variable_one_millionth_tail_adjacent_crossing.1
    actual_ten_variable_one_millionth_tail_adjacent_crossing.2.le

theorem actual_thirty_six_variable_one_thousandth_tail_adjacent_crossing :
    (1/1000:ℝ) < lowerTail 1137 36 (1/20) ∧
      lowerTail 1138 36 (1/20) < 1/1000 := by
  norm_num [lowerTail,binomialMass,Finset.sum_range_succ,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem actual_exact_least_thirty_six_variable_one_thousandth_size (n : ℕ) :
    lowerTail n 36 (1/20) ≤ 1/1000 ↔ 1138 ≤ n := by
  apply actual_adjacent_tail_crossing_determines_the_least_integer 35 1137 (1/20)
    (1/1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    actual_thirty_six_variable_one_thousandth_tail_adjacent_crossing.1
    actual_thirty_six_variable_one_thousandth_tail_adjacent_crossing.2.le

theorem actual_old_ten_support_union_bound_adjacent_crossing :
    (1/1000000:ℝ) < oldSupportUnionBound 1395 10 (1/20) ∧
      oldSupportUnionBound 1396 10 (1/20) < 1/1000000 := by
  norm_num [oldSupportUnionBound,Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,Nat.factorial]

theorem actual_old_ten_support_union_bound_successor_nonincrease
    (n : ℕ) (hn : 199 ≤ n) :
    oldSupportUnionBound (n+1) 10 (1/20) ≤ oldSupportUnionBound n 10 (1/20) := by
  have hc : (n.choose 10:ℝ)*((n:ℝ)+1)=
      ((n+1).choose 10:ℝ)*((n:ℝ)+1-10) := by
    have h : (n.choose 10:ℝ)*((n+1:ℕ):ℝ)=
        ((n+1).choose 10:ℝ)*((n+1-10:ℕ):ℝ) := by
      exact_mod_cast Nat.choose_mul_succ_eq n 10
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub (show 10 ≤ n+1 by omega)] using h
  have hnreal : (199:ℝ) ≤ n := by exact_mod_cast hn
  have he : n+1-10=(n-10)+1 := by omega
  have hmul : ((n:ℝ)+1-10)*oldSupportUnionBound (n+1) 10 (1/20)=
      ((n:ℝ)+1)*(19/20)*oldSupportUnionBound n 10 (1/20) := by
    unfold oldSupportUnionBound
    norm_num only [show (1-(1/20:ℝ))=19/20 by norm_num]
    rw [he,pow_succ]
    have h := congrArg (fun z : ℝ => z*((19/20:ℝ)^(n-10)*19/20)) hc
    nlinarith [h]
  have hnonneg : 0 ≤ oldSupportUnionBound n 10 (1/20) := by
    unfold oldSupportUnionBound; positivity
  have hcoef : ((n:ℝ)+1)*(19/20) ≤ (n:ℝ)+1-10 := by linarith
  have hle := mul_le_mul_of_nonneg_right hcoef hnonneg
  nlinarith

theorem actual_old_ten_support_union_bound_antitone_from_one_ninety_nine :
    Antitone (fun k : ℕ => oldSupportUnionBound (k+199) 10 (1/20)) := by
  apply antitone_nat_of_succ_le
  intro k
  convert actual_old_ten_support_union_bound_successor_nonincrease (k+199) (by omega)
    using 1

theorem actual_old_support_bound_cannot_succeed_before_one_ninety_nine
    (n : ℕ) (hn : 10 ≤ n) (hn' : n ≤ 199) :
    (1/1000000:ℝ) < oldSupportUnionBound n 10 (1/20) := by
  have hc : (1:ℝ) ≤ n.choose 10 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos hn).ne')
  have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 19/20)
    (by norm_num : (19/20:ℝ) ≤ 1) (show n-10 ≤ 189 by omega)
  have hnum : (1/1000000:ℝ) < (19/20)^189 := by norm_num
  unfold oldSupportUnionBound
  norm_num only [show (1-(1/20:ℝ))=19/20 by norm_num]
  exact hnum.trans_le (hp.trans (by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤19/20) (n-10)]))

theorem actual_exact_least_old_ten_support_bound_size_on_its_design_domain
    (n : ℕ) (hn : 10 ≤ n) :
    oldSupportUnionBound n 10 (1/20) ≤ 1/1000000 ↔ 1396 ≤ n := by
  have hm := actual_old_ten_support_union_bound_antitone_from_one_ninety_nine
  constructor
  · intro h
    by_contra hlarge
    by_cases hsmall : n ≤ 199
    · exact not_le_of_gt
        (actual_old_support_bound_cannot_succeed_before_one_ninety_nine n hn hsmall) h
    · have hmono := hm (show n-199 ≤ 1196 by omega)
      have he : n-199+199=n := by omega
      norm_num only [he,show (1196+199:ℕ)=1395 by rfl] at hmono
      exact not_le_of_gt actual_old_ten_support_union_bound_adjacent_crossing.1
        (hmono.trans h)
  · intro hn'
    have hmono := hm (show 1197 ≤ n-199 by omega)
    have he : n-199+199=n := by omega
    norm_num only [he,show (1197+199:ℕ)=1396 by rfl] at hmono
    exact hmono.trans actual_old_ten_support_union_bound_adjacent_crossing.2.le

theorem actual_logarithm_of_ten_rigorous_enclosure :
    (230258508/100000000:ℝ) < Real.log 10 ∧
      Real.log 10 < 230258510/100000000 := by
  have h20 := CompleteModulesGPNumerics.log_twenty_enclosure
  have h2 := Real.log_two_near_10
  have he : Real.log (10:ℝ)=Real.log 20-Real.log 2 := by
    rw [←Real.log_div (by norm_num : (20:ℝ)≠0) (by norm_num : (2:ℝ)≠0)]
    norm_num
  rw [he]
  constructor <;> linarith [(abs_le.mp h2).1,(abs_le.mp h2).2]

theorem actual_logarithms_three_and_six_decades :
    Real.log 1000=3*Real.log 10 ∧ Real.log 1000000=6*Real.log 10 := by
  constructor
  · rw [show (1000:ℝ)=10^3 by norm_num,Real.log_pow]; norm_num
  · rw [show (1000000:ℝ)=10^6 by norm_num,Real.log_pow]; norm_num

theorem actual_explicit_thresholds_have_least_integer_sizes_nine_fifty_three_and_seventeen_seventeen :
    Nat.ceil (40*(Real.log 1000000+10))=953 ∧
      Nat.ceil (40*(Real.log 1000+36))=1717 := by
  obtain ⟨hl,hu⟩ := actual_logarithm_of_ten_rigorous_enclosure
  obtain ⟨he3,he6⟩ := actual_logarithms_three_and_six_decades
  rw [he3,he6]
  constructor
  · apply (Nat.ceil_eq_iff (by norm_num : (953:ℕ)≠0)).mpr
    constructor <;> norm_num <;> linarith
  · apply (Nat.ceil_eq_iff (by norm_num : (1717:ℕ)≠0)).mpr
    constructor <;> norm_num <;> linarith

theorem actual_printed_logarithms_and_explicit_cutoffs_are_rounded_displays :
    |Real.log 1000000-13816/1000|<1/2000 ∧
      |Real.log 1000-6908/1000|<1/2000 ∧
      |40*(Real.log 1000000+10)-9526/10|<1/20 ∧
      |40*(Real.log 1000+36)-17163/10|<1/20 ∧
      Real.log 1000000≠13816/1000 ∧ Real.log 1000≠6908/1000 := by
  obtain ⟨hl,hu⟩ := actual_logarithm_of_ten_rigorous_enclosure
  obtain ⟨he3,he6⟩ := actual_logarithms_three_and_six_decades
  rw [he3,he6]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> linarith
  · intro h;linarith
  · intro h;linarith

theorem actual_chernoff_parameter_is_admissible_exactly_on_the_mean_domain
    (d mu : ℝ) (hd : 0 ≤ d) (hm : 0 < mu) :
    (1-d/mu) ∈ Icc (0:ℝ) 1 ↔ d ≤ mu := by
  rw [mem_Icc]
  have hnonneg : 0 ≤ d/mu := div_nonneg hd hm.le
  have hdiv : d/mu ≤ 1 ↔ d ≤ mu := by rw [div_le_iff₀ hm];simp
  constructor
  · intro h;exact hdiv.mp (by linarith [h.1])
  · intro h;exact ⟨by linarith [hdiv.mpr h],by linarith⟩

theorem actual_chernoff_exponent_retains_a_nonnegative_quadratic_slack
    (d mu : ℝ) (hm : mu≠0) :
    (1-d/mu)^2*mu/2=mu/2-d+d^2/(2*mu) := by
  field_simp
  ring

theorem actual_explicit_rule_places_the_chernoff_parameter_in_its_domain
    (d beta epsilon N : ℝ) (hd : 0 ≤ d) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (he : 0 < epsilon) (hN : (2/epsilon)*(Real.log (1/beta)+d) ≤ N)
    (hm : 0 < N*epsilon) :
    d ≤ N*epsilon ∧ (1-d/(N*epsilon)) ∈ Icc (0:ℝ) 1 := by
  have hlog : 0 ≤ Real.log (1/beta) :=
    Real.log_nonneg ((one_le_div hb).mpr hb1)
  have hscale := (mul_le_mul_of_nonneg_right hN he.le)
  have heq : ((2/epsilon)*(Real.log (1/beta)+d))*epsilon=
      2*(Real.log (1/beta)+d) := by field_simp
  rw [heq] at hscale
  have h : d ≤ N*epsilon := by linarith
  exact ⟨h,(actual_chernoff_parameter_is_admissible_exactly_on_the_mean_domain
    d (N*epsilon) hd hm).mpr h⟩

theorem actual_common_lyapunov_lmi_parameter_count_four_states_one_input :
    (2*4^2+4*1:ℕ)=36 := by norm_num

theorem actual_exact_explicit_and_old_counts_are_strictly_ordered :
    (643:ℕ)<953 ∧ (953:ℕ)<1396 ∧ (1138:ℕ)<1717 ∧
      |((953-643:ℝ)/643)-1/2|<1/50 := by norm_num

end SafeLearning.CompleteModulesScenarioSamplesExact30
