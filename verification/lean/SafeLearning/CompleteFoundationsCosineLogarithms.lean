import SafeLearning.CompleteFoundationsCosineIterates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
noncomputable section
namespace SafeLearning.CompleteFoundationsCosineLogarithms
open scoped BigOperators

def expPartial16 (x : ℝ) : ℝ := ∑ m∈Finset.range 16,x^m/(m.factorial:ℝ)
def expRemainder16 (x : ℝ) : ℝ := |x|^16*(17/((16:ℕ).factorial*16:ℝ))

theorem actual_log_lower_from_negative_exponential_series (target value bound : ℝ)
    (ht : 0<target) (hb : 0≤bound) (hsmall : |(-value/16)|≤1)
    (hseries : bound≤expPartial16 (-value/16)-expRemainder16 (-value/16))
    (hpow : 1/target<bound^16) : value<Real.log target := by
  have h := Real.exp_bound hsmall (n:=16) (by norm_num)
  change |Real.exp (-value/16)-expPartial16 (-value/16)|≤expRemainder16 (-value/16) at h
  have hl : bound≤Real.exp (-value/16) := by linarith [(abs_le.mp h).1]
  have hp := pow_le_pow_left₀ hb hl 16
  have he : (Real.exp (-value/16))^16=Real.exp (-value) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have htlog : Real.exp (-Real.log target)=1/target := by rw [Real.exp_neg,Real.exp_log ht,one_div]
  have hlt : Real.exp (-Real.log target)<Real.exp (-value) := by rw [htlog,←he];exact hpow.trans_le hp
  have hlog := Real.exp_lt_exp.mp hlt
  linarith

theorem actual_log_upper_from_negative_exponential_series (target value bound : ℝ)
    (ht : 0<target) (hsmall : |(-value/16)|≤1)
    (hseries : expPartial16 (-value/16)+expRemainder16 (-value/16)≤bound)
    (hpow : bound^16<1/target) : Real.log target<value := by
  have h := Real.exp_bound hsmall (n:=16) (by norm_num)
  change |Real.exp (-value/16)-expPartial16 (-value/16)|≤expRemainder16 (-value/16) at h
  have hu : Real.exp (-value/16)≤bound := by linarith [(abs_le.mp h).2]
  have hp := pow_le_pow_left₀ (Real.exp_nonneg _) hu 16
  have he : (Real.exp (-value/16))^16=Real.exp (-value) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have htlog : Real.exp (-Real.log target)=1/target := by rw [Real.exp_neg,Real.exp_log ht,one_div]
  have hlt : Real.exp (-value)<Real.exp (-Real.log target) := by rw [htlog,←he];exact hp.trans_lt hpow
  have hlog := Real.exp_lt_exp.mp hlt
  linarith

theorem actual_rounded_apriori_numerator_log_enclosure :
    (148803299000/10000000000:ℝ)<Real.log (4597000000/1585:ℝ) ∧ Real.log (4597000000/1585:ℝ)<(148803302000/10000000000:ℝ) := by
  constructor
  · apply actual_log_lower_from_negative_exponential_series (4597000000/1585) (148803299000/10000000000:ℝ) (394545575250/1000000000000)
      (by norm_num) (by norm_num) (by norm_num)
    · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
    · norm_num
  · apply actual_log_upper_from_negative_exponential_series (4597000000/1585) (148803302000/10000000000:ℝ) (394545567855/1000000000000)
      (by norm_num) (by norm_num)
    · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
    · norm_num

theorem actual_rounded_apriori_denominator_log_enclosure :
    (1725692653/10000000000:ℝ)<Real.log (2000/1683:ℝ) ∧ Real.log (2000/1683:ℝ)<(1725692654/10000000000:ℝ) := by
  constructor
  · apply actual_log_lower_from_negative_exponential_series (2000/1683) (1725692653/10000000000:ℝ) (989272376726/1000000000000)
      (by norm_num) (by norm_num) (by norm_num)
    · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
    · norm_num
  · apply actual_log_upper_from_negative_exponential_series (2000/1683) (1725692654/10000000000:ℝ) (989272376723/1000000000000)
      (by norm_num) (by norm_num)
    · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
    · norm_num

theorem actual_local_estimate_numerator_log_enclosure :
    (124722756000/10000000000:ℝ)<Real.log (261000:ℝ) ∧ Real.log (261000:ℝ)<(124722758000/10000000000:ℝ) := by
  constructor
  · apply actual_log_lower_from_negative_exponential_series (261000) (124722756000/10000000000:ℝ) (458627371695/1000000000000)
      (by norm_num) (by norm_num) (by norm_num)
    · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
    · norm_num
  · apply actual_log_upper_from_negative_exponential_series (261000) (124722758000/10000000000:ℝ) (458627365965/1000000000000)
      (by norm_num) (by norm_num)
    · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
    · norm_num

theorem actual_local_estimate_denominator_log_enclosure :
    (3945251680/10000000000:ℝ)<Real.log (500/337:ℝ) ∧ Real.log (500/337:ℝ)<(3945251682/10000000000:ℝ) := by
  constructor
  · apply actual_log_lower_from_negative_exponential_series (500/337) (3945251680/10000000000:ℝ) (975643697750/1000000000000)
      (by norm_num) (by norm_num) (by norm_num)
    · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
    · norm_num
  · apply actual_log_upper_from_negative_exponential_series (500/337) (3945251682/10000000000:ℝ) (975643697741/1000000000000)
      (by norm_num) (by norm_num)
    · norm_num [expPartial16,expRemainder16,Finset.sum_range_succ,Nat.factorial]
    · norm_num

theorem actual_rounded_worked_logarithms_and_ratio :
    |Real.log (4597000000/1585:ℝ)-(1488/100:ℝ)|<1/200 ∧
      |Real.log (2000/1683:ℝ)-(1726/10000:ℝ)|<1/20000 ∧
      |Real.log (4597000000/1585:ℝ)/Real.log (2000/1683:ℝ)-(862/10:ℝ)|<1/20 ∧
      |(1488/100:ℝ)/(1726/10000)-(862/10:ℝ)|<1/20 := by
  have hn := actual_rounded_apriori_numerator_log_enclosure
  have hd := actual_rounded_apriori_denominator_log_enclosure
  have hdpos : 0<Real.log (2000/1683:ℝ) := by linarith [hd.1]
  constructor
  · rw [abs_lt];constructor <;> linarith [hn.1,hn.2]
  constructor
  · rw [abs_lt];constructor <;> linarith [hd.1,hd.2]
  constructor
  · rw [abs_lt]
    constructor
    · have hh : (8615/100:ℝ)<Real.log (4597000000/1585:ℝ)/Real.log (2000/1683:ℝ) := by
        apply (lt_div_iff₀ hdpos).mpr
        nlinarith [hn.1,hd.2]
      linarith
    · have hh : Real.log (4597000000/1585:ℝ)/Real.log (2000/1683:ℝ)<(8625/100:ℝ) := by
        apply (div_lt_iff₀ hdpos).mpr
        nlinarith [hn.2,hd.1]
      linarith
  · norm_num

theorem actual_local_rounded_data_log_estimate_rounding :
    |Real.log (261000:ℝ)/Real.log (500/337:ℝ)-(316/10:ℝ)|<1/20 := by
  have hn := actual_local_estimate_numerator_log_enclosure
  have hd := actual_local_estimate_denominator_log_enclosure
  have hdpos : 0<Real.log (500/337:ℝ) := by linarith [hd.1]
  rw [abs_lt]
  constructor
  · have hh : (3155/100:ℝ)<Real.log (261000:ℝ)/Real.log (500/337:ℝ) := by
      apply (lt_div_iff₀ hdpos).mpr
      nlinarith [hn.1,hd.2]
    linarith
  · have hh : Real.log (261000:ℝ)/Real.log (500/337:ℝ)<(3165/100:ℝ) := by
      apply (div_lt_iff₀ hdpos).mpr
      nlinarith [hn.2,hd.1]
    linarith

end SafeLearning.CompleteFoundationsCosineLogarithms
