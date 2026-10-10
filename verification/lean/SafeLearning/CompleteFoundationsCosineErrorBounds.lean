import SafeLearning.CompleteFoundationsCosineIterates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
noncomputable section
namespace SafeLearning.CompleteFoundationsCosineErrorBounds
open Set
open SafeLearning.CompleteFoundationsCosineContraction
open SafeLearning.CompleteFoundationsCosineNumerics
open SafeLearning.CompleteFoundationsCosineIterates

def apriori (n : ℕ) : ℝ := (1-Real.cos 1)*(Real.sin 1)^n/(1-Real.sin 1)

def lowerApriori (n : ℕ) : ℝ :=
  (1-5403023059/10000000000)*(8414709847/10000000000)^n/(1-8414709847/10000000000)

def upperApriori (n : ℕ) : ℝ :=
  (1-5403023058/10000000000)*(8414709849/10000000000)^n/(1-8414709849/10000000000)

theorem actual_apriori_rational_sandwich (n : ℕ) : lowerApriori n≤apriori n ∧ apriori n≤upperApriori n := by
  have h := actual_sine_one_and_cosine_one_certified_enclosures
  have hs := actual_sine_one_strict_contraction_range
  have hc := actual_cosine_one_positive_and_below_one
  have hpl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8414709847/10000000000) h.1.le n
  have hpu := pow_le_pow_left₀ hs.1.le h.2.1.le n
  constructor
  · unfold lowerApriori apriori
    apply div_le_div₀ (mul_nonneg (sub_nonneg.mpr hc.2.le) (pow_nonneg hs.1.le n))
      (mul_le_mul (by linarith [h.2.2.2]) hpl (pow_nonneg (by norm_num) n)
        (sub_nonneg.mpr hc.2.le)) (by linarith [hs.2])
    linarith [h.1]
  · unfold apriori upperApriori
    apply div_le_div₀ (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) n))
      (mul_le_mul (by linarith [h.2.2.1]) hpu (pow_nonneg hs.1.le n) (by norm_num))
      (by norm_num)
    linarith [h.2.1]

theorem actual_apriori_antitone : Antitone apriori := by
  intro n m hnm
  have hs := actual_sine_one_strict_contraction_range
  have hpow : (Real.sin 1)^m≤(Real.sin 1)^n := by
    have hp : sourceConstant≤1 := by exact_mod_cast hs.2.le
    exact_mod_cast (pow_le_pow_right_of_le_one' hp hnm)
  unfold apriori
  apply div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by linarith [actual_cosine_one_positive_and_below_one.2]))
  linarith [hs.2]

theorem actual_first_permanent_apriori_tolerance_cutoff :
    (∀ n : ℕ,n<87→1/1000000<apriori n) ∧
      (∀ n : ℕ,87≤n→apriori n<1/1000000) := by
  have h86 := (actual_apriori_rational_sandwich 86).1
  have h87 := (actual_apriori_rational_sandwich 87).2
  have hl : (1/1000000:ℝ)<lowerApriori 86 := by norm_num [lowerApriori]
  have hu : upperApriori 87<(1/1000000:ℝ) := by norm_num [upperApriori]
  constructor
  · intro n hn
    exact (hl.trans_le h86).trans_le (actual_apriori_antitone (by omega : n≤86))
  · intro n hn
    exact (actual_apriori_antitone hn).trans_lt (h87.trans_lt hu)

theorem actual_all_iterations_from_eighty_seven_meet_tolerance (n : ℕ) (hn : 87≤n) :
    |Real.cos^[n] 1-(sourceFixedPoint:ℝ)|<1/1000000 :=
  (actual_source_apriori_bound n).trans_lt (actual_first_permanent_apriori_tolerance_cutoff.2 n hn)

theorem actual_apriori_at_ten_rounds_to_point_five_two :
    |apriori 10-(52/100:ℝ)|<1/200 := by
  have h := actual_apriori_rational_sandwich 10
  have hl : (515/1000:ℝ)<lowerApriori 10 := by norm_num [lowerApriori]
  have hu : upperApriori 10<(525/1000:ℝ) := by norm_num [upperApriori]
  rw [abs_lt]
  constructor <;> linarith [h.1,h.2]

theorem actual_posteriori_factor_rational_enclosure :
    (530799350/100000000:ℝ)<Real.sin 1/(1-Real.sin 1) ∧
      Real.sin 1/(1-Real.sin 1)<530799353/100000000 := by
  have h := actual_sine_one_and_cosine_one_certified_enclosures
  have hd : 0<1-Real.sin 1 := by linarith [actual_sine_one_strict_contraction_range.2]
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith [h.1]
  · apply (div_lt_iff₀ hd).mpr
    linarith [h.2.1]

def posterioriTen : ℝ := Real.sin 1/(1-Real.sin 1)*|Real.cos^[10] 1-Real.cos^[9] 1|

theorem actual_ninth_to_tenth_step_certified_enclosure :
    (1283331230/100000000000:ℝ) < |Real.cos^[10] 1-Real.cos^[9] 1| ∧
      |Real.cos^[10] 1-Real.cos^[9] 1|<1283331260/100000000000 := by
  have h9 := actual_source_first_thirty_two_iterations_enclosed 9 (by omega)
  have h10 := actual_source_first_thirty_two_iterations_enclosed 10 (by omega)
  norm_num [lowerBound,upperBound,sourceTable] at h9 h10
  have hp : 0<Real.cos^[10] 1-Real.cos^[9] 1 := by
    norm_num
    linarith [h9.2,h10.1]
  rw [abs_of_pos hp]
  norm_num
  constructor <;> linarith [h9.1,h9.2,h10.1,h10.2]

theorem actual_posteriori_and_true_tenth_error_roundings :
    |posterioriTen-(68/1000:ℝ)|<1/2000 ∧
      |(|Real.cos^[10] 1-(sourceFixedPoint:ℝ)|)-(52/10000:ℝ)|<1/20000 ∧
      |Real.sin 1/(1-Real.sin 1)-(531/100:ℝ)|<1/200 ∧
      |(|Real.cos^[10] 1-Real.cos^[9] 1|)-(12833/1000000:ℝ)|<1/2000000 := by
  have hp := actual_posteriori_factor_rational_enclosure
  have hs := actual_ninth_to_tenth_step_certified_enclosure
  have h10 := actual_source_first_thirty_two_iterations_enclosed 10 (by omega)
  have hf := actual_fixed_point_certified_enclosure
  norm_num [lowerBound,upperBound,sourceTable] at h10
  have ht : 0<Real.cos^[10] 1-(sourceFixedPoint:ℝ) := by
    norm_num
    linarith [h10.1,hf.2]
  have hpm : (530799350/100000000:ℝ)*(1283331230/100000000000)<posterioriTen :=
    mul_lt_mul hp.1 hs.1.le (by norm_num) (by linarith [hp.1])
  have hpu : posterioriTen<(530799353/100000000:ℝ)*(1283331260/100000000000) :=
    mul_lt_mul hp.2 hs.2.le (by linarith [hs.1]) (by norm_num)
  norm_num at hpm hpu
  constructor
  · rw [abs_lt];constructor <;> linarith [hpm,hpu]
  constructor
  · rw [abs_of_pos ht,abs_lt]
    norm_num
    constructor <;> linarith [h10.1,h10.2,hf.1,hf.2]
  constructor
  · rw [abs_lt];constructor <;> linarith [hp.1,hp.2]
  · rw [abs_lt];constructor <;> linarith [hs.1,hs.2]

theorem actual_true_error_le_tenth_posteriori_certificate :
    |Real.cos^[10] 1-(sourceFixedPoint:ℝ)|≤posterioriTen :=
  actual_real_aposteriori_previous_step_bound 9

end SafeLearning.CompleteFoundationsCosineErrorBounds
