import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedDiscountedHorizons

def discount : ℝ := 19/20
def discreteReturn (reward : ℕ → ℝ) : ℝ := ∑'n,discount^n*reward n
def timeConstant : ℝ := (1/10)/Real.log (20/19)

theorem actual_every_bounded_path_has_a_summable_return_and_bound_forty
    (reward : ℕ → ℝ) (hr : ∀n, |reward n|≤2) :
    Summable (fun n=>discount^n*reward n) ∧ |discreteReturn reward|≤40 := by
  have hg : HasSum (fun n : ℕ => discount^n*2) ((1-discount)⁻¹*2) :=
    (hasSum_geometric_of_lt_one (by norm_num [discount] : 0≤discount)
    (by norm_num [discount] : discount<1)).mul_right (2:ℝ)
  have hm (n : ℕ) : ‖discount^n*reward n‖≤discount^n*2 := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (by norm_num [discount]) n)]
    exact mul_le_mul_of_nonneg_left (hr n) (pow_nonneg (by norm_num [discount]) n)
  have hs : Summable (fun n : ℕ => discount^n*reward n) :=
    hg.summable.of_norm_bounded hm
  refine ⟨hs,?_⟩
  have hb := norm_tsum_le_tsum_norm hs.norm
  have hn := hs.norm
  have hc := hn.tsum_le_tsum hm hg.summable
  have hv : (1-discount)⁻¹*2=(40:ℝ) := by norm_num [discount]
  rw [hg.tsum_eq,hv] at hc
  exact (show |discreteReturn reward|≤∑'n,‖discount^n*reward n‖ from hb).trans hc

theorem actual_discount_powers_eighty_nine_and_ninety_have_rigorous_rounding :
    (1/100:ℝ)<discount^89 ∧ discount^90<1/100 ∧
      |discount^89-104/10000|<1/20000 ∧ |discount^90-99/10000|<1/20000 := by
  norm_num [discount]

theorem actual_first_integer_one_percent_horizon_is_ninety (T : ℕ) :
    discount^T≤1/100 ↔ 90≤T := by
  constructor
  · intro h
    by_contra hn
    have ht : T≤89 := by omega
    have hm := pow_le_pow_of_le_one (by norm_num [discount] : 0≤discount)
      (by norm_num [discount] : discount≤1) ht
    exact not_le_of_gt actual_discount_powers_eighty_nine_and_ninety_have_rigorous_rounding.1
      (hm.trans h)
  · intro h
    exact (pow_le_pow_of_le_one (by norm_num [discount] : 0≤discount)
      (by norm_num [discount] : discount≤1) h).trans
      actual_discount_powers_eighty_nine_and_ninety_have_rigorous_rounding.2.1.le

theorem actual_discount_log_enclosure_and_log_hundred_enclosure :
    (5129329438/100000000000:ℝ)<Real.log (20/19) ∧
      Real.log (20/19)<5129329441/100000000000 ∧
      (4605170185/1000000000:ℝ)<Real.log 100 ∧
      Real.log 100<4605170188/1000000000 := by
  have hl := Real.sum_range_le_log_div (by norm_num : (0:ℝ)≤1/39)
    (by norm_num : (1/39:ℝ)<1) 3
  have hu := Real.log_div_le_sum_range_add (by norm_num : (0:ℝ)≤1/39)
    (by norm_num : (1/39:ℝ)<1) 3
  norm_num [Finset.sum_range_succ] at hl hu
  have he : Real.log (100:ℝ)=2*(Real.log 2+Real.log 5) := by
    rw [show (100:ℝ)=(2*5)^2 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  refine ⟨by linarith,by linarith,?_,?_⟩
  · rw [he]
    linarith [Real.log_two_gt_d9,Real.log_five_gt_d9]
  · rw [he]
    linarith [Real.log_two_lt_d9,Real.log_five_lt_d9]

theorem actual_logarithmic_horizon_is_the_exact_real_threshold (T : ℕ) :
    discount^T≤1/100 ↔ Real.log 100/Real.log (20/19)≤(T:ℝ) := by
  have hd : 0<Real.log (20/19:ℝ) := Real.log_pos (by norm_num)
  have hi : Real.log discount= -Real.log (20/19) := by
    rw [discount,show (19/20:ℝ)=(20/19)⁻¹ by norm_num,Real.log_inv]
  have ht : Real.log (1/100:ℝ)= -Real.log 100 := by
    rw [show (1/100:ℝ)=(100:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [←Real.log_le_log_iff (pow_pos (by norm_num [discount]) T) (by norm_num),
    Real.log_pow,hi,ht,div_le_iff₀ hd]
  constructor <;> intro h <;> linarith

theorem actual_real_horizon_and_time_constant_have_the_source_roundings :
    |Real.log 100/Real.log (20/19)-898/10|<1/20 ∧
      0<timeConstant ∧ |timeConstant-195/100|<1/200 ∧
      |10*timeConstant-195/10|<1/20 ∧
      (1/(1-discount):ℝ)=20 ∧ 10*timeConstant<20 := by
  obtain ⟨hl,hu,h100l,h100u⟩ := actual_discount_log_enclosure_and_log_hundred_enclosure
  have hd : 0<Real.log (20/19:ℝ) := by linarith
  refine ⟨?_,by unfold timeConstant;positivity,?_,?_,by norm_num [discount],?_⟩
  · rw [abs_lt]
    constructor
    · have h := (lt_div_iff₀ hd).mpr (show (898/10-1/20)*Real.log (20/19)<Real.log 100 by linarith)
      linarith
    · have h := (div_lt_iff₀ hd).mpr (show Real.log 100<(898/10+1/20)*Real.log (20/19) by linarith)
      linarith
  · unfold timeConstant
    rw [abs_lt]
    constructor
    · have h := (lt_div_iff₀ hd).mpr (show (195/100-1/200)*Real.log (20/19)<1/10 by linarith)
      linarith
    · have h := (div_lt_iff₀ hd).mpr (show (1/10:ℝ)<(195/100+1/200)*Real.log (20/19) by linarith)
      linarith
  · unfold timeConstant
    rw [abs_lt]
    constructor
    · have h := (lt_div_iff₀ hd).mpr (show (195/10-1/20)*Real.log (20/19)<1 by linarith)
      have he : 10*((1/10)/Real.log (20/19))=1/Real.log (20/19) := by ring
      rw [he]
      linarith
    · have h := (div_lt_iff₀ hd).mpr (show (1:ℝ)<(195/10+1/20)*Real.log (20/19) by linarith)
      have he : 10*((1/10)/Real.log (20/19))=1/Real.log (20/19) := by ring
      rw [he]
      linarith
  · unfold timeConstant
    have h := (div_lt_iff₀ hd).mpr (show (1:ℝ)<20*Real.log (20/19) by linarith)
    have he : 10*((1/10)/Real.log (20/19))=1/Real.log (20/19) := by ring
    rw [he]
    exact h

theorem actual_continuous_time_weight_matches_every_sampled_step (n : ℕ) :
    Real.exp (-((n:ℝ)/10)/timeConstant)=discount^n := by
  have hd : Real.log (20/19:ℝ)≠0 := ne_of_gt (Real.log_pos (by norm_num))
  have hi : Real.log (20/19:ℝ)= -Real.log discount := by
    rw [discount,show (20/19:ℝ)=(19/20)⁻¹ by norm_num,Real.log_inv]
  have he : -((n:ℝ)/10)/timeConstant=(n:ℝ)*Real.log discount := by
    unfold timeConstant
    rw [hi]
    field_simp
  rw [he,Real.exp_nat_mul,Real.exp_log (by norm_num [discount])]

theorem actual_every_path_return_after_ninety_has_the_true_tail_bound
    (reward : ℕ → ℝ) (hr : ∀n, |reward n|≤2) :
    Summable (fun n=>discount^(n+90)*reward (n+90)) ∧
      |∑'n,discount^(n+90)*reward (n+90)|≤40*discount^90 ∧
      40*discount^90<2/5 ∧ |40*discount^90-40/100|<1/200 := by
  have ht := actual_every_bounded_path_has_a_summable_return_and_bound_forty
    (fun n=>reward (n+90)) (fun n=>hr (n+90))
  have he : (fun n=>discount^(n+90)*reward (n+90))=
      (fun n=>discount^90*(discount^n*reward (n+90))) := by
    funext n
    rw [pow_add]
    ring
  rw [he]
  refine ⟨ht.1.mul_left _,?_,?_,?_⟩
  · rw [tsum_mul_left,abs_mul,
      abs_of_nonneg (pow_nonneg (by norm_num [discount] : (0:ℝ)≤discount) 90)]
    have hb := mul_le_mul_of_nonneg_left ht.2
      (pow_nonneg (by norm_num [discount] : (0:ℝ)≤discount) 90)
    unfold discreteReturn at hb
    nlinarith
  · have hh := actual_discount_powers_eighty_nine_and_ninety_have_rigorous_rounding.2.1
    nlinarith
  · norm_num [discount]

end SafeLearning.CompleteAppliedDiscountedHorizons
