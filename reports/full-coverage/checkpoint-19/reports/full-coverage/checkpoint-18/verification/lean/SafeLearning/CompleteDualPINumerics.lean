import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SafeLearning.CompleteDualPINumerics
open scoped BigOperators

theorem complex_cos_fourth_order_remainder (x : ℂ) (hx : ‖x‖≤1) :
    ‖Complex.cos x-(1-x^2/2+x^4/24)‖≤‖x‖^6*(7/4320) := by
  calc
    ‖Complex.cos x-(1-x^2/2+x^4/24)‖ =
      ‖(Complex.exp (-x*Complex.I)-∑ m∈Finset.range 6,(-x*Complex.I)^m/m.factorial)/2+
        (Complex.exp (x*Complex.I)-∑ m∈Finset.range 6,(x*Complex.I)^m/m.factorial)/2‖ := by
          simp [Complex.cos,field,Finset.sum_range_succ,Nat.factorial]
          grind [Complex.I_sq,two_ne_zero]
    _ ≤ ‖Complex.exp (-x*Complex.I)-∑ m∈Finset.range 6,(-x*Complex.I)^m/m.factorial‖/2+
        ‖Complex.exp (x*Complex.I)-∑ m∈Finset.range 6,(x*Complex.I)^m/m.factorial‖/2 := by
          grw [norm_add_le]
          simp
    _ ≤ ‖-x*Complex.I‖^6*(Nat.succ 6*(Nat.factorial 6*(6:ℕ):ℝ)⁻¹)/2+
        ‖x*Complex.I‖^6*(Nat.succ 6*(Nat.factorial 6*(6:ℕ):ℝ)⁻¹)/2 := by
          grw [Complex.exp_bound (by simpa using hx) (by simp),
            Complex.exp_bound (by simpa using hx) (by simp)]
    _ ≤ ‖x‖^6*(7/4320) := by norm_num

theorem real_cos_fourth_order_remainder (x : ℝ) (hx : |x|≤1) :
    |Real.cos x-(1-x^2/2+x^4/24)|≤|x|^6*(7/4320) := by
  have h := complex_cos_fourth_order_remainder (x:ℂ)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx)
  norm_cast at h

theorem actual_source_angle_cosine_brackets :
    (98/100:ℝ)<Real.cos (20025/100000) ∧
      Real.cos (20035/100000)<98/100 := by
  have h1 := real_cos_fourth_order_remainder (20025/100000) (by norm_num)
  have h2 := real_cos_fourth_order_remainder (20035/100000) (by norm_num)
  norm_num at h1 h2
  constructor <;> linarith [(abs_le.mp h1).1,(abs_le.mp h2).2]

theorem actual_source_angle_rounds_to_2003 :
    |Real.arccos (98/100:ℝ)-2003/10000|<1/20000 := by
  obtain ⟨h1,h2⟩ := actual_source_angle_cosine_brackets
  have hl := Real.arccos_lt_arccos (by norm_num : (-1:ℝ)≤98/100) h1
    (Real.cos_le_one (20025/100000))
  have hu := Real.arccos_lt_arccos (Real.neg_one_le_cos (20035/100000)) h2
    (by norm_num : (98/100:ℝ)≤1)
  rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at hl hu
  rw [abs_lt]
  constructor <;> linarith

theorem actual_source_period_rounds_to_31 :
    |2*Real.pi/Real.arccos (98/100:ℝ)-31|<1/2 := by
  have ha := abs_lt.mp actual_source_angle_rounds_to_2003
  have hp : 0<Real.arccos (98/100:ℝ) := Real.arccos_pos.mpr (by norm_num)
  rw [abs_lt]
  constructor
  · have hl : (61/2:ℝ)*Real.arccos (98/100)<2*Real.pi := by
      linarith [Real.pi_gt_d2]
    have h := (lt_div_iff₀ hp).mpr hl
    linarith
  · have hu : 2*Real.pi<(63/2:ℝ)*Real.arccos (98/100) := by
      linarith [Real.pi_lt_d2]
    have h := (div_lt_iff₀ hp).mpr hu
    linarith

theorem actual_half_envelope_logarithmic_identity :
    Real.log (1/Real.sqrt (4/5:ℝ))=Real.log (5/4:ℝ)/2 ∧
      Real.log (5/4:ℝ)=Real.log 5-2*Real.log 2 := by
  constructor
  · rw [one_div,Real.log_inv,Real.log_sqrt (by norm_num)]
    rw [Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num)]
    ring
  · rw [Real.log_div (by norm_num) (by norm_num),
      show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num

theorem actual_source_half_envelope_rounds_to_62 :
    |Real.log 2/Real.log (1/Real.sqrt (4/5:ℝ))-62/10|<1/20 := by
  obtain ⟨hid,hlog⟩ := actual_half_envelope_logarithmic_identity
  rw [hid,hlog]
  have hd : 0<(Real.log 5-2*Real.log 2)/2 := by
    linarith [Real.log_five_gt_d9,Real.log_two_lt_d9]
  rw [abs_lt]
  constructor
  · have h : (123/20:ℝ)*((Real.log 5-2*Real.log 2)/2)<Real.log 2 := by
      linarith [Real.log_five_lt_d9,Real.log_two_gt_d9]
    have hh := (lt_div_iff₀ hd).mpr h
    linarith
  · have h : Real.log 2<(125/20:ℝ)*((Real.log 5-2*Real.log 2)/2) := by
      linarith [Real.log_five_gt_d9,Real.log_two_lt_d9]
    have hh := (div_lt_iff₀ hd).mpr h
    linarith

end SafeLearning.CompleteDualPINumerics
