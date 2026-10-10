import SafeLearning.CompleteFoundationsCosineContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsCosineNumerics

def cosPoly (x : ℝ) : ℝ :=
  1-x^2/2+x^4/24-x^6/720+x^8/40320-x^10/3628800+x^12/479001600

def sinPoly (x : ℝ) : ℝ :=
  x-x^3/6+x^5/120-x^7/5040+x^9/362880-x^11/39916800+x^13/6227020800

theorem actual_complex_cosine_degree_twelve_remainder (x : ℂ) (hx : ‖x‖≤1) :
    ‖Complex.cos x-(1-x^2/2+x^4/24-x^6/720+x^8/40320-x^10/3628800+x^12/479001600)‖≤
      ‖x‖^14*(15/(1220496076800:ℝ)) := by
  calc
    _ = ‖(Complex.exp (-x*Complex.I)-∑ m∈Finset.range 14,(-x*Complex.I)^m/m.factorial)/2+
        (Complex.exp (x*Complex.I)-∑ m∈Finset.range 14,(x*Complex.I)^m/m.factorial)/2‖ := by
          simp [Complex.cos,field,Finset.sum_range_succ,Nat.factorial]
          grind [Complex.I_sq,two_ne_zero]
    _ ≤ ‖Complex.exp (-x*Complex.I)-∑ m∈Finset.range 14,(-x*Complex.I)^m/m.factorial‖/2+
        ‖Complex.exp (x*Complex.I)-∑ m∈Finset.range 14,(x*Complex.I)^m/m.factorial‖/2 := by
          grw [norm_add_le]
          simp
    _ ≤ ‖-x*Complex.I‖^14*(Nat.succ 14*(Nat.factorial 14*(14:ℕ):ℝ)⁻¹)/2+
        ‖x*Complex.I‖^14*(Nat.succ 14*(Nat.factorial 14*(14:ℕ):ℝ)⁻¹)/2 := by
          grw [Complex.exp_bound (by simpa using hx) (by simp),
            Complex.exp_bound (by simpa using hx) (by simp)]
    _ ≤ ‖x‖^14*(15/(1220496076800:ℝ)) := by norm_num

theorem actual_real_cosine_degree_twelve_remainder (x : ℝ) (hx : |x|≤1) :
    |Real.cos x-cosPoly x|≤|x|^14*(15/(1220496076800:ℝ)) := by
  have h := actual_complex_cosine_degree_twelve_remainder (x:ℂ)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx)
  norm_cast at h

theorem actual_real_cosine_uniform_rational_error (x : ℝ) (hx : |x|≤1) :
    |Real.cos x-cosPoly x|≤1/80000000000 := by
  have h := actual_real_cosine_degree_twelve_remainder x hx
  have hp : |x|^14≤1 := by simpa using pow_le_pow_left₀ (abs_nonneg x) hx 14
  calc
    _≤|x|^14*(15/(1220496076800:ℝ)) := h
    _≤1*(15/(1220496076800:ℝ)) := mul_le_mul_of_nonneg_right hp (by norm_num)
    _≤1/80000000000 := by norm_num

theorem actual_complex_sine_degree_thirteen_remainder (x : ℂ) (hx : ‖x‖≤1) :
    ‖Complex.sin x-(x-x^3/6+x^5/120-x^7/5040+x^9/362880-x^11/39916800+x^13/6227020800)‖≤
      ‖x‖^14*(15/(1220496076800:ℝ)) := by
  calc
    _ = ‖((Complex.exp (-x*Complex.I)-∑ m∈Finset.range 14,(-x*Complex.I)^m/m.factorial)/2-
        (Complex.exp (x*Complex.I)-∑ m∈Finset.range 14,(x*Complex.I)^m/m.factorial)/2)*Complex.I‖ := by
          apply congrArg norm
          simp [Complex.sin,field,Finset.sum_range_succ,Nat.factorial]
          grind [Complex.I_sq,two_ne_zero]
    _ ≤ ‖Complex.exp (-x*Complex.I)-∑ m∈Finset.range 14,(-x*Complex.I)^m/m.factorial‖/2+
        ‖Complex.exp (x*Complex.I)-∑ m∈Finset.range 14,(x*Complex.I)^m/m.factorial‖/2 := by
          rw [norm_mul,Complex.norm_I,mul_one]
          grw [norm_sub_le]
          simp
    _ ≤ ‖-x*Complex.I‖^14*(Nat.succ 14*(Nat.factorial 14*(14:ℕ):ℝ)⁻¹)/2+
        ‖x*Complex.I‖^14*(Nat.succ 14*(Nat.factorial 14*(14:ℕ):ℝ)⁻¹)/2 := by
          grw [Complex.exp_bound (by simpa using hx) (by simp),
            Complex.exp_bound (by simpa using hx) (by simp)]
    _ ≤ ‖x‖^14*(15/(1220496076800:ℝ)) := by norm_num

theorem actual_real_sine_degree_thirteen_remainder (x : ℝ) (hx : |x|≤1) :
    |Real.sin x-sinPoly x|≤|x|^14*(15/(1220496076800:ℝ)) := by
  have h := actual_complex_sine_degree_thirteen_remainder (x:ℂ)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx)
  norm_cast at h

theorem actual_sine_one_and_cosine_one_certified_enclosures :
    (8414709847/10000000000:ℝ)<Real.sin 1 ∧ Real.sin 1<8414709849/10000000000 ∧
    (5403023058/10000000000:ℝ)<Real.cos 1 ∧ Real.cos 1<5403023059/10000000000 := by
  have hs := actual_real_sine_degree_thirteen_remainder 1 (by norm_num)
  have hc := actual_real_cosine_degree_twelve_remainder 1 (by norm_num)
  norm_num [sinPoly,cosPoly] at hs hc
  constructor
  · linarith [(abs_le.mp hs).1]
  constructor
  · linarith [(abs_le.mp hs).2]
  constructor <;> linarith [(abs_le.mp hc).1,(abs_le.mp hc).2]

end SafeLearning.CompleteFoundationsCosineNumerics
