import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteAppliedUniformMGFSeries

theorem actual_six_power_factorial_is_bounded_by_the_odd_factorial (n : ℕ) :
    6^n*Nat.factorial n≤Nat.factorial (2*n+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hf : 6*(n+1)≤(2*n+3)*(2*n+2) := by nlinarith
    calc
      6^(n+1)*Nat.factorial (n+1)=6*(n+1)*(6^n*Nat.factorial n) := by
        rw [pow_succ,Nat.factorial_succ];ring
      _≤6*(n+1)*Nat.factorial (2*n+1) := Nat.mul_le_mul_left _ ih
      _≤((2*n+3)*(2*n+2))*Nat.factorial (2*n+1) := Nat.mul_le_mul_right _ hf
      _=Nat.factorial (2*(n+1)+1) := by
        have hfac : Nat.factorial ((2*n+1)+1+1)=
            ((2*n+1)+1+1)*(((2*n+1)+1)*Nat.factorial (2*n+1)) := by
          rw [Nat.factorial_succ, Nat.factorial_succ]
        rw [show 2*(n+1)+1=(2*n+1)+1+1 by omega, hfac]
        ring

def normalizedSinh (t : ℝ) : ℝ := if t=0 then 1 else Real.sinh t/t

theorem actual_normalized_hyperbolic_sine_has_the_true_even_moment_series
    (t : ℝ) (ht : t≠0) :
    HasSum (fun n : ℕ => t^(2*n)/(Nat.factorial (2*n+1):ℝ)) (normalizedSinh t) := by
  have h := (Real.hasSum_sinh t).div_const t
  have he (n : ℕ) : (t^(2*n+1)/(Nat.factorial (2*n+1):ℝ))/t=
      t^(2*n)/(Nat.factorial (2*n+1):ℝ) := by
    rw [pow_succ]
    field_simp
  simpa only [he,normalizedSinh,ite_eq_right ht] using h

theorem actual_uniform_moment_series_is_bounded_by_the_variance_proxy_exponential (t : ℝ) :
    normalizedSinh t≤Real.exp (t^2/6) := by
  by_cases ht : t=0
  · simp [normalizedSinh,ht]
  · have hs := actual_normalized_hyperbolic_sine_has_the_true_even_moment_series t ht
    have hex : HasSum (fun n : ℕ => (t^2/6)^n/(Nat.factorial n:ℝ)) (Real.exp (t^2/6)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (t^2/6)
    rw [←hs.tsum_eq,←hex.tsum_eq]
    apply hs.summable.tsum_le_tsum _ hex.summable
    intro n
    have hf : (6:ℝ)^n*(Nat.factorial n:ℝ)≤(Nat.factorial (2*n+1):ℝ) := by
      exact_mod_cast actual_six_power_factorial_is_bounded_by_the_odd_factorial n
    have hnonneg : 0≤t^(2*n) := by rw [pow_mul]; positivity
    calc
      t^(2*n)/(Nat.factorial (2*n+1):ℝ)≤t^(2*n)/((6:ℝ)^n*(Nat.factorial n:ℝ)) :=
        div_le_div_of_nonneg_left hnonneg (by positivity) hf
      _=(t^2/6)^n/(Nat.factorial n:ℝ) := by
        rw [div_pow,←pow_mul]
        field_simp

end SafeLearning.CompleteAppliedUniformMGFSeries
