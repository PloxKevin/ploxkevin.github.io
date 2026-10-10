import SafeLearning.CompleteAppliedUniformMGFSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteAppliedUniformOptimalSeries
open SafeLearning.CompleteAppliedUniformMGFSeries

theorem actual_uniform_moment_series_is_at_least_its_first_two_terms (t : ℝ) :
    1+t^2/6≤normalizedSinh t := by
  by_cases ht : t=0
  · simp [ht,normalizedSinh]
  have hs := actual_normalized_hyperbolic_sine_has_the_true_even_moment_series t ht
  have hnonneg (n : ℕ) : 0≤t^(2*n)/(Nat.factorial (2*n+1):ℝ) := by
    rw [pow_mul];positivity
  have h := sum_le_hasSum (Finset.range 2) (fun n _=>hnonneg n) hs
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  exact h

theorem actual_every_smaller_uniform_variance_proxy_has_a_true_mgf_violation
    (c : ℝ) (hc : 0≤c) (hcsmall : c<1/3) :
    ∃ t : ℝ,0<t ∧ Real.exp (c*t^2/2)<normalizedSinh t := by
  let d : ℝ:=1/3-c
  have hd : 0<d := by dsimp [d];linarith
  have hdu : d≤1/3 := by dsimp [d];linarith
  have hc2 : c^2≤1/9 := by nlinarith
  have hd2 : d^2≤1/9 := by nlinarith
  have hx : ‖c*d^2/2‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have h := mul_le_mul_of_nonneg_left hd2 hc
    nlinarith
  have he := Real.norm_exp_sub_one_sub_id_le hx
  rw [Real.norm_eq_abs,Real.norm_eq_abs,sq_abs] at he
  have heupper := (abs_le.mp he).2
  have hpow : d^4≤d^3/3 := by
    have h := mul_le_mul_of_nonneg_left hdu (by positivity : 0≤d^3)
    nlinarith only [h]
  have hrem : (c*d^2/2)^2≤d^3/108 := by
    have h := mul_le_mul_of_nonneg_right hc2 (by positivity : 0≤d^4)
    have hh := mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤1/9)
    nlinarith only [h,hh]
  have hgap : c*d^2/2+d^3/2=d^2/6 := by dsimp [d];ring
  have hd3 : 0<d^3 := by positivity
  have hupper : Real.exp (c*d^2/2)<1+d^2/6 := by
    nlinarith only [heupper,hrem,hgap,hd3]
  exact ⟨d,hd,hupper.trans_le (actual_uniform_moment_series_is_at_least_its_first_two_terms d)⟩

end SafeLearning.CompleteAppliedUniformOptimalSeries
