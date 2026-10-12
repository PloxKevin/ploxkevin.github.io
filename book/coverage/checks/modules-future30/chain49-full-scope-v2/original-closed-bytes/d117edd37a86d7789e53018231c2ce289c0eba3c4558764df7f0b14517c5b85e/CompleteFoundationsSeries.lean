import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsSeries

theorem discounted_return_bound (r : ℕ → ℝ) (q M : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q<1) (hr : ∀ n, |r n| ≤ M) :
    Summable (fun n => q^n*r n) ∧ |∑' n, q^n*r n| ≤ M/(1-q) := by
  have hmajor : HasSum (fun n : ℕ => M*q^n) (M*(1-q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq₀ hq₁).mul_left M
  have hbound : ∀ n, ‖q^n*r n‖ ≤ M*q^n := by
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hq₀ n)]
    nlinarith [mul_le_mul_of_nonneg_left (hr n) (pow_nonneg hq₀ n)]
  have hs : Summable (fun n => q^n*r n) := hmajor.summable.of_norm_bounded hbound
  refine ⟨hs,?_⟩
  simpa [Real.norm_eq_abs,div_eq_mul_inv] using hs.hasSum.norm_le_of_bounded hmajor hbound

theorem discounted_tail_bound (r : ℕ → ℝ) (q M : ℝ) (T : ℕ)
    (hq₀ : 0 ≤ q) (hq₁ : q<1) (hr : ∀ n, |r n| ≤ M) :
    |∑' n : ℕ, q^(n+T)*r (n+T)| ≤ M*q^T/(1-q) := by
  have hh := (discounted_return_bound (fun n => q^T*r (n+T)) q (M*q^T) hq₀ hq₁ ?_).2
  · convert hh using 1
    congr 1
    apply tsum_congr
    intro n; rw [pow_add]; ring
  · intro n
    rw [abs_mul,abs_of_nonneg (pow_nonneg hq₀ T)]
    nlinarith [mul_le_mul_of_nonneg_left (hr (n+T)) (pow_nonneg hq₀ T)]

theorem constant_discounted_tail (q M : ℝ) (T : ℕ) (hq₀ : 0 ≤ q) (hq₁ : q<1) :
    (∑' n : ℕ, q^(n+T)*M)=M*q^T/(1-q) := by
  have hh := ((hasSum_geometric_of_lt_one hq₀ hq₁).mul_left (M*q^T)).tsum_eq
  convert hh using 1
  · apply tsum_congr; intro n; rw [pow_add]; ring
  · ring

theorem half_discount_minimal_budget (T : ℕ) :
    (4*(1/2 : ℝ)^T ≤ 1/100 ↔ 9 ≤ T) := by
  have hmono : Antitone (fun n : ℕ => (1/2 : ℝ)^n) := pow_right_anti₀ (by norm_num) (by norm_num)
  constructor
  · intro h; by_contra hn
    have hn' : T ≤ 8 := by omega
    have hh := hmono hn'; norm_num at hh; linarith
  · intro hn; have hh := hmono hn; norm_num at hh; linarith

theorem half_discount_numbers :
    (∑ n ∈ Finset.range 4, (1/2 : ℝ)^n*2)=15/4 ∧
    4*(1/2 : ℝ)^4=1/4 ∧ 4*(1/2 : ℝ)^8=1/64 ∧
    4*(1/2 : ℝ)^9=1/128 := by norm_num [Finset.sum_range_succ]

theorem geometric_hasSum (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q<1) :
    HasSum (fun n : ℕ => q^n) (1/(1-q)) := by
  simpa [one_div] using hasSum_geometric_of_lt_one hq₀ hq₁

theorem weighted_geometric_hasSum (q : ℝ) (hq : |q|<1) :
    HasSum (fun n : ℕ => (n : ℝ)*q^n) (q/(1-q)^2) := by
  simpa [Real.norm_eq_abs] using hasSum_coe_mul_geometric_of_norm_lt_one hq

end SafeLearning.CompleteFoundationsSeries
