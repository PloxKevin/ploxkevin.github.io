import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset Filter Set
open scoped Topology
namespace SafeLearning.CompleteFoundationsFourPowerBlocks

/-- The printed one-based block indicator; zero is inactive. -/
def reward (t : ℕ) : ℕ := by
  classical
  exact if ∃ k : ℕ, 4^k ≤ t ∧ t < 2*4^k then 1 else 0
def countBefore (n : ℕ) : ℕ := ∑ t ∈ Finset.range n, reward t
def average (T : ℕ) : ℝ := (countBefore (T+1) : ℝ) / (T : ℝ)

theorem actual_zero_reward : reward 0 = 0 := by
  classical
  simp only [reward]
  rw [ite_eq_right]
  rintro ⟨k,hk,_⟩
  have hp : 0 < (4:ℕ)^k := pow_pos (by norm_num) _
  omega

theorem actual_reward_inside_one_four_power_block (k t : ℕ)
    (hlo : 4^k ≤ t) (hhi : t < 4^(k+1)) :
    reward t = if t < 2*4^k then 1 else 0 := by
  classical
  unfold reward
  congr 1
  apply propext
  constructor
  · rintro ⟨j,hjlo,hjhi⟩
    rcases lt_trichotomy j k with hj | rfl | hj
    · have hp := Nat.pow_le_pow_right (by norm_num : 0 < (4:ℕ)) (Nat.succ_le_of_lt hj)
      rw [pow_succ] at hp
      have hpos : 0 < (4:ℕ)^j := pow_pos (by norm_num) _
      omega
    · exact hjhi
    · have hp := Nat.pow_le_pow_right (by norm_num : 0 < (4:ℕ)) (Nat.succ_le_of_lt hj)
      omega
  · intro ht
    exact ⟨k,hlo,ht⟩

theorem actual_initial_segment_indicator_count (m p : ℕ) :
    (∑ i ∈ Finset.range m, if i < p then (1:ℕ) else 0) = min m p := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,ih]
    by_cases h : m < p
    · simp only [ite_eq_left h]
      omega
    · simp only [ite_eq_right h]
      omega

theorem actual_count_within_one_block (k n : ℕ)
    (hlo : 4^k ≤ n) (hhi : n ≤ 4^(k+1)) :
    countBefore n = countBefore (4^k) + min (n-4^k) (4^k) := by
  have hn : n = 4^k + (n-4^k) := by omega
  unfold countBefore
  nth_rw 1 [hn]
  rw [Finset.sum_range_add]
  congr 1
  calc
    (∑ i ∈ Finset.range (n-4^k), reward (4^k+i)) =
        ∑ i ∈ Finset.range (n-4^k), if i < 4^k then (1:ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have him : i < n-4^k := Finset.mem_range.mp hi
      rw [actual_reward_inside_one_four_power_block k (4^k+i) (by omega) (by omega)]
      have he : 4^k+i < 2*4^k ↔ i < 4^k := by omega
      simp only [he]
    _ = min (n-4^k) (4^k) := actual_initial_segment_indicator_count _ _

theorem actual_count_before_each_four_power (k : ℕ) :
    3 * countBefore (4^k) = 4^k - 1 := by
  induction k with
  | zero => simp [countBefore,actual_zero_reward]
  | succ k ih =>
    have hp : 0 < (4:ℕ)^k := pow_pos (by norm_num) _
    rw [actual_count_within_one_block k (4^(k+1))
      (Nat.pow_le_pow_right (by norm_num) (by omega)) le_rfl]
    rw [pow_succ]
    have hm : min (4^k*4-4^k) (4^k) = 4^k := by omega
    rw [hm]
    omega

theorem actual_count_formula_at_every_block (k n : ℕ)
    (hlo : 4^k ≤ n) (hhi : n ≤ 4^(k+1)) :
    3 * countBefore n = 4^k-1 + 3 * min (n-4^k) (4^k) := by
  rw [actual_count_within_one_block k n hlo hhi,Nat.mul_add,
    actual_count_before_each_four_power]

theorem actual_all_horizon_integer_count_bounds (T : ℕ) (hT : 0 < T) :
    T ≤ 3*countBefore (T+1) ∧ 3*countBefore (T+1) ≤ 2*T+1 := by
  let k := Nat.log 4 (T+1)
  have hlo : 4^k ≤ T+1 := Nat.pow_log_le_self 4 (by omega)
  have hhi : T+1 ≤ 4^(k+1) := (Nat.lt_pow_succ_log_self (by norm_num) (T+1)).le
  have hp : 0 < (4:ℕ)^k := pow_pos (by norm_num) _
  have hc := actual_count_formula_at_every_block k (T+1) hlo hhi
  rw [pow_succ] at hhi
  by_cases hm : T+1-4^k ≤ 4^k
  · rw [min_eq_left hm] at hc
    omega
  · rw [min_eq_right (by omega)] at hc
    omega

theorem actual_all_horizon_average_bounds (T : ℕ) (hT : 0 < T) :
    (1/3:ℝ) ≤ average T ∧ average T ≤ 2/3 + 1/(3*(T:ℝ)) := by
  have hden : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  have hb := actual_all_horizon_integer_count_bounds T hT
  have hlo : (T:ℝ) ≤ 3*(countBefore (T+1):ℝ) := by exact_mod_cast hb.1
  have hhi : 3*(countBefore (T+1):ℝ) ≤ 2*(T:ℝ)+1 := by exact_mod_cast hb.2
  unfold average
  constructor
  · apply (le_div_iff₀ hden).mpr
    linarith
  · apply (div_le_iff₀ hden).mpr
    field_simp
    nlinarith

theorem actual_zero_block_endpoint_count (k : ℕ) :
    3*countBefore (4^(k+1)) = 4^(k+1)-1 :=
  actual_count_before_each_four_power _

theorem actual_one_block_endpoint_count (k : ℕ) :
    3*countBefore (2*4^k) = 4^(k+1)-1 := by
  have hp : 0 < (4:ℕ)^k := pow_pos (by norm_num) _
  rw [actual_count_formula_at_every_block k (2*4^k) (by omega) (by rw [pow_succ];omega)]
  have hm : min (2*4^k-4^k) (4^k) = 4^k := by omega
  rw [hm,pow_succ]
  omega

end SafeLearning.CompleteFoundationsFourPowerBlocks
