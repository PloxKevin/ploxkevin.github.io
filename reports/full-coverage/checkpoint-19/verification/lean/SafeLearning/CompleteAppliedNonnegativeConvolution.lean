import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedNonnegativeConvolution

def causalOutput (h u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), h k*u (n-k)

def dcGain (h : ℕ → ℝ) : ℝ := ∑' k, h k

def delayedSquare (u : ℕ → ℝ) (k n : ℕ) : ℝ :=
  if k ≤ n then (u (n-k))^2 else 0

theorem actual_delayed_square_preserves_the_full_input_energy
    (u : ℕ → ℝ) (hu : Summable (fun n => (u n)^2)) (k : ℕ) :
    HasSum (delayedSquare u k) (∑' n, (u n)^2) := by
  have hz : (∑ n ∈ Finset.range k, delayedSquare u k n)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [delayedSquare,show ¬k ≤ n by have ht:=Finset.mem_range.mp hn; omega]
  have ht : HasSum (fun n=>delayedSquare u k (n+k)) (∑' n, (u n)^2) := by
    simpa [delayedSquare] using hu.hasSum
  simpa only [hz,add_zero] using
    (hasSum_nat_add_iff (f:=delayedSquare u k) (g:=∑' n, (u n)^2) k).mp ht

theorem actual_output_square_has_the_weighted_Cauchy_bound
    (h u : ℕ → ℝ) (hh : ∀ k, 0 ≤ h k) (hs : Summable h) (n : ℕ) :
    (causalOutput h u n)^2 ≤ dcGain h*
      (∑ k ∈ Finset.range (n+1), h k*(u (n-k))^2) := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range (n+1))
    (r:=fun k=>h k*u (n-k)) (f:=h) (g:=fun k=>h k*(u (n-k))^2)
    (fun k _=>hh k) (fun k _=>mul_nonneg (hh k) (sq_nonneg _))
    (fun k _=>by nlinarith)
  have hp := hs.sum_le_tsum (Finset.range (n+1)) (fun k _=>hh k)
  have hw : 0 ≤ ∑ k ∈ Finset.range (n+1), h k*(u (n-k))^2 :=
    Finset.sum_nonneg (fun k _=>mul_nonneg (hh k) (sq_nonneg _))
  exact hc.trans (mul_le_mul_of_nonneg_right hp hw)

theorem actual_finite_horizon_output_energy_is_bounded_by_DC_squared
    (h u : ℕ → ℝ) (hh : ∀ k, 0 ≤ h k) (hs : Summable h)
    (hu : Summable (fun n => (u n)^2)) (N : ℕ) :
    (∑ n ∈ Finset.range N, (causalOutput h u n)^2) ≤
      (dcGain h)^2*(∑' n, (u n)^2) := by
  have hH : 0 ≤ dcGain h := tsum_nonneg hh
  have hE : 0 ≤ ∑' n, (u n)^2 := tsum_nonneg (fun n=>sq_nonneg _)
  have hpad (n : ℕ) (hn : n<N) :
      (∑ k ∈ Finset.range (n+1), h k*(u (n-k))^2)=
        ∑ k ∈ Finset.range N, h k*delayedSquare u k n := by
    rw [←Finset.sum_subset (Finset.range_mono (by omega : n+1≤N))]
    · apply Finset.sum_congr rfl
      intro k hk
      simp [delayedSquare,show k≤n by have ht:=Finset.mem_range.mp hk; omega]
    · intro k _ hk
      have hk' : ¬k≤n := by simp only [Finset.mem_range] at hk; omega
      simp [delayedSquare,hk']
  have hc : (∑ n ∈ Finset.range N, (causalOutput h u n)^2) ≤
      dcGain h*(∑ n ∈ Finset.range N,
        ∑ k ∈ Finset.range N, h k*delayedSquare u k n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [hpad n (Finset.mem_range.mp hn)] using
      actual_output_square_has_the_weighted_Cauchy_bound h u hh hs n
  have hinner : (∑ n ∈ Finset.range N,
      ∑ k ∈ Finset.range N, h k*delayedSquare u k n) ≤
        dcGain h*(∑' n, (u n)^2) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ k ∈ Finset.range N, h k*(∑ n ∈ Finset.range N, delayedSquare u k n) := by
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range N, h k*(∑' n, (u n)^2) := by
        apply Finset.sum_le_sum
        intro k _
        have hv := actual_delayed_square_preserves_the_full_input_energy u hu k
        have hb := hv.summable.sum_le_tsum (Finset.range N)
          (fun n _=>by unfold delayedSquare; split_ifs <;> positivity)
        rw [hv.tsum_eq] at hb
        exact mul_le_mul_of_nonneg_left hb (hh k)
      _ = (∑ k ∈ Finset.range N, h k)*(∑' n, (u n)^2) := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (hs.sum_le_tsum (Finset.range N) (fun k _=>hh k)) hE
  have hm := mul_le_mul_of_nonneg_left hinner hH
  nlinarith

theorem actual_every_square_summable_input_has_a_square_summable_output
    (h u : ℕ → ℝ) (hh : ∀ k, 0 ≤ h k) (hs : Summable h)
    (hu : Summable (fun n => (u n)^2)) :
    Summable (fun n => (causalOutput h u n)^2) ∧
      (∑' n, (causalOutput h u n)^2) ≤ (dcGain h)^2*(∑' n, (u n)^2) := by
  have hb := actual_finite_horizon_output_energy_is_bounded_by_DC_squared h u hh hs hu
  exact ⟨summable_of_sum_range_le (fun n=>sq_nonneg _) hb,
    Real.tsum_le_of_sum_range_le (fun n=>sq_nonneg _) hb⟩

theorem actual_every_unit_bounded_input_has_peak_output_bounded_by_DC
    (h u : ℕ → ℝ) (hh : ∀ k, 0 ≤ h k) (hs : Summable h)
    (hu : ∀ n, |u n|≤1) (n : ℕ) : |causalOutput h u n| ≤ dcGain h := by
  unfold causalOutput
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), |h k*u (n-k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n+1), h k := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul,abs_of_nonneg (hh k)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hu (n-k)) (hh k)
    _ ≤ _ := hs.sum_le_tsum (Finset.range (n+1)) (fun k _=>hh k)

theorem actual_constant_unit_input_output_tends_to_DC
    (h : ℕ → ℝ) (hs : Summable h) :
    Tendsto (causalOutput h (fun _=>1)) atTop (𝓝 (dcGain h)) := by
  have ht := (tendsto_add_atTop_iff_nat 1).mpr hs.hasSum.tendsto_sum_nat
  change Tendsto (fun n=>∑ k ∈ Finset.range (n+1), h k*1) atTop (𝓝 (∑'k,h k))
  simpa only [mul_one] using ht

def peakGains (h : ℕ → ℝ) : Set ℝ :=
  {g | 0≤g ∧ ∀ u : ℕ → ℝ, (∀ n, |u n|≤1) → ∀ n, |causalOutput h u n|≤g}

def energyGains (h : ℕ → ℝ) : Set ℝ :=
  {g | 0≤g ∧ ∀ u : ℕ → ℝ, Summable (fun n=>(u n)^2) →
    Summable (fun n=>(causalOutput h u n)^2) ∧
      (∑' n, (causalOutput h u n)^2) ≤ g^2*(∑' n, (u n)^2)}

theorem actual_nonnegative_summable_impulse_response_has_least_peak_gain_DC
    (h : ℕ → ℝ) (hh : ∀ k, 0≤h k) (hs : Summable h) :
    IsLeast (peakGains h) (dcGain h) := by
  refine ⟨⟨tsum_nonneg hh,fun u hu n=>
    actual_every_unit_bounded_input_has_peak_output_bounded_by_DC h u hh hs hu n⟩,?_⟩
  intro g hg
  have ht := actual_constant_unit_input_output_tends_to_DC h hs
  have hb (n : ℕ) : causalOutput h (fun _=>1) n≤g :=
    (le_abs_self _).trans (hg.2 (fun _=>1) (fun _=>by norm_num) n)
  exact le_of_tendsto ht (Eventually.of_forall hb)

end SafeLearning.CompleteAppliedNonnegativeConvolution
