import SafeLearning.CompleteModulesScalarTrajectory

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesScalarExactGain
open CompleteModulesScalarTrajectory

def actualFinitePulse (horizon time : ℕ) : ℝ := if time < horizon then 1 else 0

theorem actual_finite_pulse_squared_input_is_summable (horizon : ℕ) :
    Summable (fun time => (actualFinitePulse horizon time)^2) := by
  apply summable_of_ne_finset_zero (s:=Finset.range horizon)
  intro time htime
  simp only [Finset.mem_range] at htime
  simp [actualFinitePulse,htime]

theorem actual_finite_pulse_squared_input_energy (horizon : ℕ) :
    (∑' time,(actualFinitePulse horizon time)^2)=(horizon:ℝ) := by
  rw [tsum_eq_sum (s:=Finset.range horizon)]
  · calc
      (∑ time ∈ Finset.range horizon,(actualFinitePulse horizon time)^2)=
          (∑ time ∈ Finset.range horizon,(1:ℝ)) := by
            apply Finset.sum_congr rfl
            intro time htime
            simp [actualFinitePulse,Finset.mem_range.mp htime]
      _ = (horizon:ℝ) := by simp
  · intro time htime
    simp only [Finset.mem_range] at htime
    simp [actualFinitePulse,htime]

theorem actual_zero_state_finite_pulse_prefix_response (horizon time : ℕ) (htime : time ≤ horizon) :
    actualStableScalarState 0 (actualFinitePulse horizon) time=2*(1-(1/2:ℝ)^time) := by
  induction time generalizing horizon with
  | zero => simp [actualStableScalarState]
  | succ time ih =>
    have ht : time < horizon := Nat.lt_of_succ_le htime
    rw [actualStableScalarState,ih horizon (Nat.le_of_lt ht)]
    simp [actualFinitePulse,ht,pow_succ]
    ring

theorem actual_half_geometric_prefix_sum (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,(1/2:ℝ)^time)=2*(1-(1/2:ℝ)^horizon) := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
    rw [Finset.sum_range_succ,ih,pow_succ]
    ring

theorem actual_finite_pulse_output_prefix_energy_lower_bound (horizon : ℕ) :
    4*(horizon:ℝ)-16 ≤
      (∑ time ∈ Finset.range horizon,(actualStableScalarState 0 (actualFinitePulse horizon) time)^2) := by
  have hpoint : (∑ time ∈ Finset.range horizon,(4-8*(1/2:ℝ)^time)) ≤
      (∑ time ∈ Finset.range horizon,(actualStableScalarState 0 (actualFinitePulse horizon) time)^2) := by
    apply Finset.sum_le_sum
    intro time htime
    rw [actual_zero_state_finite_pulse_prefix_response horizon time (Nat.le_of_lt (Finset.mem_range.mp htime))]
    nlinarith [sq_nonneg ((1/2:ℝ)^time)]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,actual_half_geometric_prefix_sum] at hpoint
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hpoint
  nlinarith [pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) horizon]

theorem actual_scalar_square_summable_signal_gain_requires_at_least_two
    (gain : ℝ) (hgain : 0 ≤ gain)
    (hbound : ∀ input : ℕ → ℝ,Summable (fun time => (input time)^2) →
      (∑' time,(actualStableScalarState 0 input time)^2) ≤ gain^2*(∑' time,(input time)^2)) :
    2 ≤ gain := by
  by_contra hn
  have hgap : 0 < 4-gain^2 := by nlinarith
  obtain ⟨horizon,hhorizon⟩ := exists_nat_gt (16/(4-gain^2))
  have hstrict : 16 < (horizon:ℝ)*(4-gain^2) := (div_lt_iff₀ hgap).mp hhorizon
  have hpulse := actual_finite_pulse_squared_input_is_summable horizon
  have houtput := (actual_source_gain_two_infinite_output_energy_bound 0 (actualFinitePulse horizon) hpulse).1
  have hupper := hbound (actualFinitePulse horizon) hpulse
  rw [actual_finite_pulse_squared_input_energy] at hupper
  have hprefix := houtput.sum_le_tsum (Finset.range horizon) (fun time htime => sq_nonneg _)
  have hlower := actual_finite_pulse_output_prefix_energy_lower_bound horizon
  nlinarith

theorem actual_scalar_square_summable_energy_gain_iff_at_least_two (gain : ℝ) (hgain : 0 ≤ gain) :
    (∀ input : ℕ → ℝ,Summable (fun time => (input time)^2) →
      Summable (fun time => (actualStableScalarState 0 input time)^2) ∧
      (∑' time,(actualStableScalarState 0 input time)^2) ≤ gain^2*(∑' time,(input time)^2)) ↔ 2 ≤ gain := by
  constructor
  · intro h
    exact actual_scalar_square_summable_signal_gain_requires_at_least_two gain hgain (fun input hi => (h input hi).2)
  · intro htwo input hinput
    have h := actual_source_gain_two_infinite_output_energy_bound 0 input hinput
    refine ⟨h.1,?_⟩
    norm_num at h
    have hnonnegative : 0 ≤ (∑' time,(input time)^2) := tsum_nonneg (fun time => sq_nonneg _)
    have hsquared : (4:ℝ) ≤ gain^2 := by nlinarith
    exact h.2.trans (mul_le_mul_of_nonneg_right hsquared hnonnegative)

end SafeLearning.CompleteModulesScalarExactGain
