import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesDissipation

/-- The storage difference is summed along the actual discrete trajectory. -/
theorem actual_storage_dissipation_telescopes
    (storage input output : ℕ → ℝ) (gain : ℝ)
    (hstep : ∀ time,storage (time+1)-storage time ≤ gain^2*(input time)^2-(output time)^2)
    (horizon : ℕ) :
    storage horizon+(∑ time ∈ Finset.range horizon,(output time)^2) ≤
      storage 0+gain^2*(∑ time ∈ Finset.range horizon,(input time)^2) := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
    simp only [Finset.sum_range_succ]
    have h := hstep horizon
    nlinarith

theorem actual_nonnegative_storage_implies_finite_energy_gain
    (storage input output : ℕ → ℝ) (gain : ℝ)
    (hstorage : ∀ time,0 ≤ storage time)
    (hstep : ∀ time,storage (time+1)-storage time ≤ gain^2*(input time)^2-(output time)^2)
    (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,(output time)^2) ≤
      gain^2*(∑ time ∈ Finset.range horizon,(input time)^2)+storage 0 := by
  have h := actual_storage_dissipation_telescopes storage input output gain hstep horizon
  linarith [hstorage horizon]

theorem actual_zero_initial_storage_implies_signal_norm_gain
    (storage input output : ℕ → ℝ) (gain : ℝ)
    (hstorage : ∀ time,0 ≤ storage time) (hzero : storage 0=0)
    (hstep : ∀ time,storage (time+1)-storage time ≤ gain^2*(input time)^2-(output time)^2)
    (horizon : ℕ) :
    Real.sqrt (∑ time ∈ Finset.range horizon,(output time)^2) ≤
      |gain| *Real.sqrt (∑ time ∈ Finset.range horizon,(input time)^2) := by
  have h := actual_nonnegative_storage_implies_finite_energy_gain storage input output gain hstorage hstep horizon
  rw [hzero,add_zero] at h
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (sq_nonneg gain),Real.sqrt_sq_eq_abs] at hs
  exact hs

theorem actual_storage_dissipation_with_square_summable_input_has_bounded_square_summable_output
    (storage input output : ℕ → ℝ) (gain : ℝ)
    (hstorage : ∀ time,0 ≤ storage time)
    (hstep : ∀ time,storage (time+1)-storage time ≤ gain^2*(input time)^2-(output time)^2)
    (hinput : Summable (fun time => (input time)^2)) :
    Summable (fun time => (output time)^2) ∧
    (∑' time,(output time)^2) ≤ gain^2*(∑' time,(input time)^2)+storage 0 := by
  have hbound : ∀ horizon,(∑ time ∈ Finset.range horizon,(output time)^2) ≤
      gain^2*(∑' time,(input time)^2)+storage 0 := by
    intro horizon
    apply (actual_nonnegative_storage_implies_finite_energy_gain storage input output gain hstorage hstep horizon).trans
    have h := mul_le_mul_of_nonneg_left (hinput.sum_le_tsum (Finset.range horizon) (fun time htime => sq_nonneg _)) (sq_nonneg gain)
    linarith
  exact ⟨summable_of_sum_range_le (fun time => sq_nonneg _) hbound,
    Real.tsum_le_of_sum_range_le (fun time => sq_nonneg _) hbound⟩

theorem actual_practice_energy_three_has_output_energy_at_most_twelve
    (storage input output : ℕ → ℝ)
    (hstorage : ∀ time,0 ≤ storage time) (hzero : storage 0=0)
    (hstep : ∀ time,storage (time+1)-storage time ≤ 4*(input time)^2-(output time)^2)
    (horizon : ℕ) (henergy : (∑ time ∈ Finset.range horizon,(input time)^2)=3) :
    (∑ time ∈ Finset.range horizon,(output time)^2) ≤ 12 := by
  have h := actual_nonnegative_storage_implies_finite_energy_gain storage input output 2 hstorage
    (by intro time; convert hstep time using 1 <;> norm_num) horizon
  norm_num [hzero,henergy] at h ⊢
  exact h

end SafeLearning.CompleteModulesDissipation
