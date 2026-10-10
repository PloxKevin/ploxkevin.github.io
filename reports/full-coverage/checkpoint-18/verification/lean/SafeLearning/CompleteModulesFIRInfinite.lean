import SafeLearning.CompleteModulesFIROperator

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesFIRInfinite
open CompleteModulesFIRBase CompleteModulesFIROperator

/-- The finite dissipation inequality passes to the genuine infinite energy sums. -/
theorem actual_fir_square_summable_input_has_bounded_square_summable_output
    (gain storage currentGain delayedGain : ℝ) (hstorage : 0 ≤ storage)
    (hcertificate : (actualFIRDissipationMatrix gain storage-
      (actualFIRKernelRow currentGain delayedGain)ᵀ*actualFIRKernelRow currentGain delayedGain).PosSemidef)
    (input : ℕ → ℝ) (hinput : Summable (fun time => (input time)^2)) :
    Summable (fun time => (actualFIRResponse currentGain delayedGain input time)^2) ∧
    (∑' time,(actualFIRResponse currentGain delayedGain input time)^2) ≤
      gain^2*(∑' time,(input time)^2) := by
  have hbound : ∀ horizon,
      (∑ time ∈ Finset.range horizon,(actualFIRResponse currentGain delayedGain input time)^2) ≤
        gain^2*(∑' time,(input time)^2) := by
    intro horizon
    exact (actual_zero_initial_fir_output_energy_bound gain storage currentGain delayedGain hstorage hcertificate input horizon).trans
      (mul_le_mul_of_nonneg_left (hinput.sum_le_tsum (Finset.range horizon) (fun time htime => sq_nonneg (input time))) (sq_nonneg gain))
  exact ⟨summable_of_sum_range_le (fun time => sq_nonneg _) hbound,
    Real.tsum_le_of_sum_range_le (fun time => sq_nonneg _) hbound⟩

end SafeLearning.CompleteModulesFIRInfinite
