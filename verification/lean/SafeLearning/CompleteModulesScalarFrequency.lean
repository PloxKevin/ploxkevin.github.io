import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SafeLearning.CompleteModulesScalarFrequency

def actualStableScalarFrequencyResponse (frequency : ℝ) : ℂ :=
  1/(Complex.exp (Complex.I*(frequency:ℂ))-(1/2:ℂ))

theorem actual_stable_scalar_frequency_denominator_norm_at_least_one_half (frequency : ℝ) :
    (1/2:ℝ) ≤ ‖Complex.exp (Complex.I*(frequency:ℂ))-(1/2:ℂ)‖ := by
  have h := norm_sub_norm_le (Complex.exp (Complex.I*(frequency:ℂ))) (1/2:ℂ)
  rw [Complex.norm_exp_I_mul_ofReal] at h
  norm_num at h ⊢
  exact h

theorem actual_stable_scalar_frequency_gain_at_most_two (frequency : ℝ) :
    ‖actualStableScalarFrequencyResponse frequency‖ ≤ 2 := by
  have h := actual_stable_scalar_frequency_denominator_norm_at_least_one_half frequency
  have hp : 0 < ‖Complex.exp (Complex.I*(frequency:ℂ))-(1/2:ℂ)‖ := by linarith
  rw [actualStableScalarFrequencyResponse,norm_div,norm_one,div_le_iff₀ hp]
  linarith

theorem actual_stable_scalar_zero_frequency_attains_gain_two :
    ‖actualStableScalarFrequencyResponse 0‖=2 := by
  norm_num [actualStableScalarFrequencyResponse]

theorem actual_stable_scalar_frequency_supremum_is_two :
    sSup (Set.range (fun frequency : ℝ => ‖actualStableScalarFrequencyResponse frequency‖))=2 := by
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro value ⟨frequency,rfl⟩
      exact actual_stable_scalar_frequency_gain_at_most_two frequency
  · have hbounded : BddAbove (Set.range (fun frequency : ℝ => ‖actualStableScalarFrequencyResponse frequency‖)) :=
      ⟨2,by rintro value ⟨frequency,rfl⟩;exact actual_stable_scalar_frequency_gain_at_most_two frequency⟩
    have h := le_csSup hbounded (Set.mem_range_self (f:=fun frequency : ℝ => ‖actualStableScalarFrequencyResponse frequency‖) 0)
    simpa only [actual_stable_scalar_zero_frequency_attains_gain_two] using h

end SafeLearning.CompleteModulesScalarFrequency
