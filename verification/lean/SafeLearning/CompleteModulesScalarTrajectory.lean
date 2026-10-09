import SafeLearning.CompleteModulesScalarBoundedReal
import SafeLearning.CompleteModulesDissipation

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesScalarTrajectory
open CompleteModulesScalarBoundedReal CompleteModulesDissipation

def actualStableScalarState (initial : ℝ) (input : ℕ → ℝ) : ℕ → ℝ
  | 0 => initial
  | time+1 => (1/2:ℝ)*actualStableScalarState initial input time+input time

theorem actual_stable_scalar_state_space_recursion (initial : ℝ) (input : ℕ → ℝ) :
    actualStableScalarState initial input 0=initial ∧
    ∀ time,actualStableScalarState initial input (time+1)=
      (1/2:ℝ)*actualStableScalarState initial input time+input time := by
  simp [actualStableScalarState]

theorem actual_stable_scalar_certificate_implies_actual_storage_dissipation
    (storage gain initial : ℝ) (input : ℕ → ℝ)
    (hcertificate : (-actualScalarGainMatrix storage gain).PosSemidef) (time : ℕ) :
    storage*(actualStableScalarState initial input (time+1))^2-
      storage*(actualStableScalarState initial input time)^2 ≤
    gain^2*(input time)^2-(actualStableScalarState initial input time)^2 := by
  have h := (actual_scalar_gain_matrix_negative_semidefinite_iff storage gain).mp hcertificate
    (actualStableScalarState initial input time) (input time)
  rw [actualStableScalarState]
  nlinarith

theorem actual_stable_scalar_finite_output_energy_bound
    (storage gain initial : ℝ) (input : ℕ → ℝ) (hstorage : 0 ≤ storage)
    (hcertificate : (-actualScalarGainMatrix storage gain).PosSemidef) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,(actualStableScalarState initial input time)^2) ≤
      gain^2*(∑ time ∈ Finset.range horizon,(input time)^2)+storage*initial^2 := by
  simpa only [actualStableScalarState] using actual_nonnegative_storage_implies_finite_energy_gain
    (fun time => storage*(actualStableScalarState initial input time)^2) input
    (actualStableScalarState initial input) gain
    (fun time => mul_nonneg hstorage (sq_nonneg _))
    (actual_stable_scalar_certificate_implies_actual_storage_dissipation storage gain initial input hcertificate) horizon

theorem actual_source_gain_two_finite_output_energy_bound
    (initial : ℝ) (input : ℕ → ℝ) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,(actualStableScalarState initial input time)^2) ≤
      4*(∑ time ∈ Finset.range horizon,(input time)^2)+2*initial^2 := by
  have h := actual_stable_scalar_finite_output_energy_bound 2 2 initial input (by norm_num)
    actual_scalar_source_matrix_is_negative_semidefinite horizon
  norm_num at h ⊢
  exact h

theorem actual_source_gain_two_infinite_output_energy_bound
    (initial : ℝ) (input : ℕ → ℝ) (hinput : Summable (fun time => (input time)^2)) :
    Summable (fun time => (actualStableScalarState initial input time)^2) ∧
    (∑' time,(actualStableScalarState initial input time)^2) ≤
      4*(∑' time,(input time)^2)+2*initial^2 := by
  have h := actual_storage_dissipation_with_square_summable_input_has_bounded_square_summable_output
    (fun time => 2*(actualStableScalarState initial input time)^2) input
    (actualStableScalarState initial input) 2
    (fun time => mul_nonneg (by norm_num) (sq_nonneg _))
    (actual_stable_scalar_certificate_implies_actual_storage_dissipation 2 2 initial input actual_scalar_source_matrix_is_negative_semidefinite) hinput
  norm_num [actualStableScalarState] at h ⊢
  exact h

end SafeLearning.CompleteModulesScalarTrajectory
