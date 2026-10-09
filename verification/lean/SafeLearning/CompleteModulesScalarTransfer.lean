import SafeLearning.CompleteModulesScalarFrequency

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesScalarTransfer
open CompleteModulesScalarFrequency

def actualScalarStateMatrix : Matrix (Fin 1) (Fin 1) ℂ := (1/2:ℂ) • 1

def actualScalarTransferMatrix (z : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  (1 : Matrix (Fin 1) (Fin 1) ℂ)*(z • (1 : Matrix (Fin 1) (Fin 1) ℂ)-actualScalarStateMatrix)⁻¹*1

theorem actual_scalar_state_space_resolvent_is_scalar_inverse (z : ℂ) (hz : z≠1/2) :
    (z • (1 : Matrix (Fin 1) (Fin 1) ℂ)-actualScalarStateMatrix)⁻¹=
      (z-(1/2:ℂ))⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  apply Matrix.inv_eq_right_inv
  have hden : z-(1/2:ℂ)≠0 := sub_ne_zero.mpr hz
  rw [actualScalarStateMatrix,← sub_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul]
  rw [mul_inv_cancel₀ hden,one_smul]

theorem actual_scalar_state_space_transfer_is_source_fraction (z : ℂ) (hz : z≠1/2) :
    actualScalarTransferMatrix z 0 0=1/(z-(1/2:ℂ)) := by
  rw [actualScalarTransferMatrix,actual_scalar_state_space_resolvent_is_scalar_inverse z hz]
  simp

theorem actual_scalar_frequency_response_is_actual_state_space_transfer (frequency : ℝ) :
    actualScalarTransferMatrix (Complex.exp (Complex.I*(frequency:ℂ))) 0 0=
      actualStableScalarFrequencyResponse frequency := by
  have hnorm := actual_stable_scalar_frequency_denominator_norm_at_least_one_half frequency
  have hden : Complex.exp (Complex.I*(frequency:ℂ))≠(1/2:ℂ) := by
    intro he
    rw [he,sub_self,norm_zero] at hnorm
    norm_num at hnorm
  rw [actual_scalar_state_space_transfer_is_source_fraction _ hden]
  rfl

end SafeLearning.CompleteModulesScalarTransfer
