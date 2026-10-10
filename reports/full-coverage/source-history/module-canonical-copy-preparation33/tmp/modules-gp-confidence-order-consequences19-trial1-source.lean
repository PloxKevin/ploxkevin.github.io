import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix

namespace SafeLearning.CompleteModulesGPConfidenceOrderConsequences
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_psd_gram_scaled_by_inverse_small_regularizer_is_larger_in_loewner_order
    (K : Matrix I I ℝ) (hK : K.PosSemidef) (lambda : ℝ)
    (hlambda : 0 < lambda) (hsmall : lambda ≤ 1) :
    (lambda⁻¹ • K - K).PosSemidef := by
  have hi : 1 ≤ lambda⁻¹ := by
    apply (le_inv_iff₀ hlambda).mpr
    simpa using hsmall
  have hp : 0 ≤ lambda⁻¹ - 1 := sub_nonneg.mpr hi
  have he : lambda⁻¹ • K - K = (lambda⁻¹ - 1) • K := by
    rw [sub_smul, one_smul]
  rw [he]
  exact hK.smul hp

theorem actual_literal_one_hundredth_regularizer_has_inverse_sqrt_factor_ten :
    (Real.sqrt (1/100 : ℝ))⁻¹ = 10 := by
  have hs : Real.sqrt (1/100 : ℝ) = 1/10 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  rw [hs]
  norm_num

end SafeLearning.CompleteModulesGPConfidenceOrderConsequences
