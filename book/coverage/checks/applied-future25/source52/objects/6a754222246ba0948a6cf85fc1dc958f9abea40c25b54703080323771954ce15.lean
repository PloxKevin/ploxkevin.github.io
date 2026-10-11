import SafeLearning.CompleteModulesKernel

set_option autoImplicit false
noncomputable section
open SafeLearning.CompleteModulesKernel
open scoped BigOperators
namespace SafeLearning.CompleteModulesKernelCorollaries

variable {H I X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype I]

theorem noiseless_residual_orthogonal (feature : I → H) (target : H) (weight : I → ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)=inner ℝ (feature i) target) :
    ∀ i, inner ℝ (target-combination feature weight) (feature i)=0 := by
  intro i
  have h := normal_system_combination_inner feature target weight 0
    (by simpa only [zero_mul,add_zero] using hsystem) i
  simp only [zero_mul,sub_zero] at h
  rw [real_inner_comm (combination feature weight) (feature i),
    real_inner_comm target (feature i)] at h
  rw [inner_sub_left,h,sub_self]

theorem noiseless_residual_target_inner (feature : I → H) (target : H) (weight : I → ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)=inner ℝ (feature i) target) :
    inner ℝ (target-combination feature weight) target=‖target-combination feature weight‖^2 := by
  have ho : inner ℝ (target-combination feature weight) (combination feature weight)=0 := by
    rw [inner_combination]
    simp only [noiseless_residual_orthogonal feature target weight hsystem,mul_zero,
      Finset.sum_const_zero]
  have hs := real_inner_self_eq_norm_sq (target-combination feature weight)
  rw [inner_sub_right,ho,sub_zero] at hs
  exact hs

def sharpResidualFunction (feature : I → H) (target : H) (weight : I → ℝ) (B : ℝ) : H :=
  (B/‖target-combination feature weight‖) • (target-combination feature weight)

theorem sharp_residual_function_norm (feature : I → H) (target : H) (weight : I → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hr : target-combination feature weight≠0) :
    ‖sharpResidualFunction feature target weight B‖=B := by
  have hp := norm_pos_iff.mpr hr
  rw [sharpResidualFunction,norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hB (le_of_lt hp))]
  exact div_mul_cancel₀ B hp.ne'

theorem sharp_residual_function_has_zero_data (feature : I → H) (target : H)
    (weight : I → ℝ) (B : ℝ)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)=inner ℝ (feature i) target) :
    ∀ i, inner ℝ (sharpResidualFunction feature target weight B) (feature i)=0 := by
  intro i
  rw [sharpResidualFunction,real_inner_smul_left,
    noiseless_residual_orthogonal feature target weight hsystem i,mul_zero]

theorem sharp_residual_function_attains_error (feature : I → H) (target : H)
    (weight : I → ℝ) (B : ℝ) (hB : 0 ≤ B) (hr : target-combination feature weight≠0)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)=inner ℝ (feature i) target) :
    |inner ℝ (sharpResidualFunction feature target weight B) target-
      ∑ i, weight i*inner ℝ (sharpResidualFunction feature target weight B) (feature i)| =
      B*Real.sqrt (posteriorVariance feature target weight) := by
  have hp := norm_pos_iff.mpr hr
  have he := posterior_residual_norm_identity feature target weight 0
    (by simpa only [zero_mul,add_zero] using hsystem)
  simp only [zero_mul,sub_zero] at he
  rw [← he,Real.sqrt_sq (norm_nonneg _)]
  simp only [sharp_residual_function_has_zero_data feature target weight B hsystem,
    mul_zero,Finset.sum_const_zero,sub_zero]
  rw [sharpResidualFunction,real_inner_smul_left,
    noiseless_residual_target_inner feature target weight hsystem]
  have hid : B/‖target-combination feature weight‖*‖target-combination feature weight‖^2=
      B*‖target-combination feature weight‖ := by
    field_simp
    <;> ring
  rw [hid,abs_of_nonneg (mul_nonneg hB (norm_nonneg _))]

theorem zero_power_function_is_exact (feature : I → H) (target coefficient : H)
    (weight : I → ℝ) (hv : posteriorVariance feature target weight=0)
    (hsystem : ∀ i, (∑ j, inner ℝ (feature i) (feature j)*weight j)=inner ℝ (feature i) target) :
    inner ℝ coefficient target=∑ i, weight i*inner ℝ coefficient (feature i) := by
  have h := noiseless_posterior_error feature target coefficient weight 0 ‖coefficient‖
    (by norm_num) le_rfl (by simpa only [zero_mul,add_zero] using hsystem)
  rw [hv,Real.sqrt_zero,mul_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

theorem singleton_residual_squared_norm (a b : H) (r : ℝ)
    (haa : inner ℝ a a=1) (hbb : inner ℝ b b=1) (hab : inner ℝ a b=r) :
    ‖b-r • a‖^2=1-r^2 := by
  have hba : inner ℝ b a=r := (real_inner_comm a b).trans hab
  rw [← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_smul_left,real_inner_smul_right,
    haa,hbb,hab,hba]
  ring

theorem singleton_noiseless_error (a b coefficient : H) (r : ℝ)
    (haa : inner ℝ a a=1) (hbb : inner ℝ b b=1) (hab : inner ℝ a b=r) :
    |inner ℝ coefficient b-r*inner ℝ coefficient a| ≤ ‖coefficient‖*Real.sqrt (1-r^2) := by
  have hsq := singleton_residual_squared_norm a b r haa hbb hab
  have hnorm : Real.sqrt (1-r^2)=‖b-r • a‖ := by
    rw [← hsq,Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm,← real_inner_smul_right,← inner_sub_right]
  exact abs_real_inner_le_norm _ _

theorem singleton_noiseless_numeric (a b coefficient : H)
    (haa : inner ℝ a a=1) (hbb : inner ℝ b b=1) (hab : inner ℝ a b=3/5)
    (hf : ‖coefficient‖≤2) :
    |inner ℝ coefficient b-(3/5)*inner ℝ coefficient a|≤8/5 := by
  have h := singleton_noiseless_error a b coefficient (3/5) haa hbb hab
  norm_num at h
  linarith

section ActualRKHS
variable [CompleteSpace H] [RKHS ℝ H X ℝ]

theorem equal_evaluations_equal_functions (first second : H)
    (he : ∀ x, first x=second x) : first=second := RKHS.ext he

theorem equal_evaluations_equal_norms (first second : H)
    (he : ∀ x, first x=second x) : ‖first‖=‖second‖ :=
  congrArg norm (equal_evaluations_equal_functions first second he)

theorem actual_singleton_noiseless_numeric (function : H) (a b : X)
    (haa : scalarKernel (H:=H) a a=1) (hbb : scalarKernel (H:=H) b b=1)
    (hab : scalarKernel (H:=H) a b=3/5) (hf : ‖function‖≤2) :
    |function b-(3/5)*function a|≤8/5 := by
  simpa only [scalar_section_reproduces] using
    singleton_noiseless_numeric (scalarSection (H:=H) a) (scalarSection (H:=H) b)
      function haa hbb hab hf

end ActualRKHS
end SafeLearning.CompleteModulesKernelCorollaries
