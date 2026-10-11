import SafeLearning.CompleteModulesGPSpectralPosterior

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesGPSpectralRemainder
open CompleteModulesMatrixGP CompleteModulesGPSpectralPosterior

theorem actual_scalar_inverse_has_the_exact_printed_three_term_remainder
    (a lambda : ℝ) (ha : 0≤a) (hlambda : 0<lambda) :
    (lambda+a)⁻¹=lambda⁻¹-a/lambda^2+a^2/(lambda^2*(lambda+a)) := by
  have hn : lambda+a≠0 := by linarith
  field_simp [hlambda.ne',hn]
  ring

variable {I : Type*} [Fintype I] [DecidableEq I]

def remainder (Q : Matrix I I ℝ) (a : I → ℝ) (lambda : ℝ) : Matrix I I ℝ :=
  Q*diagonal (fun i => a i^2/(lambda^2*(lambda+a i)))*Qᵀ

theorem actual_spectral_ridge_inverse_equals_the_first_two_terms_plus_the_explicit_remainder
    (Q : Matrix I I ℝ) (a : I → ℝ) (lambda : ℝ)
    (hleft : Qᵀ*Q=1) (hright : Q*Qᵀ=1)
    (ha : ∀ i,0≤a i) (hlambda : 0<lambda) :
    (ridgeMatrix (Q*diagonal a*Qᵀ) lambda)⁻¹=
      lambda⁻¹ • (1 : Matrix I I ℝ)-(lambda⁻¹)^2 • (Q*diagonal a*Qᵀ)+remainder Q a lambda := by
  rw [actual_orthogonal_spectral_ridge_inverse Q a lambda hleft hright ha hlambda]
  have hd : diagonal (fun i => (a i+lambda)⁻¹)=
      lambda⁻¹ • (1 : Matrix I I ℝ)-(lambda⁻¹)^2 • diagonal a+
      diagonal (fun i => a i^2/(lambda^2*(lambda+a i))) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [diagonal_apply_eq,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
        smul_eq_mul,Matrix.one_apply_eq]
      rw [add_comm (a i) lambda,actual_scalar_inverse_has_the_exact_printed_three_term_remainder
        (a i) lambda (ha i) hlambda]
      simp [div_eq_mul_inv,inv_pow,mul_comm]
    · simp [diagonal_apply_ne _ hij,hij]
  rw [hd,Matrix.mul_add,Matrix.mul_sub,Matrix.add_mul,Matrix.sub_mul]
  simp [remainder,hright]

theorem actual_explicit_remainder_has_the_true_spectral_matrix_norm_bound
    (Q : Matrix I I ℝ) (a : I → ℝ) (lambda M : ℝ)
    (hleft : Qᵀ*Q=1) (hright : Q*Qᵀ=1)
    (ha : ∀ i,0≤a i) (hlambda : 0<lambda) (hM : 0≤M)
    (hbound : ∀ i,a i^2≤M) :
    ‖remainder Q a lambda‖≤M/lambda^3 := by
  let U : unitary (Matrix I I ℝ) := ⟨Q,by
    apply Unitary.mem_iff.mpr
    simpa [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
      using And.intro hleft hright⟩
  have hnorm : ‖remainder Q a lambda‖=
      ‖fun i => a i^2/(lambda^2*(lambda+a i))‖ := by
    change ‖(U : Matrix I I ℝ)*diagonal (fun i => a i^2/(lambda^2*(lambda+a i)))*Qᵀ‖=_
    have ht : Qᵀ=(star U : unitary (Matrix I I ℝ)) := by
      simp [U,Unitary.coe_star,Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [ht,CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,l2_opNorm_diagonal]
  rw [hnorm]
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hM (pow_nonneg hlambda.le _))).mpr
  intro i
  have hp : 0<lambda+a i := by linarith [ha i]
  have hn : 0≤a i^2/(lambda^2*(lambda+a i)) := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  calc
    a i^2/(lambda^2*(lambda+a i))≤a i^2/(lambda^2*lambda) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      nlinarith [mul_nonneg (sq_nonneg lambda) (ha i)]
    _=a i^2/lambda^3 := by congr 1;ring
    _≤M/lambda^3 := by exact div_le_div_of_nonneg_right (hbound i) (by positivity)

theorem actual_spectral_remainder_is_bounded_by_the_maximum_squared_eigenvalue
    (Q : Matrix I I ℝ) (a : I → ℝ) (lambda : ℝ)
    (hleft : Qᵀ*Q=1) (hright : Q*Qᵀ=1)
    (ha : ∀ i,0≤a i) (hlambda : 0<lambda) :
    ‖remainder Q a lambda‖≤‖fun i => a i^2‖/lambda^3 := by
  apply actual_explicit_remainder_has_the_true_spectral_matrix_norm_bound Q a lambda _
    hleft hright ha hlambda (norm_nonneg _)
  intro i
  have h := norm_le_pi_norm (fun i => a i^2) i
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (a i))] at h
  exact h

theorem actual_two_ten_example_is_exact_including_the_repeating_remainder :
    (10 : ℝ)⁻¹-2/10^2=2/25 ∧ 2^2/(10^2*(10+2))=1/300 ∧
    (10 : ℝ)⁻¹-2/10^2+2^2/(10^2*(10+2))=1/12 := by norm_num

end SafeLearning.CompleteModulesGPSpectralRemainder
