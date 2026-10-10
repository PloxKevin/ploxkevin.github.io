import SafeLearning.CompleteModulesCayleyInverse
import SafeLearning.CompleteModulesCayleyPlane

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesCayleyRange

theorem actual_every_plane_skew_matrix_has_scalar_form
    (skew : Matrix (Fin 2) (Fin 2) ℝ) (hskew : skewᵀ= -skew) :
    skew=SafeLearning.CompleteModulesCayleyPlane.actualPlaneSkew (skew 0 1) := by
  have h00 := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => matrix 0 0) hskew
  have h11 := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => matrix 1 1) hskew
  have h10 := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => matrix 0 1) hskew
  simp only [Matrix.transpose_apply,Matrix.neg_apply] at h00 h11 h10
  have hz00 : skew 0 0=0 := by linarith
  have hz11 : skew 1 1=0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SafeLearning.CompleteModulesCayleyPlane.actualPlaneSkew,hz00,hz11,h10]

theorem actual_plane_rotation_denominator_is_invertible
    (orthogonal : Matrix (Fin 2) (Fin 2) ℝ)
    (horthogonal : orthogonalᵀ*orthogonal=1) (hdet : orthogonal.det=1)
    (hnotpi : orthogonal≠ -(1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    IsUnit (1+orthogonal) := by
  have hmem : orthogonal ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
    ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mpr horthogonal,hdet⟩
  obtain ⟨hdiagonal,hoff,hcircle⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp hmem
  have hnonzero : 1+orthogonal 0 0≠0 := by
    intro hzero
    have ha : orthogonal 0 0= -1 := by linarith
    have hb : orthogonal 0 1=0 := by nlinarith
    have hc : orthogonal 1 0=0 := by linarith
    have hd : orthogonal 1 1= -1 := by linarith
    apply hnotpi
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply,ha,hb,hc,hd]
  apply ((1+orthogonal).isUnit_iff_isUnit_det).mpr
  apply isUnit_iff_ne_zero.mpr
  have he : (1+orthogonal).det=2*(1+orthogonal 0 0) := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply,Matrix.one_apply]
    norm_num
    rw [← hdiagonal,← neg_eq_iff_eq_neg.mpr hoff]
    nlinarith
  rw [he]
  exact mul_ne_zero (by norm_num) hnonzero

theorem actual_plane_cayley_range_is_exact
    (orthogonal : Matrix (Fin 2) (Fin 2) ℝ) :
    (∃ parameter : ℝ, SafeLearning.CompleteModulesCayley.actualCayley
      (SafeLearning.CompleteModulesCayleyPlane.actualPlaneSkew parameter)=orthogonal) ↔
    orthogonalᵀ*orthogonal=1 ∧ orthogonal.det=1 ∧
      orthogonal≠ -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor
  · rintro ⟨parameter,rfl⟩
    exact ⟨SafeLearning.CompleteModulesCayley.actual_cayley_is_orthogonal _
        (SafeLearning.CompleteModulesCayleyPlane.actual_plane_matrix_is_skew parameter),
      SafeLearning.CompleteModulesCayley.actual_cayley_has_determinant_one _
        (SafeLearning.CompleteModulesCayleyPlane.actual_plane_matrix_is_skew parameter),
      SafeLearning.CompleteModulesCayleyPlane.actual_plane_cayley_never_produces_pi_rotation parameter⟩
  · rintro ⟨horthogonal,hdet,hnotpi⟩
    have hunit := actual_plane_rotation_denominator_is_invertible orthogonal horthogonal hdet hnotpi
    let skew := SafeLearning.CompleteModulesCayleyInverse.actualInverseCayley orthogonal
    have hs := SafeLearning.CompleteModulesCayleyInverse.actual_inverse_cayley_is_skew_symmetric
      orthogonal horthogonal hunit
    have he := actual_every_plane_skew_matrix_has_scalar_form skew hs
    refine ⟨skew 0 1,?_⟩
    rw [← he]
    exact SafeLearning.CompleteModulesCayleyInverse.actual_inverse_cayley_recovers_orthogonal
      orthogonal horthogonal hunit

theorem actual_every_orthogonal_reflection_has_negative_one_eigenvector
    {N : Type*} [Fintype N] [DecidableEq N]
    (orthogonal : Matrix N N ℝ) (horthogonal : orthogonalᵀ*orthogonal=1)
    (hdet : orthogonal.det= -1) :
    ∃ vector : N → ℝ, orthogonal*ᵥvector= -vector ∧ vector≠0 := by
  classical
  by_contra hnone
  have hnoeigen : ∀ vector : N → ℝ, orthogonal*ᵥvector= -vector → vector=0 := by
    intro vector heigen
    by_contra hnonzero
    exact hnone ⟨vector,heigen,hnonzero⟩
  obtain ⟨skew,⟨hskew,he⟩,_⟩ :=
    SafeLearning.CompleteModulesCayleyInverse.actual_orthogonal_without_negative_one_has_unique_skew_preimage
      orthogonal horthogonal hnoeigen
  have hd := SafeLearning.CompleteModulesCayley.actual_cayley_has_determinant_one skew hskew
  rw [he,hdet] at hd
  norm_num at hd

end SafeLearning.CompleteModulesCayleyRange
