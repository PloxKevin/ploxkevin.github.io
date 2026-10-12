import SafeLearning.CompleteAppliedPendulumSampling

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Filter
open scoped BigOperators Topology Matrix.Norms.Operator
namespace SafeLearning.CompleteAppliedPendulumExactSample
open SafeLearning.CompleteAppliedPendulumLinear
open SafeLearning.CompleteAppliedPendulumSampling

def frame : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;hangingPlus,hangingMinus]
def generator : Matrix (Fin 2) (Fin 2) ℂ := (1/10:ℂ) • complexMatrix (-10)
def rootDiagonal : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![hangingPlus/10,hangingMinus/10]
def actualSample : Matrix (Fin 2) (Fin 2) ℂ := NormedSpace.exp generator

theorem actual_hanging_eigenvector_frame_is_invertible : IsUnit frame := by
  rw [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  intro h
  have hi:=congrArg Complex.im h
  have hp:=Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3999)
  norm_num [frame,Matrix.det_fin_two,hangingPlus,hangingMinus] at hi
  linarith

theorem actual_sample_generator_is_diagonalized_by_its_true_eigenvectors :
    generator*frame=frame*rootDiagonal := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3999)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator,frame,rootDiagonal,complexMatrix,matrix,mul_apply,
      Fin.sum_univ_two,diagonal_apply,hangingPlus,hangingMinus]
  all_goals apply Complex.ext <;>
    simp [Complex.mul_re,Complex.mul_im,pow_two] <;> nlinarith

theorem actual_exact_sample_official_spectrum (z:ℂ) :
    z∈spectrum ℂ actualSample ↔
      z=Complex.exp (hangingPlus/10) ∨ z=Complex.exp (hangingMinus/10) := by
  obtain ⟨u,hu⟩:=actual_hanging_eigenvector_frame_is_invertible
  have hdiag : generator=(u:Matrix (Fin 2) (Fin 2) ℂ)*rootDiagonal*
      (↑u⁻¹:Matrix (Fin 2) (Fin 2) ℂ) := by
    have he:=actual_sample_generator_is_diagonalized_by_its_true_eigenvectors
    rw [←hu] at he
    calc
      generator=generator*((u:Matrix (Fin 2) (Fin 2) ℂ)*↑u⁻¹) := by simp
      _=(generator*u)*↑u⁻¹ := by rw [mul_assoc]
      _=(u*rootDiagonal)*↑u⁻¹ := by rw [he]
  have hexp : actualSample=(u:Matrix (Fin 2) (Fin 2) ℂ)*
      NormedSpace.exp rootDiagonal*(↑u⁻¹:Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold actualSample
    rw [hdiag,Matrix.exp_units_conj]
  rw [hexp,spectrum.units_conjugate]
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (NormedSpace.exp rootDiagonal).charpoly.eval z=0 ↔ _
  rw [rootDiagonal,Matrix.exp_diagonal,Matrix.charpoly_diagonal]
  simp [Fin.prod_univ_two,Pi.coe_exp,Complex.exp_eq_exp_ℂ,mul_eq_zero,sub_eq_zero]

theorem actual_every_exact_sample_spectral_mode_has_modulus_below_one (z:ℂ)
    (hz:z∈spectrum ℂ actualSample) : ‖z‖=Real.exp (-1/200) ∧ ‖z‖<1 := by
  have h:=actual_exact_sample_eigenvalue_moduli_are_strictly_below_one
  rcases (actual_exact_sample_official_spectrum z).mp hz with rfl|rfl
  · exact ⟨h.1,h.1.symm ▸ h.2.2⟩
  · exact ⟨h.2.1,h.2.1.symm ▸ h.2.2⟩

end SafeLearning.CompleteAppliedPendulumExactSample
