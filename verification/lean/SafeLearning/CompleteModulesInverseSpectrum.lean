import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesInverseSpectrum

variable {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]

theorem actual_inverse_eigen_diagonalization (matrix : Matrix N N ℝ) (hpositive : matrix.PosDef) :
    matrix⁻¹=Unitary.conjStarAlgAut ℝ _ hpositive.isHermitian.eigenvectorUnitary
      (Matrix.diagonal (fun i => (hpositive.isHermitian.eigenvalues i)⁻¹)) := by
  let aut := Unitary.conjStarAlgAut ℝ _ hpositive.isHermitian.eigenvectorUnitary
  have hmatrix : matrix=aut (Matrix.diagonal hpositive.isHermitian.eigenvalues) := by
    simpa [aut,Function.comp_def] using hpositive.isHermitian.spectral_theorem
  have hd : Matrix.diagonal hpositive.isHermitian.eigenvalues*
      Matrix.diagonal (fun i => (hpositive.isHermitian.eigenvalues i)⁻¹)=(1 : Matrix N N ℝ) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal_apply,Matrix.one_apply,(hpositive.eigenvalues_pos i).ne']
  apply Matrix.inv_eq_right_inv
  change matrix*aut (Matrix.diagonal (fun i => (hpositive.isHermitian.eigenvalues i)⁻¹))=1
  calc
    _ = aut (Matrix.diagonal hpositive.isHermitian.eigenvalues)*
        aut (Matrix.diagonal (fun i => (hpositive.isHermitian.eigenvalues i)⁻¹)) :=
      congrArg (fun left : Matrix N N ℝ => left*
        aut (Matrix.diagonal (fun i => (hpositive.isHermitian.eigenvalues i)⁻¹))) hmatrix
    _ = _ := by rw [← map_mul,hd,map_one]

theorem actual_inverse_spectral_norm_is_eigen_inverse_norm
    (matrix : Matrix N N ℝ) (hpositive : matrix.PosDef) :
    ‖matrix⁻¹‖=‖fun i => (hpositive.isHermitian.eigenvalues i)⁻¹‖ := by
  rw [actual_inverse_eigen_diagonalization matrix hpositive,Unitary.conjStarAlgAut_apply]
  rw [← Unitary.coe_star,CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]

def minimumEigenvalue (matrix : Matrix N N ℝ) (hpositive : matrix.PosDef) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hpositive.isHermitian.eigenvalues

theorem actual_minimum_eigenvalue_is_positive (matrix : Matrix N N ℝ) (hpositive : matrix.PosDef) :
    0 < minimumEigenvalue matrix hpositive := by
  unfold minimumEigenvalue
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hpositive.isHermitian.eigenvalues
  rw [he]
  exact hpositive.eigenvalues_pos i

theorem actual_minimum_eigenvalue_is_attained (matrix : Matrix N N ℝ) (hpositive : matrix.PosDef) :
    ∃ i, minimumEigenvalue matrix hpositive=hpositive.isHermitian.eigenvalues i := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hpositive.isHermitian.eigenvalues
  exact ⟨i,he⟩

theorem actual_inverse_spectral_norm_is_exact_reciprocal
    (matrix : Matrix N N ℝ) (hpositive : matrix.PosDef) :
    ‖matrix⁻¹‖=(minimumEigenvalue matrix hpositive)⁻¹ := by
  rw [actual_inverse_spectral_norm_is_eigen_inverse_norm matrix hpositive]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr
      (actual_minimum_eigenvalue_is_positive matrix hpositive).le)).mpr
    intro i
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hpositive.eigenvalues_pos i))]
    apply (inv_le_inv₀ (hpositive.eigenvalues_pos i)
      (actual_minimum_eigenvalue_is_positive matrix hpositive)).mpr
    exact Finset.inf'_le _ (Finset.mem_univ i)
  · obtain ⟨i,he⟩ := actual_minimum_eigenvalue_is_attained matrix hpositive
    rw [he]
    have h := norm_le_pi_norm (fun i => (hpositive.isHermitian.eigenvalues i)⁻¹) i
    simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hpositive.eigenvalues_pos i))] using h

open Filter
open scoped Topology in
theorem actual_inverse_norm_blows_up_at_singular_boundary {T : Type*}
    (filter : Filter T) (matrix : T → Matrix N N ℝ) (hpositive : ∀ t, (matrix t).PosDef)
    (hboundary : Tendsto (fun t => minimumEigenvalue (matrix t) (hpositive t)) filter (𝓝 0)) :
    Tendsto (fun t => ‖(matrix t)⁻¹‖) filter atTop := by
  have hp : Tendsto (fun t => minimumEigenvalue (matrix t) (hpositive t)) filter (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hboundary,Filter.Eventually.of_forall (fun t =>
      actual_minimum_eigenvalue_is_positive (matrix t) (hpositive t))⟩
  have hi := hp.inv_tendsto_nhdsGT_zero
  change Tendsto (fun t => (minimumEigenvalue (matrix t) (hpositive t))⁻¹) filter atTop at hi
  exact hi.congr' (Filter.Eventually.of_forall (fun t =>
    (actual_inverse_spectral_norm_is_exact_reciprocal (matrix t) (hpositive t)).symm))

end SafeLearning.CompleteModulesInverseSpectrum
