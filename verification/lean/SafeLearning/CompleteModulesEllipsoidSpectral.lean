import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set Unitary
open scoped MatrixOrder
namespace SafeLearning.CompleteModulesEllipsoidSpectral

variable {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index]

def actualMaximumEigenvalue (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hsymmetric.eigenvalues

theorem actual_maximum_eigenvalue_is_one_of_the_true_eigenvalues
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    ∃ index,actualMaximumEigenvalue matrix hsymmetric=hsymmetric.eigenvalues index := by
  obtain ⟨index,_,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hsymmetric.eigenvalues
  exact ⟨index,he⟩

theorem actual_maximum_eigenvalue_bound_iff_every_true_eigenvalue_is_bounded
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) (bound : ℝ) :
    actualMaximumEigenvalue matrix hsymmetric≤bound ↔ ∀ index,hsymmetric.eigenvalues index≤bound := by
  constructor
  · intro h index
    exact (Finset.le_sup' hsymmetric.eigenvalues (Finset.mem_univ index)).trans h
  · intro h
    exact Finset.sup'_le _ _ (fun index _ => h index)

theorem actual_symmetric_shift_is_psd_iff_bound_exceeds_the_true_largest_eigenvalue
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) (bound : ℝ) :
    (bound • (1 : Matrix Index Index ℝ)-matrix).PosSemidef ↔
      actualMaximumEigenvalue matrix hsymmetric≤bound := by
  let aut := Unitary.conjStarAlgAut ℝ _ hsymmetric.eigenvectorUnitary
  have hm : matrix=aut (Matrix.diagonal hsymmetric.eigenvalues) := by
    simpa [aut,Function.comp_def] using hsymmetric.spectral_theorem
  have hd : Matrix.diagonal (fun index => bound-hsymmetric.eigenvalues index)=
      bound • (1 : Matrix Index Index ℝ)-Matrix.diagonal hsymmetric.eigenvalues := by
    ext row column
    by_cases he : row=column
    · subst column;simp
    · simp [he]
  have he : bound • (1 : Matrix Index Index ℝ)-matrix=
      aut (Matrix.diagonal (fun index => bound-hsymmetric.eigenvalues index)) := by
    rw [hd,map_sub,map_smul,map_one,←hm]
  rw [he,Unitary.conjStarAlgAut_apply,
    isUnit_coe.posSemidef_star_right_conjugate_iff,Matrix.posSemidef_diagonal_iff,
    actual_maximum_eigenvalue_bound_iff_every_true_eigenvalue_is_bounded]
  simp

def quadraticValue (matrix : Matrix Index Index ℝ) (vector : Index → ℝ) : ℝ :=
  vector ⬝ᵥ (matrix *ᵥ vector)

def unitBallValues (matrix : Matrix Index Index ℝ) : Set ℝ :=
  {value | ∃ vector : Index → ℝ,vector ⬝ᵥ vector ≤ 1 ∧ value=quadraticValue matrix vector}

theorem actual_quadratic_unit_ball_upper_bound
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian)
    (vector : Index → ℝ) (hvector : vector ⬝ᵥ vector ≤ 1) :
    quadraticValue matrix vector ≤ max 0 (actualMaximumEigenvalue matrix hsymmetric) := by
  let bound := max 0 (actualMaximumEigenvalue matrix hsymmetric)
  have hpsd : (bound • (1 : Matrix Index Index ℝ)-matrix).PosSemidef :=
    (actual_symmetric_shift_is_psd_iff_bound_exceeds_the_true_largest_eigenvalue
      matrix hsymmetric bound).2 (le_max_right _ _)
  have hquad := hpsd.dotProduct_mulVec_nonneg vector
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul] at hquad
  have hb : 0 ≤ bound := le_max_left _ _
  have hu : bound*(vector ⬝ᵥ vector) ≤ bound := by
    calc
      bound*(vector ⬝ᵥ vector) ≤ bound*1 := mul_le_mul_of_nonneg_left hvector hb
      _=bound := mul_one bound
  unfold quadraticValue
  linarith

omit [Nonempty Index] in
theorem actual_true_largest_eigenvector_has_unit_energy_and_its_eigenvalue
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) (index : Index) :
    (⇑(hsymmetric.eigenvectorBasis index) ⬝ᵥ ⇑(hsymmetric.eigenvectorBasis index))=1 ∧
    quadraticValue matrix ⇑(hsymmetric.eigenvectorBasis index)=hsymmetric.eigenvalues index := by
  constructor
  · simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using
      hsymmetric.eigenvectorBasis.inner_eq_one index
  · simpa only [quadraticValue,star_trivial,RCLike.re_to_real] using
      (hsymmetric.eigenvalues_eq index).symm

theorem actual_unit_ball_quadratic_maximum
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    IsGreatest (unitBallValues matrix) (max 0 (actualMaximumEigenvalue matrix hsymmetric)) := by
  constructor
  · by_cases hmax : 0 ≤ actualMaximumEigenvalue matrix hsymmetric
    · obtain ⟨index,he⟩ := actual_maximum_eigenvalue_is_one_of_the_true_eigenvalues matrix hsymmetric
      obtain ⟨henergy,hvalue⟩ := actual_true_largest_eigenvector_has_unit_energy_and_its_eigenvalue
        matrix hsymmetric index
      refine ⟨⇑(hsymmetric.eigenvectorBasis index),by linarith,?_⟩
      rw [max_eq_right hmax,he,hvalue]
    · refine ⟨0,by simp,?_⟩
      rw [max_eq_left (le_of_not_ge hmax)]
      simp [quadraticValue]
  · rintro value ⟨vector,hvector,rfl⟩
    exact actual_quadratic_unit_ball_upper_bound matrix hsymmetric vector hvector

end SafeLearning.CompleteModulesEllipsoidSpectral
