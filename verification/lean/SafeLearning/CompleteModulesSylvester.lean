import SafeLearning.CompleteModulesCholesky

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesSylvester

variable {n : ℕ}

theorem actual_scalar_matrix_positive_definite_of_positive_determinant
    (matrix : Matrix (Fin 1) (Fin 1) ℝ) (hdet : 0 < matrix.det) : matrix.PosDef := by
  have he : matrix=Matrix.diagonal (fun _ => matrix 0 0) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [he,Matrix.posDef_diagonal_iff]
  intro i
  simpa only [Matrix.det_fin_one] using hdet

theorem actual_last_schur_block_is_positive_definite
    (first : Matrix (Fin n) (Fin n) ℝ) (cross : Matrix (Fin n) (Fin 1) ℝ)
    (last : Matrix (Fin 1) (Fin 1) ℝ) (hfirst : first.PosDef)
    (hdet : 0 < (Matrix.fromBlocks first cross crossᴴ last).det) :
    (Matrix.fromBlocks first cross crossᴴ last).PosDef := by
  letI := hfirst.isUnit.invertible
  have hdetfactor : (Matrix.fromBlocks first cross crossᴴ last).det=
      first.det*(last-crossᴴ*first⁻¹*cross).det := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using Matrix.det_fromBlocks₁₁ first cross crossᴴ last
  have hschurdet : 0 < (last-crossᴴ*first⁻¹*cross).det := by
    rw [hdetfactor] at hdet
    exact pos_of_mul_pos_right hdet hfirst.det_pos.le
  have hschur := actual_scalar_matrix_positive_definite_of_positive_determinant
    (last-crossᴴ*first⁻¹*cross) hschurdet
  have hsemidefinite := (Matrix.PosDef.fromBlocks₁₁ cross last hfirst).mpr hschur.posSemidef
  exact hsemidefinite.posDef_iff_det_ne_zero.mpr hdet.ne'

def positiveLeadingPrincipalMinors (matrix : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ size, ∀ hsize : size ≤ n,
    0 < (matrix.submatrix (Fin.castLE hsize) (Fin.castLE hsize)).det

theorem actual_symmetric_matrix_with_positive_leading_minors_is_positive_definite
    (size : ℕ) : ∀ matrix : Matrix (Fin size) (Fin size) ℝ,
    matrix.IsHermitian → positiveLeadingPrincipalMinors matrix → matrix.PosDef := by
  induction size with
  | zero =>
    intro matrix hsymmetry hminors
    have he : matrix=(1 : Matrix (Fin 0) (Fin 0) ℝ) := by ext i; exact Fin.elim0 i
    rw [he]
    exact Matrix.PosDef.one
  | succ size ih =>
    intro matrix hsymmetry hminors
    let first := matrix.submatrix Fin.castSucc Fin.castSucc
    let cross := matrix.submatrix Fin.castSucc (fun _ : Fin 1 => Fin.last size)
    let last := matrix.submatrix (fun _ : Fin 1 => Fin.last size) (fun _ : Fin 1 => Fin.last size)
    have hfirstminors : positiveLeadingPrincipalMinors first := by
      intro smaller hsmaller
      have he : first.submatrix (Fin.castLE hsmaller) (Fin.castLE hsmaller)=
          matrix.submatrix (Fin.castLE (hsmaller.trans (Nat.le_succ size)))
            (Fin.castLE (hsmaller.trans (Nat.le_succ size))) := by
        ext i j
        rfl
      rw [he]
      exact hminors smaller (hsmaller.trans (Nat.le_succ size))
    have hfirst : first.PosDef := ih first (hsymmetry.submatrix Fin.castSucc) hfirstminors
    let equivalence : Fin size ⊕ Fin 1 ≃ Fin (size+1) := finSumFinEquiv
    have hblocks : matrix.submatrix equivalence equivalence=Matrix.fromBlocks first cross crossᴴ last := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · have hj : j=0 := Subsingleton.elim _ _
        subst j
        rfl
      · have hi : i=0 := Subsingleton.elim _ _
        subst i
        have hlast : Fin.natAdd size (0 : Fin 1)=Fin.last size := by rfl
        have hcast : Fin.castAdd 1 j=j.castSucc := by rfl
        simpa [Matrix.submatrix_apply,equivalence,cross,Matrix.conjTranspose_apply,hlast,hcast]
          using hsymmetry.apply (Fin.castSucc j) (Fin.last size)
      · have hi : i=0 := Subsingleton.elim _ _
        have hj : j=0 := Subsingleton.elim _ _
        subst i
        subst j
        rfl
    have hfull : 0 < matrix.det := by
      have h := hminors (size+1) le_rfl
      simpa using h
    have hblockdet : 0 < (Matrix.fromBlocks first cross crossᴴ last).det := by
      rw [← hblocks,Matrix.det_submatrix_equiv_self]
      exact hfull
    have hpositive := actual_last_schur_block_is_positive_definite first cross last hfirst hblockdet
    rw [← hblocks] at hpositive
    have hback := hpositive.submatrix equivalence.symm.injective
    simpa [Matrix.submatrix_submatrix] using hback

theorem actual_sylvester_criterion (matrix : Matrix (Fin n) (Fin n) ℝ)
    (hsymmetry : matrix.IsHermitian) :
    matrix.PosDef ↔ positiveLeadingPrincipalMinors matrix := by
  constructor
  · intro hpositive size hsize
    exact CompleteModulesCholesky.actual_positive_definite_leading_principal_minors_are_positive
      matrix hpositive size hsize
  · exact actual_symmetric_matrix_with_positive_leading_minors_is_positive_definite n matrix hsymmetry

end SafeLearning.CompleteModulesSylvester
