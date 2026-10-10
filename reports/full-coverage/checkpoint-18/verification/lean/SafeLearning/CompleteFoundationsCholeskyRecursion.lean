import SafeLearning.CompleteModulesCholesky

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsCholeskyRecursion

def priorProduct {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  ∑ k ∈ Finset.Iio j,L i k*L j k
def pivotArgument {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  P j j-∑ k ∈ Finset.Iio j,(L j k)^2

theorem actual_lower_factor_entry {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (hL : L.IsLowerTriangular) (i j : Fin n) :
    (L*Lᵀ) i j=priorProduct L i j+L i j*L j j := by
  have hr : (∑ k ∈ Finset.Iic j,L i k*L j k)=∑ k,L i k*L j k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k hk hnot
    have hjk : j < k := lt_of_not_ge (fun h => hnot (Finset.mem_Iic.mpr h))
    have hz : L j k=0 := hL hjk
    rw [hz,mul_zero]
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [← hr,Finset.Iic_eq_cons_Iio,Finset.sum_cons]
  unfold priorProduct
  ring

theorem actual_diagonal_recursion {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ)
    (hL : L.IsLowerTriangular) (hdiag : ∀ j,0 < L j j) (hfactor : P=L*Lᵀ) (j : Fin n) :
    L j j=Real.sqrt (pivotArgument P L j) ∧ 0 < pivotArgument P L j := by
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j j) hfactor
  rw [actual_lower_factor_entry L hL j j] at he
  have hp : pivotArgument P L j=(L j j)^2 := by
    rw [pivotArgument,he]
    simp only [priorProduct,pow_two]
    ring
  rw [hp]
  exact ⟨(Real.sqrt_sq (hdiag j).le).symm,sq_pos_of_pos (hdiag j)⟩

theorem actual_off_diagonal_recursion {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ)
    (hL : L.IsLowerTriangular) (hdiag : ∀ j,0 < L j j) (hfactor : P=L*Lᵀ) (i j : Fin n) :
    L i j=(P i j-priorProduct L i j)/L j j := by
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hfactor
  rw [actual_lower_factor_entry L hL i j] at he
  apply (eq_div_iff (hdiag j).ne').mpr
  linarith

theorem actual_positive_triangular_factor_unique {n : ℕ}
    (L R : Matrix (Fin n) (Fin n) ℝ) (hL : L.IsLowerTriangular) (hR : R.IsLowerTriangular)
    (hdiagL : ∀ j,0 < L j j) (hdiagR : ∀ j,0 < R j j) (hfactor : L*Lᵀ=R*Rᵀ) : L=R := by
  have hcolumns : ∀ b : ℕ,∀ j : Fin n,j.val=b → ∀ i : Fin n,L i j=R i j := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro j hj i
      have hprevious : ∀ k ∈ Finset.Iio j,∀ a : Fin n,L a k=R a k := by
        intro k hk a
        apply ih k.val
        · simpa only [Fin.lt_def,← hj] using Finset.mem_Iio.mp hk
        · exact rfl
      have hprefix : ∀ a : Fin n,priorProduct L a j=priorProduct R a j := by
        intro a
        apply Finset.sum_congr rfl
        intro k hk
        rw [hprevious k hk a,hprevious k hk j]
      have hd : L j j=R j j := by
        have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j j) hfactor
        rw [actual_lower_factor_entry L hL j j,actual_lower_factor_entry R hR j j,hprefix j] at he
        nlinarith [hdiagL j,hdiagR j]
      have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hfactor
      rw [actual_lower_factor_entry L hL i j,actual_lower_factor_entry R hR i j,hprefix i,hd] at he
      exact mul_right_cancel₀ (hdiagR j).ne' (add_left_cancel he)
  ext i j
  exact hcolumns j.val j rfl i

def positiveRecursion {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  L.IsLowerTriangular ∧
  (∀ j,0 < pivotArgument P L j ∧ L j j=Real.sqrt (pivotArgument P L j)) ∧
  (∀ i j,j < i → L i j=(P i j-priorProduct L i j)/L j j)

theorem actual_factor_gives_positive_recursion {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ)
    (hL : L.IsLowerTriangular) (hdiag : ∀ j,0 < L j j) (hfactor : P=L*Lᵀ) :
    positiveRecursion P L := by
  refine ⟨hL,?_,?_⟩
  · intro j
    exact ⟨(actual_diagonal_recursion P L hL hdiag hfactor j).2,
      (actual_diagonal_recursion P L hL hdiag hfactor j).1⟩
  · intro i j hij
    exact actual_off_diagonal_recursion P L hL hdiag hfactor i j

theorem actual_positive_recursion_gives_factor {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℝ)
    (hsymmetric : Pᵀ=P) (h : positiveRecursion P L) :
    (∀ j,0 < L j j) ∧ P=L*Lᵀ := by
  have hd : ∀ j,0 < L j j := by
    intro j
    rw [(h.2.1 j).2]
    exact Real.sqrt_pos.mpr (h.2.1 j).1
  have hentry : ∀ i j : Fin n,j ≤ i → P i j=(L*Lᵀ) i j := by
    intro i j hij
    rw [actual_lower_factor_entry L h.1 i j]
    rcases lt_or_eq_of_le hij with hij|hij
    · have he := (eq_div_iff (hd j).ne').mp (h.2.2 i j hij)
      linarith
    · subst i
      have he : (L j j)^2=pivotArgument P L j := by
        rw [(h.2.1 j).2,Real.sq_sqrt (h.2.1 j).1.le]
      unfold pivotArgument at he
      simp only [priorProduct,pow_two] at he ⊢
      linarith
  refine ⟨hd,?_⟩
  ext i j
  by_cases hij : j ≤ i
  · exact hentry i j hij
  · have hji : i ≤ j := le_of_lt (lt_of_not_ge hij)
    have hp := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hsymmetric
    have hls : (L*Lᵀ)ᵀ=L*Lᵀ := by simp [Matrix.transpose_mul]
    have hl := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hls
    simp only [Matrix.transpose_apply] at hp hl
    rw [← hp,hentry j i hji,hl]

theorem actual_positive_recursion_iff_positive_definite {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hsymmetric : Pᵀ=P) :
    (∃ L : Matrix (Fin n) (Fin n) ℝ,positiveRecursion P L) ↔ P.PosDef := by
  constructor
  · rintro ⟨L,h⟩
    have hf := actual_positive_recursion_gives_factor P L hsymmetric h
    rw [hf.2]
    exact SafeLearning.CompleteModulesCholesky.actual_positive_triangular_factor_implies_positive_definite L h.1 hf.1
  · intro hP
    obtain ⟨L,hL,hd,hfactor⟩ := SafeLearning.CompleteModulesCholesky.actual_positive_definite_matrix_has_cholesky P hP
    exact ⟨L,actual_factor_gives_positive_recursion P L hL hd hfactor⟩

theorem actual_cholesky_factor_exists_uniquely {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    ∃! L : Matrix (Fin n) (Fin n) ℝ,L.IsLowerTriangular ∧ (∀ j,0 < L j j) ∧ P=L*Lᵀ := by
  obtain ⟨L,hL,hd,hfactor⟩ := SafeLearning.CompleteModulesCholesky.actual_positive_definite_matrix_has_cholesky P hP
  refine ⟨L,⟨hL,hd,hfactor⟩,?_⟩
  intro R hR
  exact actual_positive_triangular_factor_unique R L hR.1 hL hR.2.1 hd (hR.2.2.symm.trans hfactor)

end SafeLearning.CompleteFoundationsCholeskyRecursion
