import SafeLearning.CompleteModulesSemidefiniteSchur

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
namespace SafeLearning.CompleteModulesSingularSchurPractice
open CompleteModulesPseudoinverse CompleteModulesSemidefiniteSchur

def actualSingularCornerMatrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a,b;b,0]

theorem actual_singular_corner_quadratic (a b : ℝ) (v : Fin 2→ℝ) :
    v ⬝ᵥ (actualSingularCornerMatrix a b *ᵥ v)=a*(v 0)^2+2*b*v 0*v 1 := by
  simp [actualSingularCornerMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_singular_corner_test_at_one_and_arbitrary_t (a b t : ℝ) :
    (![1,t] : Fin 2→ℝ) ⬝ᵥ (actualSingularCornerMatrix a b *ᵥ ![1,t])=a+2*b*t := by
  rw [actual_singular_corner_quadratic]
  norm_num

theorem actual_nonzero_off_diagonal_has_a_genuine_negative_quadratic_witness
    (a b : ℝ) (hb : b≠0) :
    (![1,-(a+1)/(2*b)] : Fin 2→ℝ) ⬝ᵥ
      (actualSingularCornerMatrix a b *ᵥ ![1,-(a+1)/(2*b)])= -1 := by
  rw [actual_singular_corner_test_at_one_and_arbitrary_t]
  field_simp
  ring

theorem actual_singular_corner_matrix_is_psd_iff_exact_source_conditions (a b : ℝ) :
    (actualSingularCornerMatrix a b).PosSemidef ↔ 0≤a ∧ b=0 := by
  constructor
  · intro h
    have ha:=h.dotProduct_mulVec_nonneg (![1,0] : Fin 2→ℝ)
    simp only [star_trivial,actual_singular_corner_test_at_one_and_arbitrary_t,mul_zero,add_zero] at ha
    refine ⟨ha,?_⟩
    by_contra hb
    have hn:=h.dotProduct_mulVec_nonneg (![1,-(a+1)/(2*b)] : Fin 2→ℝ)
    rw [star_trivial,actual_nonzero_off_diagonal_has_a_genuine_negative_quadratic_witness a b hb] at hn
    norm_num at hn
  · rintro ⟨ha,rfl⟩
    have he : actualSingularCornerMatrix a 0=Matrix.diagonal (![a,0] : Fin 2→ℝ) := by
      ext i j;fin_cases i <;> fin_cases j <;> simp [actualSingularCornerMatrix]
    rw [he,Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> simp_all

variable {Left Right : Type*} [Fintype Left] [DecidableEq Left]
  [Fintype Right] [DecidableEq Right]

theorem actual_zero_corner_range_condition_is_exactly_zero_off_diagonal
    (B : Matrix Left Right ℝ) : actualRangeCondition B (0 : Matrix Right Right ℝ) ↔ B=0 := by
  rw [actual_true_range_condition_iff_pseudoinverse_identity B 0 Matrix.isHermitian_zero]
  simp only [actual_zero_matrix_pseudoinverse_is_zero,Matrix.mul_zero,Matrix.zero_mul]
  exact eq_comm

theorem actual_zero_corner_general_psd_iff_both_source_conditions
    (A : Matrix Left Left ℝ) (B : Matrix Left Right ℝ) :
    (actualSymmetricBlock A B (0 : Matrix Right Right ℝ)).PosSemidef ↔
      B=0 ∧ A.PosSemidef := by
  rw [actual_semidefinite_schur_iff_corner_range_and_pseudoinverse_remainder A B 0 Matrix.isHermitian_zero,
    actual_zero_corner_range_condition_is_exactly_zero_off_diagonal,
    actual_zero_matrix_pseudoinverse_is_zero,Matrix.mul_zero,Matrix.zero_mul,sub_zero]
  simp [Matrix.PosSemidef.zero]

omit [DecidableEq Left] in
theorem actual_invertible_corner_has_the_entire_space_as_its_true_range
    (D : Matrix Right Right ℝ) (hD : IsUnit D) :
    Set.range (fun y : Right→ℝ => D *ᵥ y)=Set.univ := by
  let := hD.invertible
  apply Set.eq_univ_of_forall
  intro z
  refine ⟨D⁻¹*ᵥ z,?_⟩
  change D*ᵥ (D⁻¹*ᵥ z)=z
  rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]

omit [DecidableEq Left] in
theorem actual_definite_corner_needs_no_extra_range_restriction
    (B : Matrix Left Right ℝ) (D : Matrix Right Right ℝ) (hD : D.PosDef) :
    actualRangeCondition B D := by
  rw [actualRangeCondition,actual_invertible_corner_has_the_entire_space_as_its_true_range D hD.isUnit]
  exact Set.subset_univ _

theorem actual_genuine_pseudoinverse_of_an_invertible_symmetric_corner_is_its_inverse
    (D : Matrix Right Right ℝ) (hsymmetric : D.IsHermitian) (hD : IsUnit D) :
    actualPseudoinverse D hsymmetric=D⁻¹ := by
  let := hD.invertible
  let T:=actualPseudoinverse D hsymmetric
  have he : D*T*D=D :=
    (actual_pseudoinverse_satisfies_both_generalized_inverse_equations D hsymmetric).1
  calc
    T=(D⁻¹*D)*T*(D*D⁻¹) := by
      rw [Matrix.inv_mul_of_invertible,Matrix.mul_inv_of_invertible,Matrix.one_mul,Matrix.mul_one]
    _=D⁻¹*(D*T*D)*D⁻¹ := by noncomm_ring
    _=D⁻¹*D*D⁻¹ := by rw [he]
    _=D⁻¹ := by rw [Matrix.inv_mul_of_invertible,Matrix.one_mul]

theorem actual_pseudoinverse_remainder_alone_can_pass_while_the_true_matrix_fails :
    (actualSingularCornerMatrix 1 1).PosSemidef=False ∧
      ((!![1] : Matrix (Fin 1) (Fin 1) ℝ)-
        (!![1] : Matrix (Fin 1) (Fin 1) ℝ)*
          actualPseudoinverse (0 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.isHermitian_zero*
          (!![1] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).PosSemidef := by
  constructor
  · apply propext
    rw [actual_singular_corner_matrix_is_psd_iff_exact_source_conditions]
    norm_num
  · rw [actual_zero_matrix_pseudoinverse_is_zero,Matrix.mul_zero,Matrix.zero_mul,sub_zero]
    have he : (!![1] : Matrix (Fin 1) (Fin 1) ℝ)=Matrix.diagonal (fun _ => 1) := by
      ext i j;fin_cases i;fin_cases j;rfl
    rw [he,Matrix.posSemidef_diagonal_iff]
    norm_num

end SafeLearning.CompleteModulesSingularSchurPractice
