import SafeLearning.CompleteModulesSDPCone
import SafeLearning.CompleteModulesSDPTrace

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped MatrixOrder
namespace SafeLearning.CompleteModulesSDPConeCorollaries

variable {Index Other : Type*} [Fintype Index] [DecidableEq Index]

def actualPositiveSquareRoot (matrix : Matrix Index Index ℝ) : Matrix Index Index ℝ := CFC.sqrt matrix

theorem actual_positive_square_root_is_psd_symmetric_and_squares_to_the_matrix
    (matrix : Matrix Index Index ℝ) (hmatrix : matrix.PosSemidef) :
    (actualPositiveSquareRoot matrix).PosSemidef ∧
      (actualPositiveSquareRoot matrix)ᵀ=actualPositiveSquareRoot matrix ∧
      actualPositiveSquareRoot matrix*actualPositiveSquareRoot matrix=matrix := by
  have hp : (actualPositiveSquareRoot matrix).PosSemidef := (CFC.sqrt_nonneg matrix).posSemidef
  exact ⟨hp,by simpa using hp.isHermitian.eq,by simpa [actualPositiveSquareRoot,pow_two] using CFC.sq_sqrt matrix hmatrix.nonneg⟩

omit [DecidableEq Index] in
theorem actual_real_symmetric_pd_iff_every_nonzero_vector_has_positive_quadratic
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix.PosDef ↔ ∀ vector : Index→ℝ,vector≠0→0 < vector ⬝ᵥ (matrix*ᵥ vector) := by
  simp only [Matrix.posDef_iff_dotProduct_mulVec,hsymmetric,true_and,star_trivial]

omit [DecidableEq Index] in
theorem actual_nonnegative_cone_combination_has_the_literal_quadratic_identity
    (first second : Matrix Index Index ℝ) (left right : ℝ) (vector : Index→ℝ) :
    vector ⬝ᵥ ((left • first+right • second)*ᵥ vector)=
      left*(vector ⬝ᵥ (first*ᵥ vector))+right*(vector ⬝ᵥ (second*ᵥ vector)) := by
  simp [Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul]

omit [DecidableEq Index] in
theorem actual_compatible_congruence_has_the_literal_quadratic_identity [Fintype Other]
    (matrix : Matrix Index Index ℝ) (map : Matrix Index Other ℝ) (vector : Other→ℝ) :
    vector ⬝ᵥ ((mapᵀ*matrix*map)*ᵥ vector)=
      (map*ᵥ vector) ⬝ᵥ (matrix*ᵥ (map*ᵥ vector)) := by
  conv_lhs => rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,dotProduct_mulVec,Matrix.vecMul_transpose]

omit [Fintype Index] [DecidableEq Index] in
theorem actual_real_loewner_order_is_the_source_psd_difference (first second : Matrix Index Index ℝ) :
    first ≤ second ↔ (second-first).PosSemidef := Iff.rfl

omit [DecidableEq Index] in
theorem actual_true_trace_of_a_transpose_gram_is_the_sum_of_all_squared_entries
    (factor : Matrix Index Index ℝ) :
    (factor*factorᵀ).trace=∑ row,∑ column,(factor row column)^2 := by
  simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,pow_two]

theorem actual_trace_pairing_equals_the_source_square_root_frobenius_energy
    (first second : Matrix Index Index ℝ) (hf : first.PosSemidef) (hs : second.PosSemidef) :
    (first*second).trace=
      ∑ row,∑ column,((actualPositiveSquareRoot first*actualPositiveSquareRoot second) row column)^2 := by
  obtain ⟨_,hft,hff⟩ := actual_positive_square_root_is_psd_symmetric_and_squares_to_the_matrix first hf
  obtain ⟨_,hst,hss⟩ := actual_positive_square_root_is_psd_symmetric_and_squares_to_the_matrix second hs
  rw [←actual_true_trace_of_a_transpose_gram_is_the_sum_of_all_squared_entries]
  conv_lhs => rw [←hff,←hss]
  calc
    _ = (actualPositiveSquareRoot first*(actualPositiveSquareRoot first*
        (actualPositiveSquareRoot second*actualPositiveSquareRoot second))).trace := by rw [Matrix.mul_assoc]
    _ = ((actualPositiveSquareRoot first*(actualPositiveSquareRoot second*actualPositiveSquareRoot second))*
        actualPositiveSquareRoot first).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.transpose_mul,hft,hst,Matrix.mul_assoc]

theorem actual_trace_pairing_is_the_square_root_congruence_trace
    (first second : Matrix Index Index ℝ) (hs : second.PosSemidef) :
    (first*second).trace=
      (actualPositiveSquareRoot second*first*actualPositiveSquareRoot second).trace := by
  obtain ⟨_,_,hss⟩ := actual_positive_square_root_is_psd_symmetric_and_squares_to_the_matrix second hs
  conv_lhs => rw [←hss,←Matrix.mul_assoc,Matrix.trace_mul_cycle]

end SafeLearning.CompleteModulesSDPConeCorollaries
