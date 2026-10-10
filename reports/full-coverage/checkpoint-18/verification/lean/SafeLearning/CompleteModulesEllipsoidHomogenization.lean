import SafeLearning.CompleteModulesEllipsoidSProcedure

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped Matrix
open SafeLearning.CompleteModulesEllipsoidSpectral
open SafeLearning.CompleteModulesEllipsoidSProcedure
namespace SafeLearning.CompleteModulesEllipsoidHomogenization

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

def actualHomogenizedMatrix (matrix : Matrix Index Index ℝ) (constant : ℝ) :
    Matrix (Index ⊕ Fin 1) (Index ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks matrix 0 0 (!![constant])

omit [DecidableEq Index] in
theorem actual_homogenized_quadratic_identity (matrix : Matrix Index Index ℝ)
    (constant : ℝ) (vector : Index ⊕ Fin 1 → ℝ) :
    quadraticValue (actualHomogenizedMatrix matrix constant) vector=
      quadraticValue matrix (vector ∘ Sum.inl)+constant*(vector (Sum.inr 0))^2 := by
  have hv : vector=Sum.elim (vector ∘ Sum.inl) (vector ∘ Sum.inr) := by
    ext index
    cases index <;> rfl
  unfold quadraticValue
  conv_lhs => rw [hv]
  simp [actualHomogenizedMatrix,Matrix.mulVec,dotProduct,pow_two]
  ring

omit [DecidableEq Index] in
theorem actual_homogenized_matrix_psd_iff_the_literal_two_conditions
    (matrix : Matrix Index Index ℝ) (constant : ℝ) :
    (actualHomogenizedMatrix matrix constant).PosSemidef ↔ matrix.PosSemidef ∧ 0 ≤ constant := by
  constructor
  · intro h
    have hsub := h.submatrix (Sum.inl : Index → Index ⊕ Fin 1)
    have he : (actualHomogenizedMatrix matrix constant).submatrix Sum.inl Sum.inl=matrix := by
      ext row column
      rfl
    rw [he] at hsub
    refine ⟨hsub,?_⟩
    have hq := h.dotProduct_mulVec_nonneg (Sum.elim (0 : Index → ℝ) (fun _ : Fin 1 => 1))
    simp only [star_trivial] at hq
    change 0 ≤ quadraticValue (actualHomogenizedMatrix matrix constant) _ at hq
    rw [actual_homogenized_quadratic_identity] at hq
    simpa [quadraticValue] using hq
  · rintro ⟨hpsd,hconstant⟩
    have hs : (!![constant] : Matrix (Fin 1) (Fin 1) ℝ).IsHermitian := by
      ext row column
      fin_cases row;fin_cases column;rfl
    have hh : (actualHomogenizedMatrix matrix constant).IsHermitian :=
      hpsd.isHermitian.fromBlocks (by simp) hs
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
    intro vector
    simp only [star_trivial]
    change 0 ≤ quadraticValue (actualHomogenizedMatrix matrix constant) vector
    rw [actual_homogenized_quadratic_identity]
    have hq := hpsd.dotProduct_mulVec_nonneg (vector ∘ Sum.inl)
    simp only [star_trivial] at hq
    exact add_nonneg hq (mul_nonneg hconstant (sq_nonneg _))

omit [DecidableEq Index] in
theorem actual_s_procedure_global_residual_iff_the_source_homogenized_block_psd
    (storage matrix : Matrix Index Index ℝ) (hstorage : storage.IsHermitian)
    (hmatrix : matrix.IsHermitian) (bound multiplier : ℝ) :
    (∀ vector : Index → ℝ,0 ≤ actualSProcedureResidual storage matrix bound multiplier vector) ↔
      (actualHomogenizedMatrix (multiplier • storage-matrix) (bound-multiplier)).PosSemidef := by
  rw [actual_s_procedure_residual_is_globally_nonnegative_iff_literal_matrix_conditions
    storage matrix hstorage hmatrix bound multiplier,
    actual_homogenized_matrix_psd_iff_the_literal_two_conditions,sub_nonneg]
  exact and_comm

end SafeLearning.CompleteModulesEllipsoidHomogenization
