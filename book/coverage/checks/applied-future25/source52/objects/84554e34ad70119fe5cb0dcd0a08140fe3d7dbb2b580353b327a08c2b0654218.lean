import SafeLearning.CompleteModulesLipSDPWalkthrough

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesLipSDPPracticeNumericalMargin21
open CompleteModulesLipSDP CompleteModulesLipSDPProduct

def family (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-1,a;a,-1]
def firstMatrix := family (11/10)
def secondMatrix := family (9/10)

theorem actual_family_is_symmetric_and_has_the_printed_eigenvectors (a : ℝ) :
    (family a).IsHermitian ∧
      family a *ᵥ (![1,1] : Fin 2 → ℝ) = (-1+a) • ![1,1] ∧
      family a *ᵥ (![1,-1] : Fin 2 → ℝ) = (-1-a) • ![1,-1] := by
  refine ⟨?_,?_,?_⟩
  · ext i j;fin_cases i <;> fin_cases j <;> simp [family,Matrix.conjTranspose_apply]
  · ext i;fin_cases i <;> simp [family,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;> ring
  · ext i;fin_cases i <;> simp [family,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;> ring

theorem actual_family_full_official_spectrum (a value : ℝ) :
    value ∈ spectrum ℝ (family a) ↔ value=-1+a ∨ value=-1-a := by
  have hc : (family a).charpoly=(X-C (-1+a))*(X-C (-1-a)) := by
    rw [Matrix.charpoly_fin_two]
    simp [family,Matrix.trace,Matrix.det_fin_two,Fin.sum_univ_two,
      map_sub,map_add,map_mul,map_neg]
    ring
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,hc]
  simp [mul_eq_zero,sub_eq_zero]

theorem actual_both_source_matrices_have_exact_full_spectra (value : ℝ) :
    (value ∈ spectrum ℝ firstMatrix ↔ value=1/10 ∨ value= -21/10) ∧
      (value ∈ spectrum ℝ secondMatrix ↔ value= -1/10 ∨ value= -19/10) := by
  constructor
  · unfold firstMatrix
    rw [actual_family_full_official_spectrum]
    norm_num
  · unfold secondMatrix
    rw [actual_family_full_official_spectrum]
    norm_num

theorem actual_first_source_matrix_is_not_negative_semidefinite :
    ¬ (-firstMatrix).PosSemidef := by
  intro h
  have hn := h.dotProduct_mulVec_nonneg (![1,1] : Fin 2 → ℝ)
  norm_num [firstMatrix,family,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hn

theorem actual_second_matrix_every_vector_energy_margin (x : Fin 2 → ℝ) :
    quadratic secondMatrix x =
      -(1/10:ℝ)*‖WithLp.toLp 2 x‖^2-(9/10:ℝ)*(x 0-x 1)^2 := by
  rw [squared_norm_of_coordinates]
  simp [quadratic,secondMatrix,family,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_second_source_matrix_is_negative_semidefinite :
    (-secondMatrix).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (actual_family_is_symmetric_and_has_the_printed_eigenvectors (9/10)).1.neg
  intro x
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg]
  change 0 ≤ -quadratic secondMatrix x
  rw [actual_second_matrix_every_vector_energy_margin]
  nlinarith [sq_nonneg ‖WithLp.toLp 2 x‖,sq_nonneg (x 0-x 1)]

theorem actual_arbitrary_perturbation_quadratic_is_bounded_by_its_operator_norm
    (E : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    |quadratic E x| ≤ ‖E‖*‖WithLp.toLp 2 x‖^2 := by
  have hi := abs_real_inner_le_norm (WithLp.toLp 2 x)
    (WithLp.toLp 2 (E *ᵥ x))
  have he : |quadratic E x| ≤ ‖WithLp.toLp 2 x‖*‖WithLp.toLp 2 (E *ᵥ x)‖ := by
    simpa [quadratic,PiLp.inner_apply,RCLike.inner_apply,dotProduct,mul_comm] using hi
  have hg := actual_spectral_matrix_gain E x
  calc
    _ ≤ ‖WithLp.toLp 2 x‖*‖WithLp.toLp 2 (E *ᵥ x)‖ := he
    _ ≤ ‖WithLp.toLp 2 x‖*(‖E‖*‖WithLp.toLp 2 x‖) :=
      mul_le_mul_of_nonneg_left hg (norm_nonneg _)
    _ = _ := by ring

theorem actual_every_proven_source_perturbation_preserves_the_strict_margin
    (E : Matrix (Fin 2) (Fin 2) ℝ) (hE : ‖E‖ ≤ 1/25) (x : Fin 2 → ℝ) :
    quadratic (secondMatrix+E) x ≤ -(3/50:ℝ)*‖WithLp.toLp 2 x‖^2 := by
  have he := actual_arbitrary_perturbation_quadratic_is_bounded_by_its_operator_norm E x
  have hb := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖WithLp.toLp 2 x‖)
  rw [quadratic_add,actual_second_matrix_every_vector_energy_margin]
  nlinarith [le_abs_self (quadratic E x),sq_nonneg (x 0-x 1)]

theorem actual_symmetric_source_perturbation_is_strictly_negative_definite
    (E : Matrix (Fin 2) (Fin 2) ℝ) (hsym : E.IsHermitian) (hE : ‖E‖ ≤ 1/25) :
    (-(secondMatrix+E)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (((actual_family_is_symmetric_and_has_the_printed_eigenvectors (9/10)).1.add hsym).neg)
  intro x hx
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg]
  change 0 < -quadratic (secondMatrix+E) x
  have hn : WithLp.toLp 2 x ≠ (0 : EuclideanSpace ℝ (Fin 2)) := by
    intro hz
    apply hx
    simpa using congrArg (WithLp.ofLp) hz
  have hp : 0 < ‖WithLp.toLp 2 x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hb := actual_every_proven_source_perturbation_preserves_the_strict_margin E hE x
  nlinarith

end SafeLearning.CompleteModulesLipSDPPracticeNumericalMargin21
