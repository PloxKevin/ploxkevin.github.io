import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix RealInnerProductSpace

namespace SafeLearning.CompleteFoundationsRayleighQuotientWhole30

section Coordinates
variable {n : Type*} [Fintype n] [DecidableEq n]

def actualCoordinates (A : Matrix n n ℝ) (hA : A.IsHermitian) (x : n → ℝ) : n → ℝ :=
  fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ x

private theorem actual_outer_sum (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A = ∑ j, hA.eigenvalues j • Matrix.vecMulVec
      (hA.eigenvectorBasis j : n → ℝ) (hA.eigenvectorBasis j : n → ℝ) := by
  calc
    A = (hA.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues *
        (hA.eigenvectorUnitary : Matrix n n ℝ).transpose := by
      simpa only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def,
        RCLike.ofReal_real_eq_id,id_eq] using hA.spectral_theorem
    _ = _ := by
      ext i k
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply,Matrix.sum_apply,
        Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hA.eigenvectorUnitary_apply,hA.eigenvectorUnitary_apply]
      ring

theorem actual_spectral_coordinates_are_transpose_times_vector
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (x : n → ℝ) :
    actualCoordinates A hA x = (hA.eigenvectorUnitary : Matrix n n ℝ).transpose *ᵥ x := by
  ext i
  rfl

theorem actual_spectral_coordinates_preserve_Euclidean_energy
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (x : n → ℝ) :
    ∑ i, actualCoordinates A hA x i ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
  have h := hA.eigenvectorBasis.sum_sq_inner_right (WithLp.toLp 2 x)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,
    star_trivial,dotProduct_comm,actualCoordinates] using h

theorem actual_quadratic_form_is_eigenvalue_weighted_coordinate_energy
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i * actualCoordinates A hA x i ^ 2 := by
  nth_rw 1 [actual_outer_sum A hA]
  simp only [Matrix.sum_mulVec,dotProduct_sum,Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec,op_smul_eq_smul,dotProduct_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dotProduct_comm x (hA.eigenvectorBasis i : n → ℝ)]
  dsimp [actualCoordinates]
  ring

theorem actual_spectral_coordinates_preserve_the_Euclidean_norm
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (x : n → ℝ) :
    ‖WithLp.toLp 2 (actualCoordinates A hA x)‖ = ‖WithLp.toLp 2 x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  exact actual_spectral_coordinates_preserve_Euclidean_energy A hA x

theorem actual_quadratic_form_at_any_eigenvector
    (A : Matrix n n ℝ) (q : n → ℝ) (a : ℝ) (hq : A *ᵥ q = a • q) :
    q ⬝ᵥ (A *ᵥ q) = a * ‖WithLp.toLp 2 q‖ ^ 2 := by
  rw [hq,dotProduct_smul,smul_eq_mul,EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct,pow_two]

end Coordinates

section Extrema
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def actualLambdaMax (A : Matrix n n ℝ) (hA : A.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues
def actualLambdaMin (A : Matrix n n ℝ) (hA : A.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues

theorem actual_all_eigenvalues_are_between_the_extremes
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (i : n) :
    actualLambdaMin A hA ≤ hA.eigenvalues i ∧
      hA.eigenvalues i ≤ actualLambdaMax A hA := by
  exact ⟨Finset.inf'_le hA.eigenvalues (Finset.mem_univ i),
    Finset.le_sup' hA.eigenvalues (Finset.mem_univ i)⟩

theorem actual_Euclidean_quadratic_form_is_squeezed_by_extreme_eigenvalues
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (x : n → ℝ) :
    actualLambdaMin A hA * ‖WithLp.toLp 2 x‖ ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) ∧
      x ⬝ᵥ (A *ᵥ x) ≤ actualLambdaMax A hA * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [actual_quadratic_form_is_eigenvalue_weighted_coordinate_energy A hA x,
    ← actual_spectral_coordinates_preserve_Euclidean_energy A hA x]
  simp only [Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (actual_all_eigenvalues_are_between_the_extremes A hA i).1 (sq_nonneg _)
  · apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (actual_all_eigenvalues_are_between_the_extremes A hA i).2 (sq_nonneg _)

theorem actual_unit_eigenvector_attains_largest_eigenvalue
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    ∃ q : n → ℝ, ‖WithLp.toLp 2 q‖ = 1 ∧
      A *ᵥ q = actualLambdaMax A hA • q ∧
      q ⬝ᵥ (A *ᵥ q) = actualLambdaMax A hA := by
  obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hA.eigenvalues
  change actualLambdaMax A hA = hA.eigenvalues i at hmax
  refine ⟨(hA.eigenvectorBasis i : n → ℝ),?_,?_,?_⟩
  · exact hA.eigenvectorBasis.orthonormal.1 i
  · rw [hmax]
    exact hA.mulVec_eigenvectorBasis i
  · have h := (hA.eigenvalues_eq i).symm
    simpa only [RCLike.re_to_real,star_trivial,hmax] using h

theorem actual_unit_eigenvector_attains_smallest_eigenvalue
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    ∃ q : n → ℝ, ‖WithLp.toLp 2 q‖ = 1 ∧
      A *ᵥ q = actualLambdaMin A hA • q ∧
      q ⬝ᵥ (A *ᵥ q) = actualLambdaMin A hA := by
  obtain ⟨i,hi,hmin⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hA.eigenvalues
  change actualLambdaMin A hA = hA.eigenvalues i at hmin
  refine ⟨(hA.eigenvectorBasis i : n → ℝ),?_,?_,?_⟩
  · exact hA.eigenvectorBasis.orthonormal.1 i
  · rw [hmin]
    exact hA.mulVec_eigenvectorBasis i
  · have h := (hA.eigenvalues_eq i).symm
    simpa only [RCLike.re_to_real,star_trivial,hmin] using h

theorem actual_largest_eigenvalue_is_greatest_unit_quadratic_form
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    IsGreatest {r : ℝ | ∃ x : n → ℝ, ‖WithLp.toLp 2 x‖ = 1 ∧ r = x ⬝ᵥ (A *ᵥ x)}
      (actualLambdaMax A hA) := by
  obtain ⟨q,hq,he,hvalue⟩ := actual_unit_eigenvector_attains_largest_eigenvalue A hA
  refine ⟨⟨q,hq,hvalue.symm⟩,?_⟩
  rintro r ⟨x,hx,rfl⟩
  simpa only [hx,one_pow,mul_one] using
    (actual_Euclidean_quadratic_form_is_squeezed_by_extreme_eigenvalues A hA x).2

theorem actual_smallest_eigenvalue_is_least_unit_quadratic_form
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    IsLeast {r : ℝ | ∃ x : n → ℝ, ‖WithLp.toLp 2 x‖ = 1 ∧ r = x ⬝ᵥ (A *ᵥ x)}
      (actualLambdaMin A hA) := by
  obtain ⟨q,hq,he,hvalue⟩ := actual_unit_eigenvector_attains_smallest_eigenvalue A hA
  refine ⟨⟨q,hq,hvalue.symm⟩,?_⟩
  rintro r ⟨x,hx,rfl⟩
  simpa only [hx,one_pow,mul_one] using
    (actual_Euclidean_quadratic_form_is_squeezed_by_extreme_eigenvalues A hA x).1

end Extrema

section Example
def actualPrintedA : Matrix (Fin 2) (Fin 2) ℝ := !![2,1;1,2]
def actualPrintedQPlus : Fin 2 → ℝ := ![1/Real.sqrt 2,1/Real.sqrt 2]
def actualPrintedQMinus : Fin 2 → ℝ := ![1/Real.sqrt 2,-1/Real.sqrt 2]

theorem actual_printed_symmetric_matrix_all_eigenvalues :
    actualPrintedA.IsHermitian ∧
      ∀ r : ℝ, r ∈ spectrum ℝ actualPrintedA ↔ r = 3 ∨ r = 1 := by
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [actualPrintedA]
  · intro r
    have hc : actualPrintedA.charpoly = (Polynomial.X-3)*(Polynomial.X-1) := by
      rw [Matrix.charpoly_fin_two]
      norm_num [actualPrintedA,Matrix.trace,Matrix.det_fin_two,Fin.sum_univ_two,
        Polynomial.C_ofNat] <;> ring
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,hc]
    simp [Polynomial.IsRoot,mul_eq_zero,sub_eq_zero]

theorem actual_printed_two_perpendicular_unit_eigenvectors :
    ‖WithLp.toLp 2 actualPrintedQPlus‖ = 1 ∧
    ‖WithLp.toLp 2 actualPrintedQMinus‖ = 1 ∧
    actualPrintedQPlus ⬝ᵥ actualPrintedQMinus = 0 ∧
    actualPrintedA *ᵥ actualPrintedQPlus = (3:ℝ) • actualPrintedQPlus ∧
    actualPrintedA *ᵥ actualPrintedQMinus = (1:ℝ) • actualPrintedQMinus := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hrec : (1/Real.sqrt 2 : ℝ)^2 = 1/2 := by rw [div_pow,one_pow,hs]
  simp only [one_div] at hrec
  have hp : ‖WithLp.toLp 2 actualPrintedQPlus‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [actualPrintedQPlus,Fin.sum_univ_two,one_div,hrec]
  have hm : ‖WithLp.toLp 2 actualPrintedQMinus‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [actualPrintedQMinus,Fin.sum_univ_two,neg_div,one_div,neg_sq,hrec]
  refine ⟨?_,?_,?_,?_,?_⟩
  · nlinarith [norm_nonneg (WithLp.toLp 2 actualPrintedQPlus)]
  · nlinarith [norm_nonneg (WithLp.toLp 2 actualPrintedQMinus)]
  · simp [actualPrintedQPlus,actualPrintedQMinus,dotProduct,Fin.sum_univ_two,neg_div]
  · ext i
    fin_cases i <;> simp [actualPrintedA,actualPrintedQPlus,Matrix.mulVec,
      dotProduct,Fin.sum_univ_two] <;> ring
  · ext i
    fin_cases i <;> simp [actualPrintedA,actualPrintedQMinus,Matrix.mulVec,
      dotProduct,Fin.sum_univ_two] <;> ring

theorem actual_printed_rank_one_decomposition :
    actualPrintedA = (3:ℝ) • Matrix.vecMulVec actualPrintedQPlus actualPrintedQPlus +
      Matrix.vecMulVec actualPrintedQMinus actualPrintedQMinus := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hrec : (1/Real.sqrt 2 : ℝ)^2 = 1/2 := by rw [div_pow,one_pow,hs]
  simp only [one_div] at hrec
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actualPrintedA,actualPrintedQPlus,actualPrintedQMinus,Matrix.vecMulVec,neg_div]
    <;> nlinarith [hrec]

theorem actual_printed_rank_one_matrices_are_the_displayed_half_matrices :
    (3:ℝ) • Matrix.vecMulVec actualPrintedQPlus actualPrintedQPlus =
      (3/2:ℝ) • (!![1,1;1,1] : Matrix (Fin 2) (Fin 2) ℝ) ∧
    Matrix.vecMulVec actualPrintedQMinus actualPrintedQMinus =
      (1/2:ℝ) • (!![1,-1;-1,1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hrec : (1/Real.sqrt 2 : ℝ)^2 = 1/2 := by rw [div_pow,one_pow,hs]
  simp only [one_div] at hrec
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [actualPrintedQPlus,actualPrintedQMinus,Matrix.vecMulVec,neg_div] <;>
    nlinarith [hrec]

theorem actual_printed_quadratic_form_values_and_global_bounds (x : Fin 2 → ℝ) :
    (![(1:ℝ),0]) ⬝ᵥ (actualPrintedA *ᵥ ![1,0]) = 2 ∧
    actualPrintedQPlus ⬝ᵥ (actualPrintedA *ᵥ actualPrintedQPlus) = 3 ∧
    actualPrintedQMinus ⬝ᵥ (actualPrintedA *ᵥ actualPrintedQMinus) = 1 ∧
    ‖WithLp.toLp 2 x‖^2 ≤ x ⬝ᵥ (actualPrintedA *ᵥ x) ∧
    x ⬝ᵥ (actualPrintedA *ᵥ x) ≤ 3*‖WithLp.toLp 2 x‖^2 := by
  obtain ⟨hp,hm,ho,hep,hem⟩ := actual_printed_two_perpendicular_unit_eigenvectors
  refine ⟨?_,?_,?_,?_,?_⟩
  · norm_num [actualPrintedA,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · rw [actual_quadratic_form_at_any_eigenvector actualPrintedA _ 3 hep,hp]
    norm_num
  · rw [actual_quadratic_form_at_any_eigenvector actualPrintedA _ 1 hem,hm]
    norm_num
  · simp [EuclideanSpace.real_norm_sq_eq,actualPrintedA,Matrix.mulVec,dotProduct,
      Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0+x 1)]
  · simp [EuclideanSpace.real_norm_sq_eq,actualPrintedA,Matrix.mulVec,dotProduct,
      Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0-x 1)]

end Example

theorem actual_zero_dimensional_Euclidean_unit_sphere_is_empty :
    {x : Fin 0 → ℝ | ‖WithLp.toLp 2 x‖ = 1} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxzero : x = 0 := by
    ext i
    exact Fin.elim0 i
  simp only [Set.mem_setOf_eq,hxzero,WithLp.toLp_zero,norm_zero] at hx
  norm_num at hx

theorem actual_zero_dimensional_quadratic_values_have_no_attained_maximum
    (A : Matrix (Fin 0) (Fin 0) ℝ) (r : ℝ) :
    ¬ IsGreatest {z : ℝ | ∃ x : Fin 0 → ℝ, ‖WithLp.toLp 2 x‖ = 1 ∧
      z = x ⬝ᵥ (A *ᵥ x)} r := by
  rintro ⟨⟨x,hx,hr⟩,hb⟩
  have he := actual_zero_dimensional_Euclidean_unit_sphere_is_empty
  have hm : x ∈ {x : Fin 0 → ℝ | ‖WithLp.toLp 2 x‖ = 1} := hx
  rw [he] at hm
  exact hm

end SafeLearning.CompleteFoundationsRayleighQuotientWhole30
