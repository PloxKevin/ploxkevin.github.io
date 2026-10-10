import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped MatrixOrder
namespace SafeLearning.CompleteModulesSDPCone

variable {Index Parameter Other : Type*} [Fintype Index] [DecidableEq Index]
  [Fintype Parameter]

def actualAffineMatrix (constant : Matrix Index Index ℝ)
    (coefficient : Parameter→Matrix Index Index ℝ) (unknown : Parameter→ℝ) : Matrix Index Index ℝ :=
  constant+∑ parameter,unknown parameter • coefficient parameter

def actualLMISet (constant : Matrix Index Index ℝ)
    (coefficient : Parameter→Matrix Index Index ℝ) : Set (Parameter→ℝ) :=
  {unknown | (actualAffineMatrix constant coefficient unknown).PosSemidef}

omit [Fintype Parameter] [DecidableEq Index] in
theorem actual_real_symmetric_psd_iff_all_quadratic_forms_nonnegative
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix.PosSemidef ↔ ∀ vector : Index→ℝ,0 ≤ vector ⬝ᵥ (matrix*ᵥ vector) := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec,hsymmetric,true_and,star_trivial]

omit [Fintype Parameter] in
theorem actual_real_symmetric_psd_iff_all_actual_eigenvalues_nonnegative
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix.PosSemidef ↔ ∀ index,0 ≤ hsymmetric.eigenvalues index := by
  exact hsymmetric.posSemidef_iff_eigenvalues_nonneg

omit [Fintype Parameter] in
theorem actual_real_symmetric_pd_iff_all_actual_eigenvalues_strictly_positive
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    matrix.PosDef ↔ ∀ index,0 < hsymmetric.eigenvalues index := by
  exact hsymmetric.posDef_iff_eigenvalues_pos

omit [Fintype Parameter] in
theorem actual_psd_iff_true_transpose_gram_factorization (matrix : Matrix Index Index ℝ) :
    matrix.PosSemidef ↔ ∃ factor : Matrix Index Index ℝ,matrix=factorᵀ*factor := by
  constructor
  · intro hmatrix
    obtain ⟨factor,hfactor⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hmatrix.nonneg
    exact ⟨factor,by simpa [Matrix.star_eq_conjTranspose] using hfactor⟩
  · rintro ⟨factor,rfl⟩
    simpa using Matrix.posSemidef_conjTranspose_mul_self factor

omit [Fintype Index] [Fintype Parameter] [DecidableEq Index] in
theorem actual_psd_cone_is_closed : IsClosed {matrix : Matrix Index Index ℝ | matrix.PosSemidef} :=
  Matrix.posSemidef_is_closed

omit [Fintype Index] [Fintype Parameter] [DecidableEq Index] in
theorem actual_nonnegative_combinations_of_psd_matrices_are_psd
    (first second : Matrix Index Index ℝ) (hf : first.PosSemidef) (hs : second.PosSemidef)
    (left right : ℝ) (hl : 0 ≤ left) (hr : 0 ≤ right) :
    (left • first+right • second).PosSemidef := (hf.smul hl).add (hs.smul hr)

omit [Fintype Index] [Fintype Parameter] [DecidableEq Index] in
theorem actual_psd_cone_is_convex : Convex ℝ {matrix : Matrix Index Index ℝ | matrix.PosSemidef} := by
  intro first hf second hs left right hl hr _
  exact actual_nonnegative_combinations_of_psd_matrices_are_psd first second hf hs left right hl hr

omit [Fintype Parameter] [DecidableEq Index] in
theorem actual_compatible_congruence_preserves_psd [Fintype Other]
    (matrix : Matrix Index Index ℝ) (hmatrix : matrix.PosSemidef) (map : Matrix Index Other ℝ) :
    (mapᵀ*matrix*map).PosSemidef := by
  simpa using hmatrix.conjTranspose_mul_mul_same map

omit [Fintype Parameter] in
theorem actual_invertible_square_congruence_preserves_and_reflects_psd
    (matrix map : Matrix Index Index ℝ) (hmap : IsUnit map) :
    (mapᵀ*matrix*map).PosSemidef ↔ matrix.PosSemidef := by
  simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using hmap.posSemidef_star_left_conjugate_iff (x:=matrix)

omit [Fintype Index] [DecidableEq Index] in
theorem actual_affine_matrix_is_genuinely_affine_in_every_unknown
    (constant : Matrix Index Index ℝ) (coefficient : Parameter→Matrix Index Index ℝ)
    (first second : Parameter→ℝ) (left right : ℝ) (hsum : left+right=1) :
    actualAffineMatrix constant coefficient (left • first+right • second)=
      left • actualAffineMatrix constant coefficient first+
        right • actualAffineMatrix constant coefficient second := by
  have hconstant : constant=left • constant+right • constant := by rw [←add_smul,hsum,one_smul]
  unfold actualAffineMatrix
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_smul,mul_smul,Finset.sum_add_distrib,
    ←Finset.smul_sum,smul_add]
  nth_rw 1 [hconstant]
  abel

omit [Fintype Index] [DecidableEq Index] in
theorem actual_lmi_feasible_set_is_convex
    (constant : Matrix Index Index ℝ) (coefficient : Parameter→Matrix Index Index ℝ) :
    Convex ℝ (actualLMISet constant coefficient) := by
  intro first hf second hs left right hl hr hsum
  change (actualAffineMatrix constant coefficient (left • first+right • second)).PosSemidef
  rw [actual_affine_matrix_is_genuinely_affine_in_every_unknown _ _ _ _ _ _ hsum]
  exact actual_nonnegative_combinations_of_psd_matrices_are_psd _ _ hf hs left right hl hr

omit [Fintype Index] [DecidableEq Index] in
theorem actual_sdp_linear_objective_is_convex_on_its_true_lmi_set
    (constant : Matrix Index Index ℝ) (coefficient : Parameter→Matrix Index Index ℝ)
    (cost : Parameter→ℝ) :
    ConvexOn ℝ (actualLMISet constant coefficient) (fun unknown => cost ⬝ᵥ unknown) := by
  refine ⟨actual_lmi_feasible_set_is_convex constant coefficient,?_⟩
  intro first _ second _ left right _ _ _
  simp [dotProduct_add,dotProduct_smul]

end SafeLearning.CompleteModulesSDPCone
