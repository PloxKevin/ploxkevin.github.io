import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Matrix BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteFoundationsSkew30

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem actual_skew_definition_entrywise_iff (A : Matrix n n ℝ) :
    A.transpose = -A ↔ ∀ i j, A j i = -A i j := by
  constructor
  · intro h i j
    exact congrFun (congrFun h i) j
  · intro h
    ext i j
    exact h i j

-- Elementary transpose argument, read in full in the selected SpectralModels source.
omit [DecidableEq n] in
theorem actual_skew_quadratic_zero
    (A : Matrix n n ℝ) (hA : A.transpose = -A) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = 0 := by
  have ht : x ⬝ᵥ (A.transpose *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.transpose_transpose, dotProduct_comm]
  rw [hA, Matrix.neg_mulVec, dotProduct_neg] at ht
  linarith

theorem actual_skew_one_add_quadratic_euclidean_norm
    (A : Matrix n n ℝ) (hA : A.transpose = -A)
    (x : EuclideanSpace ℝ n) :
    x.ofLp ⬝ᵥ ((1+A) *ᵥ x.ofLp) = ‖x‖^2 := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
    actual_skew_quadratic_zero A hA, add_zero, EuclideanSpace.norm_sq_eq]
  simp [dotProduct, Real.norm_eq_abs, pow_two]

-- Elementary injectivity argument, read in full in selected StructuredModels.
theorem actual_skew_one_add_is_invertible
    (A : Matrix n n ℝ) (hA : A.transpose = -A) : IsUnit (1+A) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  have hz : (1+A) *ᵥ (x-y) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
  have hh := congrArg (fun w : n → ℝ => (x-y) ⬝ᵥ w) hz
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
    actual_skew_quadratic_zero A hA (x-y), dotProduct_zero, add_zero] at hh
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hh)

theorem actual_real_skew_complexification_transpose
    (A : Matrix n n ℝ) (hA : A.transpose = -A) :
    (A.map (algebraMap ℝ ℂ)).transpose = -(A.map (algebraMap ℝ ℂ)) := by
  ext i j
  have h := congrFun (congrFun hA i) j
  change A j i = -A i j at h
  change (A j i : ℂ) = -(A i j : ℂ)
  exact_mod_cast h

theorem actual_real_skew_complexification_star
    (A : Matrix n n ℝ) (hA : A.transpose = -A) :
    star (A.map (algebraMap ℝ ℂ)) = -(A.map (algebraMap ℝ ℂ)) := by
  rw [Matrix.star_eq_conjTranspose]
  have ht := actual_real_skew_complexification_transpose A hA
  ext i j
  simpa [Matrix.conjTranspose_apply] using congrFun (congrFun ht i) j

theorem actual_real_skew_eigenvalues_have_zero_real_part
    (A : Matrix n n ℝ) (hA : A.transpose = -A) (z : ℂ)
    (hz : z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) : z.re = 0 := by
  let C : Matrix n n ℂ := A.map (algebraMap ℝ ℂ)
  have hs : star C = -C := actual_real_skew_complexification_star A hA
  have hi : IsSelfAdjoint (Complex.I • C) := by
    rw [isSelfAdjoint_iff, star_smul, hs]
    simp
  let u : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  have hm : Complex.I*z ∈ spectrum ℂ (Complex.I • C) := by
    simpa only [u, C, Units.smul_def, Units.val_mk0, smul_eq_mul] using
      (spectrum.smul_mem_smul_iff (r := u)).mpr hz
  simpa using hi.im_eq_zero_of_mem_spectrum hm

theorem actual_real_skew_spectrum_closed_under_negation
    (A : Matrix n n ℝ) (hA : A.transpose = -A) (z : ℂ) :
    z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) ↔
      -z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
  let C : Matrix n n ℂ := A.map (algebraMap ℝ ℂ)
  have ht : C.transpose = -C := actual_real_skew_complexification_transpose A hA
  have he : spectrum ℂ (-C) = spectrum ℂ C := by
    rw [← ht, Matrix.spectrum_transpose]
  have hn := spectrum.neg_eq (R := ℂ) C
  rw [he] at hn
  change z ∈ spectrum ℂ C ↔ -z ∈ spectrum ℂ C
  have hm := Set.ext_iff.mp hn (-z)
  simpa using hm

theorem actual_real_skew_eigenvalues_zero_or_positive_imaginary_pair
    (A : Matrix n n ℝ) (hA : A.transpose = -A) (z : ℂ)
    (hz : z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) :
    z = 0 ∨ ∃ ω : ℝ, 0 < ω ∧
      (z = (ω : ℂ)*Complex.I ∨ z = -((ω : ℂ)*Complex.I)) := by
  have hr := actual_real_skew_eigenvalues_have_zero_real_part A hA z hz
  have he : z = (z.im : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [hr]
  rcases lt_trichotomy 0 z.im with hp | heq | hn
  · exact Or.inr ⟨z.im, hp, Or.inl he⟩
  · left
    rw [he, ← heq]
    simp
  · right
    refine ⟨-z.im, neg_pos.mpr hn, Or.inr ?_⟩
    rw [he]
    simp

omit [Fintype n] [DecidableEq n] in
theorem actual_symmetric_skew_half_decomposition (M : Matrix n n ℝ) :
    M = (1/2 : ℝ) • (M+M.transpose) + (1/2 : ℝ) • (M-M.transpose) ∧
    ((1/2 : ℝ) • (M+M.transpose)).transpose = (1/2 : ℝ) • (M+M.transpose) ∧
    ((1/2 : ℝ) • (M-M.transpose)).transpose = -((1/2 : ℝ) • (M-M.transpose)) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.transpose_apply] <;> ring

omit [Fintype n] [DecidableEq n] in
theorem actual_arbitrary_matrix_skew_parametrization (W : Matrix n n ℝ) :
    (W-W.transpose).transpose = -(W-W.transpose) := by
  rw [Matrix.transpose_sub, Matrix.transpose_transpose]
  ext i j
  simp

omit [Fintype n] [DecidableEq n] in
theorem actual_every_skew_matrix_has_free_parametrization
    (A : Matrix n n ℝ) (hA : A.transpose = -A) :
    ∃ W : Matrix n n ℝ, A = W-W.transpose := by
  refine ⟨(1/2 : ℝ) • A, ?_⟩
  rw [Matrix.transpose_smul, hA]
  ext i j
  simp
  ring

end SafeLearning.CompleteFoundationsSkew30
