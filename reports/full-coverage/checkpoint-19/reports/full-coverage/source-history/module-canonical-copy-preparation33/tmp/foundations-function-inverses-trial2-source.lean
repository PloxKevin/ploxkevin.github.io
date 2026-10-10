import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteFoundationsFunctionInverses

theorem actual_injective_surjective_and_bijective_definitions
    {X Y : Type*} (f : X → Y) :
    (Function.Injective f ↔ ∀ x x', f x = f x' → x = x') ∧
      (Function.Surjective f ↔ ∀ y, ∃ x, f x = y) ∧
      (Function.Bijective f ↔ Function.Injective f ∧ Function.Surjective f) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem actual_bijection_iff_a_genuine_two_sided_function_inverse_exists
    {X Y : Type*} (f : X → Y) :
    Function.Bijective f ↔ ∃ inverse : Y → X,
      (∀ x, inverse (f x) = x) ∧ (∀ y, f (inverse y) = y) :=
  Function.bijective_iff_has_inverse

theorem actual_preimages_exist_for_every_function_without_an_inverse
    {X Y : Type*} (f : X → Y) (B : Set Y) (x : X) :
    x ∈ f ⁻¹' B ↔ f x ∈ B := Iff.rfl

theorem actual_affine_source_function_has_its_literal_inverse :
    Function.Bijective (fun x : ℝ => 2*x+1) ∧
      (∀ x : ℝ, ((2*x+1)-1)/2=x) ∧
      (∀ y : ℝ, 2*((y-1)/2)+1=y) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro x y h; linarith
    · intro y; exact ⟨(y-1)/2, by ring⟩
  · intro x; ring
  · intro y; ring

theorem actual_square_function_is_neither_injective_nor_surjective_on_all_reals :
    ¬ Function.Injective (fun x : ℝ => x^2) ∧
      ¬ Function.Surjective (fun x : ℝ => x^2) := by
  constructor
  · intro h
    have hh := h (a₁ := -1) (a₂ := 1) (by norm_num)
    norm_num at hh
  · intro h
    obtain ⟨x,hx⟩ := h (-1)
    nlinarith [sq_nonneg x]

abbrev Nonnegative := {x : ℝ // 0 ≤ x}
def nonnegativeSquare (x : Nonnegative) : Nonnegative := ⟨x.val^2, sq_nonneg x.val⟩
def nonnegativeSquareRoot (x : Nonnegative) : Nonnegative :=
  ⟨Real.sqrt x.val, Real.sqrt_nonneg _⟩

theorem actual_nonnegative_square_and_square_root_are_two_sided_inverses :
    Function.LeftInverse nonnegativeSquareRoot nonnegativeSquare ∧
      Function.RightInverse nonnegativeSquareRoot nonnegativeSquare := by
  constructor
  · intro x; apply Subtype.ext; exact Real.sqrt_sq x.property
  · intro x; apply Subtype.ext; exact Real.sq_sqrt x.property

theorem actual_square_on_the_nonnegative_domain_is_bijective :
    Function.Bijective nonnegativeSquare :=
  actual_bijection_iff_a_genuine_two_sided_function_inverse_exists _ |>.mpr
    ⟨nonnegativeSquareRoot, actual_nonnegative_square_and_square_root_are_two_sided_inverses⟩

theorem actual_strictly_increasing_functions_are_injective
    {X Y : Type*} [LinearOrder X] [Preorder Y]
    (f : X → Y) (hf : StrictMono f) : Function.Injective f := hf.injective

theorem actual_bijective_rectangular_real_matrix_forces_equal_dimensions
    (rows columns : ℕ) (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hA : Function.Bijective A.mulVec) : rows = columns := by
  have hdim := (LinearEquiv.ofBijective A.mulVecLin hA).finrank_eq
  simpa using hdim.symm

theorem actual_square_real_matrix_map_is_bijective_iff_matrix_is_invertible
    (dimension : ℕ) (A : Matrix (Fin dimension) (Fin dimension) ℝ) :
    Function.Bijective A.mulVec ↔ IsUnit A := by
  constructor
  · intro h; exact Matrix.mulVec_surjective_iff_isUnit.mp h.2
  · intro h
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr h,
      Matrix.mulVec_surjective_iff_isUnit.mpr h⟩

theorem actual_invertible_matrix_function_has_the_actual_inverse_matrix_function
    (dimension : ℕ) (A : Matrix (Fin dimension) (Fin dimension) ℝ) (hA : IsUnit A) :
    (∀ x, A⁻¹.mulVec (A.mulVec x) = x) ∧
      (∀ y, A.mulVec (A⁻¹.mulVec y) = y) := by
  have hdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA
  constructor
  · intro x
    rw [Matrix.mulVec_mulVec, A.nonsing_inv_mul hdet, Matrix.one_mulVec]
  · intro y
    rw [Matrix.mulVec_mulVec, A.mul_nonsing_inv hdet, Matrix.one_mulVec]

end SafeLearning.CompleteFoundationsFunctionInverses
