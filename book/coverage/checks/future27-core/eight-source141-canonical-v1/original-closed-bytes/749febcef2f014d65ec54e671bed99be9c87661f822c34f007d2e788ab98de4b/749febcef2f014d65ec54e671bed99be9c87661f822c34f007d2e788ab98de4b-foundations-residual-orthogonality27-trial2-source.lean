import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Matrix

namespace SafeLearning.CompleteFoundationsResidualOrthogonality27

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

def loss (A : V →L[ℝ] W) (y : W) (x : V) : ℝ := ‖A x-y‖^2

theorem actual_residual_two_sided_perturbation_expansion
    (A : V →L[ℝ] W) (y : W) (x v : V) (t : ℝ) :
    loss A y (x+t • v) = loss A y x +
      2*t*inner ℝ (A x-y) (A v)+t^2*‖A v‖^2 := by
  have he : A (x+t • v)-y = (A x-y)+t • A v := by
    rw [map_add,map_smul]
    abel
  rw [loss,he,norm_add_sq_real]
  simp only [real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,loss]
  ring

theorem actual_global_minimum_forces_every_residual_inner_product_zero
    (A : V →L[ℝ] W) (y : W) (x : V)
    (hmin : ∀z : V,loss A y x ≤ loss A y z) (v : V) :
    inner ℝ (A x-y) (A v) = 0 := by
  have hq : ∀t : ℝ,0 ≤ ‖A v‖^2*(t*t)+
      (2*inner ℝ (A x-y) (A v))*t+0 := by
    intro t
    have h := hmin (x+t • v)
    rw [actual_residual_two_sided_perturbation_expansion] at h
    nlinarith
  have hd := discrim_le_zero hq
  simp only [discrim,mul_zero,sub_zero] at hd
  nlinarith [sq_nonneg (inner ℝ (A x-y) (A v))]

theorem actual_normal_equation_iff_residual_perpendicular_to_whole_range
    (A : V →L[ℝ] W) (y : W) (x : V) :
    A.adjoint (A x-y)=0 ↔ ∀v : V,inner ℝ (A x-y) (A v)=0 := by
  constructor
  · intro h v
    rw [← A.adjoint_inner_left v (A x-y),h,inner_zero_left]
  · intro h
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [A.adjoint_inner_left]
    exact h (A.adjoint (A x-y))

theorem actual_normal_equation_gives_exact_global_loss_difference
    (A : V →L[ℝ] W) (y : W) (x : V)
    (hx : A.adjoint (A x-y)=0) (z : V) :
    loss A y z = loss A y x + ‖A (z-x)‖^2 := by
  have ho := (actual_normal_equation_iff_residual_perpendicular_to_whole_range A y x).mp hx
  have he := actual_residual_two_sided_perturbation_expansion A y x (z-x) 1
  simp only [one_smul,add_sub_cancel,one_pow,mul_one,ho,mul_zero,add_zero] at he
  simpa using he

theorem actual_least_squares_global_minimum_iff_normal_equation
    (A : V →L[ℝ] W) (y : W) (x : V) :
    (∀z : V,loss A y x ≤ loss A y z) ↔ A.adjoint (A x-y)=0 := by
  constructor
  · intro h
    apply (actual_normal_equation_iff_residual_perpendicular_to_whole_range A y x).mpr
    exact actual_global_minimum_forces_every_residual_inner_product_zero A y x h
  · intro h z
    rw [actual_normal_equation_gives_exact_global_loss_difference A y x h z]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem actual_independent_columns_gram_is_strictly_positive
    (A : V →L[ℝ] W) (hA : Function.Injective A) (v : V) (hv : v≠0) :
    0 < inner ℝ v (A.adjoint (A v)) := by
  rw [A.adjoint_inner_right,real_inner_self_eq_norm_sq]
  have hn : A v ≠ 0 := by
    intro h
    apply hv
    apply hA
    simpa using h
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

theorem actual_independent_columns_make_the_normal_equation_solution_unique
    (A : V →L[ℝ] W) (hA : Function.Injective A) (y : W) (x : V)
    (hx : A.adjoint (A x-y)=0) (z : V) :
    loss A y z = loss A y x ↔ z=x := by
  rw [actual_normal_equation_gives_exact_global_loss_difference A y x hx z]
  constructor
  · intro h
    have hs : ‖A (z-x)‖^2=0 := by linarith
    have hn : ‖A (z-x)‖=0 := by nlinarith [norm_nonneg (A (z-x))]
    have hz : A (z-x)=0 := norm_eq_zero.mp hn
    have hzx : z-x=0 := hA (by simpa using hz)
    exact sub_eq_zero.mp hzx
  · rintro rfl
    simp

theorem actual_finite_dimensional_independent_columns_have_one_attained_minimum
    [FiniteDimensional ℝ V] (A : V →L[ℝ] W) (hA : Function.Injective A) (y : W) :
    ∃!x : V,∀z : V,loss A y x ≤ loss A y z := by
  have hinj : Function.Injective (A.adjoint.comp A).toLinearMap :=
    A.adjoint_comp_self_injective_iff.mpr hA
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨x,hx⟩ := hsurj (A.adjoint y)
  have hn : A.adjoint (A x-y)=0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hx
  refine ⟨x,(actual_least_squares_global_minimum_iff_normal_equation A y x).mpr hn,?_⟩
  intro z hz
  apply (actual_independent_columns_make_the_normal_equation_solution_unique A hA y x hn z).mp
  exact le_antisymm (hz x)
    ((actual_least_squares_global_minimum_iff_normal_equation A y x).mpr hn z)

theorem actual_independent_matrix_columns_give_positive_definite_transpose_gram
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (H : Matrix m n ℝ) (hH : Function.Injective H.mulVec) :
    (H.transpose*H).PosDef := by
  have ht : H.conjTranspose=H.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [← ht]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_conjTranspose_mul_self H) ?_
  intro x hx
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_conjTranspose,star_star]
  apply Matrix.dotProduct_star_self_pos_iff.mpr
  intro hz
  apply hx
  apply hH
  simpa using hz

end SafeLearning.CompleteFoundationsResidualOrthogonality27


namespace SafeLearning.CompleteFoundationsResidualOrthogonality27
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem actual_residual_direction_derivative_follows_from_expansion
    (A : V →L[ℝ] W) (y : W) (x v : V) :
    HasDerivAt (fun t : ℝ => loss A y (x+t • v))
      (2*inner ℝ (A x-y) (A v)) 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) (loss A y x)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul (2*inner ℝ (A x-y) (A v)))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (‖A v‖^2))
  convert h using 1
  · funext t
    change loss A y (x+t • v) = loss A y x + (2*inner ℝ (A x-y) (A v))*t + ‖A v‖^2*t^2
    rw [actual_residual_two_sided_perturbation_expansion]
    ring
  · norm_num

theorem actual_every_local_minimum_has_a_residual_perpendicular_to_whole_range
    (A : V →L[ℝ] W) (y : W) (x : V) (hx : IsLocalMin (loss A y) x) :
    ∀v : V,inner ℝ (A x-y) (A v)=0 := by
  intro v
  have hc : ContinuousAt (fun t : ℝ => x+t • v) 0 := by fun_prop
  have hl : IsLocalMin (loss A y) ((fun t : ℝ => x+t • v) 0) := by simpa using hx
  have hlocal : IsLocalMin (fun t : ℝ => loss A y (x+t • v)) 0 :=
    IsLocalMin.comp_continuous (g := fun t : ℝ => x+t • v) hl hc
  have hd := hlocal.hasDerivAt_eq_zero
    (actual_residual_direction_derivative_follows_from_expansion A y x v)
  linarith

theorem actual_local_least_squares_minimum_is_already_a_global_minimum
    (A : V →L[ℝ] W) (y : W) (x : V) (hx : IsLocalMin (loss A y) x) :
    ∀z : V,loss A y x ≤ loss A y z := by
  apply (actual_least_squares_global_minimum_iff_normal_equation A y x).mpr
  apply (actual_normal_equation_iff_residual_perpendicular_to_whole_range A y x).mpr
  exact actual_every_local_minimum_has_a_residual_perpendicular_to_whole_range A y x hx

end SafeLearning.CompleteFoundationsResidualOrthogonality27
