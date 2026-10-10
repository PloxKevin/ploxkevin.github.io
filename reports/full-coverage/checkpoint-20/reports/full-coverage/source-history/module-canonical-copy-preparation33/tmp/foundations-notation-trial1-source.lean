import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Gradient

namespace SafeLearning.CompleteFoundationsNotation

theorem actual_euclidean_norm_is_the_square_root_of_the_coordinate_dot_product
    (dimension : ℕ) (x : EuclideanSpace ℝ (Fin dimension)) :
    ‖x‖ = Real.sqrt ((fun i => x i) ⬝ᵥ (fun i => x i)) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [dotProduct, Real.norm_eq_abs, sq_abs, pow_two]

theorem actual_euclidean_distance_is_the_norm_of_the_difference
    (dimension : ℕ) (x y : EuclideanSpace ℝ (Fin dimension)) :
    dist x y = ‖x-y‖ := dist_eq_norm x y

theorem actual_closed_and_open_real_interval_notation (a b x : ℝ) :
    (x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b) ∧
      (x ∈ Ioo a b ↔ a < x ∧ x < b) ∧
      IsClosed (Icc a b) ∧ IsOpen (Ioo a b) :=
  ⟨Iff.rfl, Iff.rfl, isClosed_Icc, isOpen_Ioo⟩

theorem actual_source_discount_interval_notation (gamma : ℝ) :
    gamma ∈ Ico (0:ℝ) 1 ↔ 0 ≤ gamma ∧ gamma < 1 := Iff.rfl

theorem actual_barrier_safe_set_is_its_nonnegative_preimage
    {X : Type*} (barrier : X → ℝ) :
    {x | 0 ≤ barrier x} = barrier ⁻¹' Ici 0 := rfl

theorem actual_closed_loop_is_the_composed_dynamics_and_policy
    {X U : Type*} (dynamics : X → U → X) (policy : X → U)
    (initial : X) (time : ℕ) :
    (fun x => dynamics x (policy x))^[0] initial = initial ∧
      (fun x => dynamics x (policy x))^[time+1] initial =
        dynamics ((fun x => dynamics x (policy x))^[time] initial)
          (policy ((fun x => dynamics x (policy x))^[time] initial)) := by
  exact ⟨rfl, Function.iterate_succ_apply' _ _ _⟩

def coordinatePartial (dimension : ℕ) (f : EuclideanSpace ℝ (Fin dimension) → ℝ)
    (x : EuclideanSpace ℝ (Fin dimension)) (coordinate : Fin dimension) : ℝ :=
  deriv (fun t : ℝ => f (x+t • PiLp.single 2 coordinate (1:ℝ))) 0

theorem actual_coordinate_slice_has_the_frechet_directional_derivative
    (dimension : ℕ) (f : EuclideanSpace ℝ (Fin dimension) → ℝ)
    (x : EuclideanSpace ℝ (Fin dimension)) (hf : DifferentiableAt ℝ f x)
    (coordinate : Fin dimension) :
    HasDerivAt (fun t : ℝ => f (x+t • PiLp.single 2 coordinate (1:ℝ)))
      ((fderiv ℝ f x) (PiLp.single 2 coordinate (1:ℝ))) 0 := by
  have hs : HasDerivAt (fun t : ℝ => x+t • PiLp.single 2 coordinate (1:ℝ))
      (PiLp.single 2 coordinate (1:ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (PiLp.single 2 coordinate (1:ℝ))).const_add x
  simpa using hf.hasFDerivAt.comp_hasDerivAt 0 hs

theorem actual_official_euclidean_gradient_is_the_vector_of_actual_partial_derivatives
    (dimension : ℕ) (f : EuclideanSpace ℝ (Fin dimension) → ℝ)
    (x : EuclideanSpace ℝ (Fin dimension)) (hf : DifferentiableAt ℝ f x)
    (coordinate : Fin dimension) :
    gradient f x coordinate = coordinatePartial dimension f x coordinate := by
  have hg : gradient f x coordinate =
      (fderiv ℝ f x) (PiLp.single 2 coordinate (1:ℝ)) := by
    have hi := inner_gradient_left (f := f) (x := x) (y := PiLp.single 2 coordinate (1:ℝ))
    simpa [PiLp.inner_apply] using hi
  rw [coordinatePartial, (actual_coordinate_slice_has_the_frechet_directional_derivative
    dimension f x hf coordinate).deriv]
  exact hg

def sourceJacobian (rows columns : ℕ)
    (f : EuclideanSpace ℝ (Fin columns) → EuclideanSpace ℝ (Fin rows))
    (x : EuclideanSpace ℝ (Fin columns)) : Matrix (Fin rows) (Fin columns) ℝ :=
  fun output input => (fderiv ℝ f x (PiLp.single 2 input (1:ℝ))) output

theorem actual_jacobian_entries_are_genuine_coordinate_partial_derivatives
    (rows columns : ℕ)
    (f : EuclideanSpace ℝ (Fin columns) → EuclideanSpace ℝ (Fin rows))
    (x : EuclideanSpace ℝ (Fin columns)) (hf : DifferentiableAt ℝ f x)
    (output : Fin rows) (input : Fin columns) :
    HasDerivAt (fun t : ℝ => f (x+t • PiLp.single 2 input (1:ℝ)) output)
      (sourceJacobian rows columns f x output input) 0 := by
  have hs : HasDerivAt (fun t : ℝ => x+t • PiLp.single 2 input (1:ℝ))
      (PiLp.single 2 input (1:ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (PiLp.single 2 input (1:ℝ))).const_add x
  have hvec := hf.hasFDerivAt.comp_hasDerivAt 0 hs
  simpa [sourceJacobian] using (EuclideanSpace.proj output).hasFDerivAt.comp_hasDerivAt 0 hvec

theorem actual_jacobian_is_the_matrix_of_the_genuine_frechet_derivative
    (rows columns : ℕ)
    (f : EuclideanSpace ℝ (Fin columns) → EuclideanSpace ℝ (Fin rows))
    (x velocity : EuclideanSpace ℝ (Fin columns)) :
    (fun output => (fderiv ℝ f x velocity) output) =
      (sourceJacobian rows columns f x).mulVec (fun input => velocity input) := by
  have hv : velocity = ∑ input, velocity input • PiLp.single 2 input (1:ℝ) := by
    ext input
    simp
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul]
  ext output
  simp only [sourceJacobian, Matrix.mulVec, dotProduct, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, mul_comm]

end SafeLearning.CompleteFoundationsNotation
