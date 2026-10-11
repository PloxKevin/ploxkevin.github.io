import SafeLearning.CompleteFoundationsSpectralModels
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators Gradient

namespace SafeLearning.CompleteFoundationsLiteralChainLie28Notation
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
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • PiLp.single 2 coordinate (1:ℝ)) :=
    by simpa using hf.hasFDerivAt
  convert! hf'.comp_hasDerivAt (0:ℝ) hs using 1

theorem actual_official_euclidean_gradient_is_the_vector_of_actual_partial_derivatives
    (dimension : ℕ) (f : EuclideanSpace ℝ (Fin dimension) → ℝ)
    (x : EuclideanSpace ℝ (Fin dimension)) (hf : DifferentiableAt ℝ f x)
    (coordinate : Fin dimension) :
    gradient f x coordinate = coordinatePartial dimension f x coordinate := by
  have hg : gradient f x coordinate =
      (fderiv ℝ f x) (PiLp.single 2 coordinate (1:ℝ)) := by
    rw [←inner_gradient_left]
    change gradient f x coordinate = inner ℝ (gradient f x) (EuclideanSpace.single coordinate (1:ℝ))
    rw [EuclideanSpace.inner_single_right]
    simp
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
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • PiLp.single 2 input (1:ℝ)) :=
    by simpa using hf.hasFDerivAt
  have hvec := hf'.comp_hasDerivAt 0 hs
  let projection : EuclideanSpace ℝ (Fin rows) →L[ℝ] ℝ := EuclideanSpace.proj output
  have houtput := projection.hasFDerivAt.comp_hasDerivAt (0:ℝ) hvec
  convert! houtput using 1

theorem actual_jacobian_is_the_matrix_of_the_genuine_frechet_derivative
    (rows columns : ℕ)
    (f : EuclideanSpace ℝ (Fin columns) → EuclideanSpace ℝ (Fin rows))
    (x velocity : EuclideanSpace ℝ (Fin columns)) :
    (fun output => (fderiv ℝ f x velocity) output) =
      (sourceJacobian rows columns f x).mulVec (fun input => velocity input) := by
  have hv : velocity = ∑ input, velocity input • PiLp.single 2 input (1:ℝ) := by
    ext input
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul]
  ext output
  simp [WithLp.ofLp_sum, sourceJacobian, Matrix.mulVec, dotProduct, mul_comm]

end SafeLearning.CompleteFoundationsLiteralChainLie28Notation

namespace SafeLearning.CompleteFoundationsLiteralChainLie28
open SafeLearning.CompleteFoundationsLiteralChainLie28Notation
abbrev Vector (n : ℕ) := EuclideanSpace ℝ (Fin n)
def matrixMap {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) :
    Vector n →L[ℝ] Vector m := (Matrix.toEuclideanLin W).toContinuousLinearMap

theorem actual_full_rectangular_jacobian_chain_rule
    {n m k : ℕ} (g : Vector n → Vector m) (f : Vector m → Vector k)
    (x : Vector n) (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ f (g x)) :
    sourceJacobian k n (f ∘ g) x = sourceJacobian k m f (g x) * sourceJacobian m n g x := by
  ext i j
  rw [sourceJacobian,fderiv_comp x hf hg]
  change (fderiv ℝ f (g x) (fderiv ℝ g x (PiLp.single 2 j (1:ℝ)))) i = _
  rw [congrFun (actual_jacobian_is_the_matrix_of_the_genuine_frechet_derivative
    k m f (g x) (fderiv ℝ g x (PiLp.single 2 j (1:ℝ)))) i]
  simp only [Matrix.mulVec,dotProduct,Matrix.mul_apply,sourceJacobian]

theorem actual_scalar_chain_rule_along_an_arbitrary_differentiable_curve
    {n : ℕ} (f : Vector n → ℝ) (curve : ℝ → Vector n)
    (t : ℝ) (velocity : Vector n)
    (hf : DifferentiableAt ℝ f (curve t)) (hcurve : HasDerivAt curve velocity t) :
    HasDerivAt (fun s => f (curve s)) (inner ℝ (gradient f (curve t)) velocity) t := by
  have h := hf.hasGradientAt.hasFDerivAt.comp_hasDerivAt t hcurve
  convert! h using 1

theorem actual_gradient_chain_rule_is_the_transposed_jacobian_product
    {n m : ℕ} (g : Vector n → Vector m) (f : Vector m → ℝ) (x : Vector n)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ f (g x)) :
    (fun j => gradient (f ∘ g) x j) =
      (sourceJacobian m n g x)ᵀ.mulVec (fun i => gradient f (g x) i) := by
  ext j
  have hcomp := hf.comp x hg
  have hleft : gradient (f ∘ g) x j =
      (fderiv ℝ (f ∘ g) x) (PiLp.single 2 j (1:ℝ)) := by
    rw [actual_official_euclidean_gradient_is_the_vector_of_actual_partial_derivatives
      n (f ∘ g) x hcomp j,coordinatePartial]
    exact (actual_coordinate_slice_has_the_frechet_directional_derivative n (f ∘ g) x hcomp j).deriv
  rw [hleft,fderiv_comp x hf hg,ContinuousLinearMap.comp_apply,←inner_gradient_left]
  change (∑ i, gradient f (g x) i *
      (fderiv ℝ g x (PiLp.single 2 j (1:ℝ))) i) = _
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,sourceJacobian]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem actual_dot_product_curve_derivative_is_the_product_rule
    {n : ℕ} (a b : ℝ → Vector n) (t : ℝ) (da db : Vector n)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun s => (fun i => a s i) ⬝ᵥ (fun i => b s i))
      ((fun i => da i) ⬝ᵥ (fun i => b t i)+(fun i => a t i) ⬝ᵥ (fun i => db i)) t := by
  convert! ha.inner ℝ hb using 1
  · funext s
    simp [dotProduct,PiLp.inner_apply]
  · simp [dotProduct,PiLp.inner_apply,add_comm]

theorem actual_inner_matrix_action_is_the_input_lie_derivative_row
    {n m : ℕ} (gradientValue : Vector n) (G : Matrix (Fin n) (Fin m) ℝ)
    (u : Vector m) :
    inner ℝ gradientValue (matrixMap G u) =
      (Gᵀ.mulVec (fun i => gradientValue i)) ⬝ᵥ (fun j => u j) := by
  change (∑ i, gradientValue i * G.mulVec (fun j => u j) i) = _
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

def driftLie {n : ℕ} (h : Vector n → ℝ) (x : Vector n)
    (drift : Vector n → Vector n) : ℝ := inner ℝ (gradient h x) (drift x)
def inputLieRow {n m : ℕ} (h : Vector n → ℝ) (x : Vector n)
    (G : Vector n → Matrix (Fin n) (Fin m) ℝ) : Fin m → ℝ :=
  (G x)ᵀ.mulVec (fun i => gradient h x i)

theorem actual_control_affine_trajectory_has_the_full_source_lie_derivative
    {n m : ℕ} (h : Vector n → ℝ) (trajectory : ℝ → Vector n)
    (drift : Vector n → Vector n) (G : Vector n → Matrix (Fin n) (Fin m) ℝ)
    (input : ℝ → Vector m) (t : ℝ)
    (hh : ContDiffAt ℝ 1 h (trajectory t))
    (htrajectory : HasDerivAt trajectory
      (drift (trajectory t)+matrixMap (G (trajectory t)) (input t)) t) :
    HasDerivAt (fun s => h (trajectory s))
      (driftLie h (trajectory t) drift+
        inputLieRow h (trajectory t) G ⬝ᵥ (fun j => input t j)) t := by
  have hf := actual_scalar_chain_rule_along_an_arbitrary_differentiable_curve
    h trajectory t _ (hh.differentiableAt (by norm_num)) htrajectory
  rw [inner_add_right,actual_inner_matrix_action_is_the_input_lie_derivative_row] at hf
  exact hf

end SafeLearning.CompleteFoundationsLiteralChainLie28
