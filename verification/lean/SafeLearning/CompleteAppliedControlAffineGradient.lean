import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators Gradient
namespace SafeLearning.CompleteAppliedControlAffineGradient

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Differentiability alone gives the actual official gradient in the source's
Lie-derivative formula, rather than a freely supplied derivative row. -/
theorem actual_differentiable_certificate_gradient_chain_rule
    (certificate : E→ℝ) (trajectory : ℝ→E) (drift : E→E)
    (inputMap : E→U→L[ℝ]E) (input : ℝ→U) (time : ℝ)
    (hc : DifferentiableAt ℝ certificate (trajectory time))
    (hx : HasDerivAt trajectory
      (drift (trajectory time)+inputMap (trajectory time) (input time)) time) :
    HasDerivAt (certificate∘trajectory)
      (inner ℝ (gradient certificate (trajectory time)) (drift (trajectory time))+
        inner ℝ (gradient certificate (trajectory time))
          (inputMap (trajectory time) (input time))) time := by
  simpa only [inner_gradient_left,map_add] using hc.hasFDerivAt.comp_hasDerivAt time hx

/-- The official gradient identifies a genuine linear functional of the input. -/
theorem actual_input_lie_derivative_is_the_actual_gradient_linear_functional
    (certificate : E→ℝ) (state : E) (inputMap : U→L[ℝ]E) (input : U) :
    inner ℝ (gradient certificate state) (inputMap input)=
      ((fderiv ℝ certificate state).comp inputMap) input := by
  simp only [inner_gradient_left,ContinuousLinearMap.comp_apply]

variable {n : Type*} [Fintype n]

theorem actual_euclidean_gradient_inner_product_is_the_literal_coordinate_dot_product
    (certificate : EuclideanSpace ℝ n→ℝ) (state velocity : EuclideanSpace ℝ n) :
    inner ℝ (gradient certificate state) velocity=
      (fun i=>gradient certificate state i)⬝ᵥ(fun i=>velocity i) := by
  simp only [PiLp.inner_apply,dotProduct,real_inner_comm]
  rfl

end SafeLearning.CompleteAppliedControlAffineGradient
