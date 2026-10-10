import SafeLearning.CompletePolicyMetricPrices
import SafeLearning.CompleteFoundationsConstrainedModels

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SafeLearning.CompletePolicyLagrangianPrices
open CompletePolicyMetricPrices
open CompleteFoundationsConstrainedModels
open CompleteFoundationsCalculusModels (coordinate)
open CompleteFoundationsSpectralModels (point inner_coordinate_formula)

def lagrangian (lambda nu : ℝ) (s : Plane) : ℝ :=
  reward s - lambda * (trustCost s - 1/2) - nu * (s 0 - 1/5)

theorem genuine_source_lagrangian_gradient (lambda nu : ℝ) (s : Plane) :
    HasGradientAt (lagrangian lambda nu)
      (vector (2 - lambda*s 0 - nu) (1 - 4*lambda*s 1)) s := by
  have hr : HasGradientAt reward (point 2 1) s := by
    convert actual_affine_constraint_gradient 2 1 0 s using 1
    funext z
    simp [reward,affineConstraint]
  have ht : HasGradientAt trustCost (point (s 0) (4*s 1)) s := by
    convert actual_weighted_distance_gradient 1 4 0 0 s using 1
    · funext z
      rw [genuine_trust_quadratic]
      simp [weightedDistance]
      ring
    · simp
  have hf := (hr.hasFDerivAt.sub (ht.hasFDerivAt.sub_const (1/2) |>.const_mul lambda)).sub
    (((coordinate 0).hasFDerivAt (x := s)).sub_const (1/5) |>.const_mul nu)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf using 1
  · rfl
  · ext u
    simp [vector,point,InnerProductSpace.toDual_apply_apply,
      coordinate,PiLp.proj,PiLp.projₗ,Fin.sum_univ_two,PiLp.inner_apply]
    ring

theorem genuine_gradient_is_matrix_stationarity (lambda nu : ℝ) (s : Plane) :
    vector (2-lambda*s 0-nu) (1-4*lambda*s 1) =
      vector 2 1 - lambda • WithLp.toLp 2 (H *ᵥ WithLp.ofLp s) - nu • vector 1 0 := by
  ext i
  fin_cases i <;> simp [vector,H,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem genuine_optimizer_zero_gradient :
    HasGradientAt (lagrangian (5/(4*Real.sqrt 6)) (2-1/(4*Real.sqrt 6)))
      0 (vector (1/5) (Real.sqrt 6/5)) := by
  have h := genuine_source_lagrangian_gradient (5/(4*Real.sqrt 6))
    (2-1/(4*Real.sqrt 6)) (vector (1/5) (Real.sqrt 6/5))
  have hp : 0 < Real.sqrt (6 : ℝ) := by positivity
  have hz : vector
      (2-(5/(4*Real.sqrt 6))*(vector (1/5) (Real.sqrt 6/5)) 0-(2-1/(4*Real.sqrt 6)))
      (1-4*(5/(4*Real.sqrt 6))*(vector (1/5) (Real.sqrt 6/5)) 1) = 0 := by
    ext i
    fin_cases i <;> simp [vector] <;> field_simp <;> ring
  rw [hz] at h
  exact h

end SafeLearning.CompletePolicyLagrangianPrices
