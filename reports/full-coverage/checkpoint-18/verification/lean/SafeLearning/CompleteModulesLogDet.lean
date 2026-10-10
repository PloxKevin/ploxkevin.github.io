import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace SafeLearning.CompleteModulesLogDet

variable {N : Type*} [Fintype N] [DecidableEq N]

def determinantAlternating : (N → ℝ) [⋀^N]→L[ℝ] ℝ :=
  { Matrix.detRowAlternating with cont := continuous_id.matrix_det }

def traceProductLinear (coefficient : Matrix N N ℝ) : Matrix N N ℝ →ₗ[ℝ] ℝ where
  toFun perturbation := Matrix.trace (coefficient*perturbation)
  map_add' first second := by simp [Matrix.mul_add,Matrix.trace_add]
  map_smul' scalar perturbation := by simp [Matrix.mul_smul,Matrix.trace_smul]

def traceProductFunctional (coefficient : Matrix N N ℝ) : Matrix N N ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (traceProductLinear coefficient)

theorem actual_determinant_multilinear_derivative (matrix perturbation : Matrix N N ℝ) :
    determinantAlternating.toContinuousMultilinearMap.linearDeriv matrix perturbation=
      Matrix.trace (matrix.adjugate*perturbation) := by
  change (determinantAlternating.toContinuousMultilinearMap.linearDeriv
    (fun i => matrix i) (fun i => perturbation i))=Matrix.trace (matrix.adjugate*perturbation)
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, Matrix.det (matrix.updateRow i (perturbation i)))=
    Matrix.trace (matrix.adjugate*perturbation)
  have hrow : ∀ i, Matrix.det (matrix.updateRow i (perturbation i))=
      (matrix.adjugateᵀ *ᵥ perturbation i) i := by
    intro i
    rw [← Matrix.cramer_transpose_apply,Matrix.cramer_eq_adjugate_mulVec,Matrix.adjugate_transpose]
  simp_rw [hrow,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
  unfold Matrix.trace
  simp only [Matrix.diag,Matrix.mul_apply]
  rw [Finset.sum_comm]

theorem actual_determinant_has_frechet_derivative (matrix : Matrix N N ℝ) :
    HasFDerivAt Matrix.det (traceProductFunctional matrix.adjugate) matrix := by
  have h := determinantAlternating.hasFDerivAt matrix
  have he : determinantAlternating.toContinuousMultilinearMap.linearDeriv matrix=
      traceProductFunctional matrix.adjugate := by
    ext perturbation
    exact actual_determinant_multilinear_derivative matrix perturbation
  rw [he] at h
  exact h

theorem inverse_trace_functional_is_scaled_adjugate (matrix : Matrix N N ℝ) :
    traceProductFunctional matrix⁻¹=matrix.det⁻¹ • traceProductFunctional matrix.adjugate := by
  ext perturbation
  change Matrix.trace (matrix⁻¹*perturbation)=matrix.det⁻¹*Matrix.trace (matrix.adjugate*perturbation)
  rw [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_mul,Matrix.trace_smul]
  rfl

theorem actual_logdet_has_frechet_derivative (matrix : Matrix N N ℝ) (hdet : matrix.det ≠ 0) :
    HasFDerivAt (fun candidate : Matrix N N ℝ => Real.log candidate.det)
      (traceProductFunctional matrix⁻¹) matrix := by
  have h := (actual_determinant_has_frechet_derivative matrix).log hdet
  rw [inverse_trace_functional_is_scaled_adjugate matrix]
  exact h

theorem actual_logdet_curve_derivative (curve : ℝ → Matrix N N ℝ)
    (derivative : Matrix N N ℝ) (point : ℝ) (hcurve : HasDerivAt curve derivative point)
    (hdet : (curve point).det ≠ 0) :
    HasDerivAt (fun value : ℝ => Real.log (curve value).det)
      (Matrix.trace ((curve point)⁻¹*derivative)) point := by
  exact (actual_logdet_has_frechet_derivative (curve point) hdet).comp_hasDerivAt point hcurve

end SafeLearning.CompleteModulesLogDet
