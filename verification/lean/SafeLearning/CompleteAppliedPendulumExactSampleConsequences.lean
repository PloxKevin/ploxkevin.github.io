import SafeLearning.CompleteAppliedPendulumExactSample

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
namespace SafeLearning.CompleteAppliedPendulumExactSampleConsequences
open SafeLearning.CompleteAppliedPendulumLinear
open SafeLearning.CompleteAppliedPendulumExactSample

def complexification : Matrix (Fin 2) (Fin 2) ℝ →+* Matrix (Fin 2) (Fin 2) ℂ :=
  (algebraMap ℝ ℂ).mapMatrix

theorem actual_matrix_complexification_is_continuous : Continuous complexification := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun A:Matrix (Fin 2) (Fin 2) ℝ=>(algebraMap ℝ ℂ) (A i j))
  fun_prop

theorem actual_complex_sample_is_exactly_the_real_source_matrix_exponential_complexified :
    actualSample=complexification (NormedSpace.exp ((1/10:ℝ) • matrix (-10))) := by
  have h:=NormedSpace.map_exp complexification actual_matrix_complexification_is_continuous
    ((1/10:ℝ) • matrix (-10))
  have hg : complexification ((1/10:ℝ) • matrix (-10))=generator := by
    ext i j
    simp [complexification,RingHom.mapMatrix_apply,generator,complexMatrix]
  rw [hg] at h
  exact h.symm

theorem actual_real_source_exact_sample_has_the_source_official_complex_spectrum (z:ℂ) :
    z∈spectrum ℂ (complexification (NormedSpace.exp ((1/10:ℝ) • matrix (-10)))) ↔
      z=Complex.exp (hangingPlus/10) ∨ z=Complex.exp (hangingMinus/10) := by
  rw [←actual_complex_sample_is_exactly_the_real_source_matrix_exponential_complexified]
  exact actual_exact_sample_official_spectrum z

end SafeLearning.CompleteAppliedPendulumExactSampleConsequences
