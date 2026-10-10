import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SafeLearning.CompleteAppliedGaussianMoments

theorem actual_gaussian_parameters_are_the_mean_and_variance (mean : ℝ) (variance : ℝ≥0) :
    (∫ x : ℝ,x ∂gaussianReal mean variance)=mean ∧
      Var[fun x : ℝ=>x;gaussianReal mean variance]=(variance:ℝ) := by
  exact ⟨integral_id_gaussianReal,variance_fun_id_gaussianReal⟩

theorem actual_source_random_variable_mean_variance_and_standard_deviation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω→ℝ}
    (hX : HasLaw X (gaussianReal 10 4) P) :
    (∫ω,X ω ∂P)=10 ∧ Var[X;P]=4 ∧ Real.sqrt (Var[X;P])=2 := by
  have hm := hX.integral_eq
  have hv := hX.variance_eq
  rw [integral_id_gaussianReal] at hm
  rw [variance_id_gaussianReal] at hv
  norm_num at hv
  refine ⟨hm,hv,?_⟩
  rw [hv]
  norm_num

end SafeLearning.CompleteAppliedGaussianMoments
