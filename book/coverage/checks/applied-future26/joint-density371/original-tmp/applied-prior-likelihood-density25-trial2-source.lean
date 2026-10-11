import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SafeLearning.CompleteAppliedPriorLikelihoodDensity25
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) [SFinite μ] (ν : Measure Y) [SFinite ν]
variable (prior : X → ℝ≥0∞) (hp : Measurable prior)
variable (likelihood : X → Y → ℝ≥0∞) (hl : Measurable (Function.uncurry likelihood))
include hp hl

def likelihoodKernel : Kernel X Y := (Kernel.const X ν).withDensity likelihood

theorem actual_normalized_likelihood_is_markov
    (hlone : ∀ x, ∫⁻ y, likelihood x y ∂ν = 1) :
    IsMarkovKernel (likelihoodKernel ν likelihood) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [likelihoodKernel,Kernel.withDensity_apply _ hl,Kernel.const_apply,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact hlone x

theorem actual_normalized_prior_is_probability
    (hpone : ∫⁻ x, prior x ∂μ = 1) : IsProbabilityMeasure (μ.withDensity prior) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact hpone

theorem actual_generated_joint_has_prior_times_likelihood_density
    (hlone : ∀ x, ∫⁻ y, likelihood x y ∂ν = 1) :
    μ.withDensity prior ⊗ₘ likelihoodKernel ν likelihood =
      (μ.prod ν).withDensity (fun xy => prior xy.1 * likelihood xy.1 xy.2) := by
  haveI := actual_normalized_likelihood_is_markov ν likelihood hl hlone
  rw [likelihoodKernel,Measure.withDensity_compProd_withDensity hp hl,
    Measure.compProd_const]

theorem actual_prior_times_likelihood_joint_is_normalized
    (hpone : ∫⁻ x, prior x ∂μ = 1)
    (hlone : ∀ x, ∫⁻ y, likelihood x y ∂ν = 1) :
    ∫⁻ xy, prior xy.1 * likelihood xy.1 xy.2 ∂μ.prod ν = 1 := by
  have hpj : Measurable (fun xy : X × Y => prior xy.1 * likelihood xy.1 xy.2) :=
    (hp.comp measurable_fst).mul hl
  rw [lintegral_prod _ hpj.aemeasurable]
  calc
    (∫⁻ x, ∫⁻ y, prior x * likelihood x y ∂ν ∂μ) = ∫⁻ x, prior x * 1 ∂μ := by
      apply lintegral_congr
      intro x
      rw [lintegral_const_mul _ (hl.comp (measurable_const.prodMk measurable_id)),hlone x]
    _ = 1 := by simpa using hpone

theorem actual_generated_data_law_has_integrated_likelihood_density
    (hlone : ∀ x, ∫⁻ y, likelihood x y ∂ν = 1) :
    (μ.withDensity prior ⊗ₘ likelihoodKernel ν likelihood).map Prod.snd =
      ν.withDensity (fun y => ∫⁻ x, likelihood x y * prior x ∂μ) := by
  rw [actual_generated_joint_has_prior_times_likelihood_density μ ν prior hp likelihood hl hlone]
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest measurable_snd]
  change (∫⁻ xy, (test ∘ Prod.snd) xy ∂(μ.prod ν).withDensity (fun xy => prior xy.1 * likelihood xy.1 xy.2)) = _
  have hpj : Measurable (fun xy : X × Y => prior xy.1 * likelihood xy.1 xy.2) :=
    (hp.comp measurable_fst).mul hl
  have hdata : Measurable (fun y => ∫⁻ x, likelihood x y * prior x ∂μ) :=
    (hl.mul (hp.comp measurable_fst)).lintegral_prod_left'
  rw [lintegral_withDensity_eq_lintegral_mul _ hpj (htest.comp measurable_snd),
    lintegral_withDensity_eq_lintegral_mul _ hdata htest,
    lintegral_prod_symm _ (hpj.mul (htest.comp measurable_snd)).aemeasurable]
  apply lintegral_congr
  intro y
  have hs : Measurable (fun x => likelihood x y * prior x) :=
    (hl.comp (measurable_id.prodMk measurable_const)).mul hp
  change (∫⁻ x, (prior x * likelihood x y) * test y ∂μ) = (∫⁻ x, likelihood x y * prior x ∂μ) * test y
  rw [← lintegral_mul_const _ hs]
  apply lintegral_congr
  intro x
  rw [mul_comm (prior x) (likelihood x y)]

end SafeLearning.CompleteAppliedPriorLikelihoodDensity25
