import SafeLearning.CompleteAppliedBaselines
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedBaselineDegenerate
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedBaselines

/-- A zero score second moment is an actual degenerate random variable, not a ratio convention. -/
theorem zero_second_moment_score_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (score : Ω → ℝ) (hscore : MemLp score 2 μ)
    (hzero : (∫ omega,score omega^2 ∂μ)=0) : score=ᵐ[μ]0 := by
  have hsquare : (fun omega => score omega^2)=ᵐ[μ]0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun omega => sq_nonneg (score omega)))
      hscore.integrable_sq).mp hzero
  filter_upwards [hsquare] with omega homega
  exact sq_eq_zero_iff.mp homega

/-- Every constant baseline gives zero gradient variance in the degenerate score case. -/
theorem every_baseline_zero_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reward score : Ω → ℝ) (hscore : MemLp score 2 μ)
    (hzero : (∫ omega,score omega^2 ∂μ)=0) (baseline : ℝ) :
    variance (gradientSample reward score baseline) μ=0 := by
  have hgrad : gradientSample reward score baseline=ᵐ[μ]0 := by
    filter_upwards [zero_second_moment_score_ae μ score hscore hzero] with omega homega
    simp [gradientSample,homega]
  rw [variance_congr hgrad,variance_zero]

/-- In Lean's totalized division convention the ratio is still a minimizer in both cases.
Ordinary mathematical division requires the positive-second-moment case. -/
theorem score_weighted_baseline_minimum_including_degenerate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (reward score : Ω → ℝ)
    (hproduct : MemLp (fun omega => reward omega*score omega) 2 μ)
    (hscore : MemLp score 2 μ) (hzero : (∫ omega,score omega ∂μ)=0)
    (baseline : ℝ) :
    variance (gradientSample reward score
      ((∫ omega,reward omega*score omega^2 ∂μ)/(∫ omega,score omega^2 ∂μ))) μ≤
      variance (gradientSample reward score baseline) μ := by
  have hnonneg : 0≤∫ omega,score omega^2 ∂μ :=
    integral_nonneg (fun omega => sq_nonneg (score omega))
  by_cases hp : 0<∫ omega,score omega^2 ∂μ
  · exact (actual_general_score_weighted_variance_minimum μ reward score hproduct hscore
      hzero hp baseline).1
  · have heq : (∫ omega,score omega^2 ∂μ)=0 := le_antisymm (le_of_not_gt hp) hnonneg
    rw [every_baseline_zero_variance μ reward score hscore heq,
      every_baseline_zero_variance μ reward score hscore heq]

end SafeLearning.CompleteAppliedBaselineDegenerate
