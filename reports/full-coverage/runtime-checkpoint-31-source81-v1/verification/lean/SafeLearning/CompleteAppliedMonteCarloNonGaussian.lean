import SafeLearning.CompleteAppliedMonteCarloEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open SafeLearning.CompleteAppliedMonteCarloEstimate
namespace SafeLearning.CompleteAppliedMonteCarloNonGaussian

theorem actual_finite_bernoulli_episode_average_is_not_any_exact_gaussian_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 200 → Ω → ℝ) (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0
      SafeLearning.CompleteAppliedValidationTests.twoPercent) μ)
    (mean : ℝ) (v : ℝ≥0) :
    ¬HasLaw (empiricalRate 200 X) (gaussianReal mean v) μ := by
  intro hg
  have hvsource := (actual_independent_episode_average_has_the_source_mean_and_variance
    μ 200 (by norm_num) X SafeLearning.CompleteAppliedValidationTests.twoPercent hInd hLaw).2
  have hvg := hg.variance_eq
  rw [variance_id_gaussianReal] at hvg
  by_cases hv : v=0
  · rw [hv] at hvg
    norm_num [SafeLearning.CompleteAppliedValidationTests.twoPercent] at hvsource hvg
    linarith
  · have hz := SafeLearning.CompleteAppliedValidationTests.positive_zero_failure_probability_at_two_percent
      μ 200 X hInd hLaw
    have hatom : 0<μ.real {omega | empiricalRate 200 X omega=0} := by
      apply hz.trans_le
      refine measureReal_mono ?_ (by finiteness)
      intro omega hclean
      exact (actual_fourteen_failures_and_zero_failures_plug_in_the_literal_rates X omega).2.1 hclean
    let : NullSingletonClass (gaussianReal mean v) := nullSingletonClass_gaussianReal hv
    have he := hg.measureReal_eq (p := fun x : ℝ => x=0) (by measurability)
    have hzero : (gaussianReal mean v).real {x | x=0}=0 := by
      simp [Measure.real]
    rw [he,hzero] at hatom
    exact (lt_irrefl 0) hatom

end SafeLearning.CompleteAppliedMonteCarloNonGaussian
