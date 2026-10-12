import SafeLearning.CompleteAppliedMonteCarloNonGaussian

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open SafeLearning.CompleteAppliedMonteCarloEstimate
namespace SafeLearning.CompleteAppliedMonteCarloModel

def actualEpisodeLaw : Measure (Fin 200 → ℝ) :=
  Measure.pi (fun _ : Fin 200 => bernoulliMeasure (1:ℝ) 0
    SafeLearning.CompleteAppliedValidationTests.twoPercent)
def actualEpisodeIndicator (i : Fin 200) (omega : Fin 200 → ℝ) : ℝ := omega i

instance : IsProbabilityMeasure actualEpisodeLaw := by
  unfold actualEpisodeLaw
  infer_instance

theorem actual_constructed_two_hundred_episode_law_has_independent_bernoulli_coordinates :
    iIndepFun actualEpisodeIndicator actualEpisodeLaw ∧
    ∀ i,HasLaw (actualEpisodeIndicator i)
      (bernoulliMeasure (1:ℝ) 0 SafeLearning.CompleteAppliedValidationTests.twoPercent)
      actualEpisodeLaw := by
  constructor
  · change iIndepFun (fun i (omega : Fin 200 → ℝ) => omega i)
      (Measure.pi (fun _ : Fin 200 => bernoulliMeasure (1:ℝ) 0
        SafeLearning.CompleteAppliedValidationTests.twoPercent))
    exact iIndepFun_pi (μ := fun _ : Fin 200 => bernoulliMeasure (1:ℝ) 0
        SafeLearning.CompleteAppliedValidationTests.twoPercent)
        (X := fun _ => id) (fun _ => aemeasurable_id)
  · intro i
    exact (measurePreserving_eval (fun _ : Fin 200 => bernoulliMeasure (1:ℝ) 0
      SafeLearning.CompleteAppliedValidationTests.twoPercent) i).hasLaw

theorem actual_constructed_episode_model_can_record_zero_failures_at_nonzero_population_rate :
    actualEpisodeLaw.real {omega | ∀ i,actualEpisodeIndicator i omega=0}=(49/50:ℝ)^200 ∧
    0<actualEpisodeLaw.real {omega | ∀ i,actualEpisodeIndicator i omega=0} ∧
    (∀ mean : ℝ,∀ v : ℝ≥0,
      ¬HasLaw (empiricalRate 200 actualEpisodeIndicator) (gaussianReal mean v) actualEpisodeLaw) := by
  obtain ⟨hi,hl⟩ := actual_constructed_two_hundred_episode_law_has_independent_bernoulli_coordinates
  refine ⟨?_,?_,?_⟩
  · simpa only [SafeLearning.CompleteAppliedValidationTests.twoPercent,NNReal.coe_mk,
      show (1-(1/50:ℝ))=(49/50:ℝ) by norm_num] using
      actual_two_hundred_clean_episodes_have_the_exact_probability actualEpisodeLaw
        actualEpisodeIndicator SafeLearning.CompleteAppliedValidationTests.twoPercent hi hl
  · exact SafeLearning.CompleteAppliedValidationTests.positive_zero_failure_probability_at_two_percent
      actualEpisodeLaw 200 actualEpisodeIndicator hi hl
  · intro mean v
    exact SafeLearning.CompleteAppliedMonteCarloNonGaussian.actual_finite_bernoulli_episode_average_is_not_any_exact_gaussian_law
      actualEpisodeLaw actualEpisodeIndicator hi hl mean v

end SafeLearning.CompleteAppliedMonteCarloModel
