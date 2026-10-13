import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Distributions.Bernoulli

open MeasureTheory
open scoped ENNReal

namespace SafeLearning.CompleteAppliedConditionalExpectationMaterial31

section Observation
variable {Ω B : Type*} [MeasurableSpace Ω] [mB : MeasurableSpace B]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Y : Ω → B} {X : Ω → ℝ}

theorem actual_observation_is_measurable_in_its_own_sigma_algebra :
    @Measurable Ω B (mB.comap Y) mB Y :=
  Measurable.of_comap_le le_rfl

theorem actual_known_observation_function_is_strongly_measurable
    {g : B → ℝ} (hg : Measurable g) :
    StronglyMeasurable[mB.comap Y] (fun ω => g (Y ω)) := by
  exact (hg.comp actual_observation_is_measurable_in_its_own_sigma_algebra).stronglyMeasurable

theorem actual_expected_conditional_mean_equals_original_mean
    (hY : Measurable Y) (_hX : Integrable X μ) :
    (∫ ω, (μ[X | mB.comap Y]) ω ∂μ) = ∫ ω, X ω ∂μ :=
  integral_condExp hY.comap_le

theorem actual_conditional_mean_has_original_integral_on_known_events
    (hY : Measurable Y) (hX : Integrable X μ)
    {A : Set Ω} (hA : MeasurableSet[mB.comap Y] A) :
    (∫ ω in A, (μ[X | mB.comap Y]) ω ∂μ) = ∫ ω in A, X ω ∂μ :=
  setIntegral_condExp hY.comap_le hX hA

theorem actual_take_out_a_function_of_the_observed_random_variable
    {g : B → ℝ} (hg : Measurable g)
    (hProduct : Integrable ((fun ω => g (Y ω)) * X) μ) (hX : Integrable X μ) :
    μ[(fun ω => g (Y ω)) * X | mB.comap Y] =ᵐ[μ]
      (fun ω => g (Y ω)) * μ[X | mB.comap Y] :=
  condExp_mul_of_stronglyMeasurable_left
    (actual_known_observation_function_is_strongly_measurable hg) hProduct hX

theorem actual_conditional_mean_of_a_known_observation
    (hY : Measurable Y) {g : B → ℝ} (hg : Measurable g)
    (hMean : Integrable (fun ω => g (Y ω)) μ) :
    μ[(fun ω => g (Y ω)) | mB.comap Y] = (fun ω => g (Y ω)) :=
  condExp_of_stronglyMeasurable hY.comap_le
    (actual_known_observation_function_is_strongly_measurable hg) hMean

theorem actual_expected_conditional_event_probability_equals_event_probability
    (hY : Measurable Y) {A : Set Ω} (hA : MeasurableSet A) :
    (∫ ω, (μ[A.indicator (fun _ => (1 : ℝ)) | mB.comap Y]) ω ∂μ) = μ.real A :=
  integral_condExp_indicator hY hA

theorem actual_nested_conditional_mean_tower
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂)
    (h₂ : m₂ ≤ inferInstance) (_hX : Integrable X μ) :
    μ[μ[X | m₂] | m₁] =ᵐ[μ] μ[X | m₁] :=
  condExp_condExp_of_le h₁₂ h₂
end Observation

section PolicyExample
open ProbabilityTheory

def actualCost (action : Bool) : ℝ := if action then 2 else 10

def firstActionProbability : Set.Icc (0 : ℝ) 1 :=
  ⟨7 / 10, by constructor <;> norm_num⟩

def secondActionProbability : Set.Icc (0 : ℝ) 1 :=
  ⟨9 / 10, by constructor <;> norm_num⟩

noncomputable def actualPolicyLaw (p : Set.Icc (0 : ℝ) 1) : Measure Bool :=
  bernoulliMeasure true false p

theorem actual_policy_cost_is_integrable (p : Set.Icc (0 : ℝ) 1) :
    Integrable actualCost (actualPolicyLaw p) :=
  integrable_bernoulliMeasure true false p actualCost

theorem actual_policy_cost_mean_is_environment_mean_weighted_by_policy
    (p : Set.Icc (0 : ℝ) 1) :
    (∫ a, actualCost a ∂actualPolicyLaw p) = (p : ℝ) * 2 + (1 - p : ℝ) * 10 := by
  rw [actualPolicyLaw, integral_bernoulliMeasure]
  simp [actualCost, smul_eq_mul]

theorem actual_first_policy_cost_mean :
    (∫ a, actualCost a ∂actualPolicyLaw firstActionProbability) = 22 / 5 := by
  rw [actual_policy_cost_mean_is_environment_mean_weighted_by_policy]
  norm_num [firstActionProbability]

theorem actual_second_policy_cost_mean :
    (∫ a, actualCost a ∂actualPolicyLaw secondActionProbability) = 14 / 5 := by
  rw [actual_policy_cost_mean_is_environment_mean_weighted_by_policy]
  norm_num [secondActionProbability]

theorem actual_policy_change_difference :
    (∫ a, actualCost a ∂actualPolicyLaw secondActionProbability) -
      (∫ a, actualCost a ∂actualPolicyLaw firstActionProbability) = -(8 / 5) := by
  rw [actual_first_policy_cost_mean, actual_second_policy_cost_mean]
  norm_num
end PolicyExample

end SafeLearning.CompleteAppliedConditionalExpectationMaterial31
