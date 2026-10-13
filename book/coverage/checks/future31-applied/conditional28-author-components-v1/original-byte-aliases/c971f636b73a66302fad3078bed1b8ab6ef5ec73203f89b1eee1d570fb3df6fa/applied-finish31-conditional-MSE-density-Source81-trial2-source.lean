import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Distributions.Bernoulli

open MeasureTheory
open scoped ENNReal

namespace SafeLearning.CompleteAppliedConditionalExpectationMaterial31

section Observation
variable {Ω B : Type*} [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace B]
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
    (h₂ : m₂ ≤ mΩ) (_hX : Integrable X μ) :
    μ[μ[X | m₂] | m₁] =ᵐ[μ] μ[X | m₁] :=
  condExp_condExp_of_le h₁₂ h₂
end Observation

section PolicyExample
open ProbabilityTheory

def actualCost (action : Bool) : ℝ := if action then 2 else 10

noncomputable def firstActionProbability : Set.Icc (0 : ℝ) 1 :=
  ⟨7 / 10, by constructor <;> norm_num⟩

noncomputable def secondActionProbability : Set.Icc (0 : ℝ) 1 :=
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

noncomputable section
open Set Filter ProbabilityTheory
open scoped Topology
namespace SafeLearning.CompleteAppliedConditionalExpectationMaterial31

section MissingMeanSquare
variable {Ω B : Type*} [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace B]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem actual_conditional_mean_really_is_a_function_of_the_observation
    (X : Ω → ℝ) (Y : Ω → B) :
    ∃ g : B → ℝ, Measurable g ∧ μ[X | mB.comap Y] = g ∘ Y := by
  exact (stronglyMeasurable_condExp (μ:=μ) (m:=mB.comap Y) (f:=X)).measurable.exists_eq_measurable_comp

private theorem actual_L2_norm_square_is_the_mean_square (f : Lp ℝ 2 μ) :
    ‖f‖^2 = ∫ ω, (f ω)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  congr 1
  funext ω
  simp [RCLike.inner_apply,pow_two]

theorem actual_conditional_mean_minimizes_mean_squared_error
    (X : Ω → ℝ) (Y : Ω → B) (hY : Measurable Y)
    (hX : MemLp X 2 μ) (prediction : Ω → ℝ)
    (hPred : MemLp prediction 2 μ)
    (hKnown : AEStronglyMeasurable[mB.comap Y] prediction μ) :
    (∫ ω, (X ω-(μ[X | mB.comap Y]) ω)^2 ∂μ) ≤
      ∫ ω, (X ω-prediction ω)^2 ∂μ := by
  have hm : mB.comap Y ≤ mΩ := hY.comap_le
  letI : Fact (mB.comap Y ≤ mΩ) := ⟨hm⟩
  let F : Lp ℝ 2 μ := hX.toLp X
  let G : Lp ℝ 2 μ := hPred.toLp prediction
  let P : lpMeas ℝ ℝ (mB.comap Y) 2 μ := condExpL2 ℝ ℝ hm F
  have hG : AEStronglyMeasurable[mB.comap Y] G μ := hKnown.congr hPred.coeFn_toLp.symm
  have hmem : G ∈ lpMeas ℝ ℝ (mB.comap Y) 2 μ := mem_lpMeas_iff_aestronglyMeasurable.mpr hG
  have hint : inner ℝ (F-(P:Lp ℝ 2 μ)) (G-(P:Lp ℝ 2 μ)) = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr (inner_condExpL2_eq_inner_fun hm F (G-(P:Lp ℝ 2 μ))
      (hG.sub (aestronglyMeasurable_condExpL2 hm F))).symm
  have hn : ‖F-(P:Lp ℝ 2 μ)‖^2 ≤ ‖F-G‖^2 := by
    have h := norm_sub_sq_real (F-(P:Lp ℝ 2 μ)) (G-(P:Lp ℝ 2 μ))
    rw [hint] at h
    have he : (F-(P:Lp ℝ 2 μ))-(G-(P:Lp ℝ 2 μ))=F-G := by abel
    rw [he] at h
    nlinarith [sq_nonneg ‖G-(P:Lp ℝ 2 μ)‖]
  rw [actual_L2_norm_square_is_the_mean_square,actual_L2_norm_square_is_the_mean_square] at hn
  have hP : (P:Ω → ℝ) =ᵐ[μ] μ[X | mB.comap Y] := hX.condExpL2_ae_eq_condExp hm
  have hleft : (fun ω => ((F-(P:Lp ℝ 2 μ)) ω)^2) =ᵐ[μ]
      (fun ω => (X ω-(μ[X | mB.comap Y]) ω)^2) := by
    filter_upwards [Lp.coeFn_sub F (P:Lp ℝ 2 μ),hX.coeFn_toLp,hP] with ω hsub hx hp
    simp only [Pi.sub_apply] at hsub
    rw [hsub]
    change (F ω-(P:Ω → ℝ) ω)^2 = _
    rw [show F ω = X ω from hx,hp]
  have hright : (fun ω => ((F-G) ω)^2) =ᵐ[μ] (fun ω => (X ω-prediction ω)^2) := by
    filter_upwards [Lp.coeFn_sub F G,hX.coeFn_toLp,hPred.coeFn_toLp] with ω hsub hx hg
    simp only [Pi.sub_apply] at hsub
    rw [hsub]
    change (F ω-G ω)^2 = _
    rw [show F ω = X ω from hx,show G ω = prediction ω from hg]
  simpa only [integral_congr_ae hleft,integral_congr_ae hright] using hn

end MissingMeanSquare

section ActualKernel
variable {Ω B : Type*} [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace B]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem actual_conditional_mean_is_the_regular_conditional_law_integral
    (X : Ω → ℝ) (Y : Ω → B) (hY : Measurable Y) (hX : Integrable X μ) :
    μ[X | mB.comap Y] =ᵐ[μ]
      fun ω => ∫ x : ℝ, x ∂condDistrib X Y μ (Y ω) :=
  condExp_ae_eq_integral_condDistrib' hY hX

noncomputable def actualConditionalDensity
    (X : Ω → ℝ) (Y : Ω → B) (μ : Measure Ω) [IsProbabilityMeasure μ] (y : B) (x : ℝ) : ℝ :=
  (pdf id (condDistrib X Y μ y) volume x).toReal

theorem actual_conditional_density_integral_is_the_actual_conditional_law_mean
    (X : Ω → ℝ) (Y : Ω → B) (y : B)
    [HasPDF (id : ℝ → ℝ) (condDistrib X Y μ y) volume] :
    (∫ x : ℝ, x*actualConditionalDensity X Y μ y x) =
      ∫ x : ℝ, x ∂condDistrib X Y μ y := by
  simpa only [actualConditionalDensity,Function.id_def] using
    (pdf.integral_mul_eq_integral (X:=(id : ℝ → ℝ)) (ℙ:=condDistrib X Y μ y))

theorem actual_conditional_mean_is_the_density_integral_where_a_density_exists
    (X : Ω → ℝ) (Y : Ω → B) (hY : Measurable Y) (hX : Integrable X μ)
    (hDensity : ∀ᵐ y ∂μ.map Y, HasPDF (id : ℝ → ℝ) (condDistrib X Y μ y) volume) :
    μ[X | mB.comap Y] =ᵐ[μ]
      fun ω => ∫ x : ℝ, x*actualConditionalDensity X Y μ (Y ω) x := by
  have hd : ∀ᵐ ω ∂μ, HasPDF (id : ℝ → ℝ) (condDistrib X Y μ (Y ω)) volume :=
    ae_of_ae_map hY.aemeasurable hDensity
  filter_upwards [actual_conditional_mean_is_the_regular_conditional_law_integral X Y hY hX,hd] with ω hmean hpdf
  letI := hpdf
  rw [hmean]
  exact (actual_conditional_density_integral_is_the_actual_conditional_law_mean X Y (Y ω)).symm

end ActualKernel

section EventMean
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem actual_event_conditioned_mean_is_the_exact_probability_ratio
    (X : Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A) (_hX : Integrable X μ) :
    (∫ ω, X ω ∂ProbabilityTheory.cond μ A) =
      (∫ ω, X ω * A.indicator (fun _ => (1:ℝ)) ω ∂μ) / μ.real A := by
  have he : (fun ω => X ω * A.indicator (fun _ => (1:ℝ)) ω) = A.indicator X := by
    funext ω
    by_cases h : ω∈A <;> simp [h]
  rw [he,integral_indicator hA]
  simp only [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,measureReal_def,smul_eq_mul]
  ring

end EventMean
end SafeLearning.CompleteAppliedConditionalExpectationMaterial31
