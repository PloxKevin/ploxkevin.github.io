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
  have hGP : AEStronglyMeasurable[mB.comap Y] (G-(P:Lp ℝ 2 μ)) μ :=
    (hG.sub (aestronglyMeasurable_condExpL2 (𝕜:=ℝ) hm F)).congr
      (Lp.coeFn_sub G (P:Lp ℝ 2 μ)).symm
  have hint : inner ℝ (F-(P:Lp ℝ 2 μ)) (G-(P:Lp ℝ 2 μ)) = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr (inner_condExpL2_eq_inner_fun hm F (G-(P:Lp ℝ 2 μ))
      hGP).symm
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
  have h : (∫ x : ℝ, x*(pdf (id : ℝ → ℝ) (condDistrib X Y μ y) volume x).toReal) =
      ∫ x : ℝ, (id : ℝ → ℝ) x ∂condDistrib X Y μ y := pdf.integral_mul_eq_integral
  simpa only [actualConditionalDensity,Function.id_def] using h

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

namespace SafeLearning.CompleteAppliedConditionalExpectationMaterial31
section CompleteMeanSquare
variable {Ω B : Type*} [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace B]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem actual_finite_second_moment_is_the_exact_square_integrability_condition
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X μ) :
    MemLp X 2 μ ↔ Integrable (fun ω => (X ω)^2) μ :=
  memLp_two_iff_integrable_sq hX

theorem actual_conditional_mean_minimizes_even_extended_mean_squared_error
    (X : Ω → ℝ) (Y : Ω → B) (hY : Measurable Y) (hX : MemLp X 2 μ)
    (prediction : Ω → ℝ) (hKnown : AEStronglyMeasurable[mB.comap Y] prediction μ) :
    (∫⁻ ω, ENNReal.ofReal ((X ω-(μ[X | mB.comap Y]) ω)^2) ∂μ) ≤
      ∫⁻ ω, ENNReal.ofReal ((X ω-prediction ω)^2) ∂μ := by
  by_cases htop : (∫⁻ ω, ENNReal.ofReal ((X ω-prediction ω)^2) ∂μ)=∞
  · rw [htop]; exact le_top
  have hPredMeas : AEStronglyMeasurable prediction μ := hKnown.mono hY.comap_le
  have hDiffMeas := hX.aestronglyMeasurable.sub hPredMeas
  have hEnorm : (fun ω => ‖(X ω-prediction ω)^2‖ₑ) =
      (fun ω => ENNReal.ofReal ((X ω-prediction ω)^2)) := by
    funext ω; exact Real.enorm_eq_ofReal (sq_nonneg _)
  have hRight : Integrable (fun ω => (X ω-prediction ω)^2) μ := by
    refine ⟨hDiffMeas.pow 2,?_⟩
    rw [hasFiniteIntegral_iff_enorm,hEnorm]
    exact lt_top_iff_ne_top.mpr htop
  have hDiffLP : MemLp (fun ω => X ω-prediction ω) 2 μ :=
    (memLp_two_iff_integrable_sq hDiffMeas).mpr hRight
  have hPredLP : MemLp prediction 2 μ := by
    convert hX.sub hDiffLP using 1
    funext ω
    change prediction ω = X ω-(X ω-prediction ω)
    ring
  have hCondLP : MemLp (μ[X | mB.comap Y]) 2 μ :=
    MemLp.condExp (m:=mB.comap Y) (by norm_num) hX
  have hLeftLP := hX.sub hCondLP
  have hLeft : Integrable (fun ω => (X ω-(μ[X | mB.comap Y]) ω)^2) μ :=
    (memLp_two_iff_integrable_sq hLeftLP.aestronglyMeasurable).mp hLeftLP
  rw [← ofReal_integral_eq_lintegral_ofReal hLeft (ae_of_all _ fun ω => sq_nonneg _),
      ← ofReal_integral_eq_lintegral_ofReal hRight (ae_of_all _ fun ω => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal
    (actual_conditional_mean_minimizes_mean_squared_error X Y hY hX prediction hPredLP hKnown)
end CompleteMeanSquare

section DiscreteConditional
variable {Ω B D : Type*} [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace B]
variable [MeasurableSpace D] [StandardBorelSpace D] [Nonempty D]
variable [Countable D] [MeasurableSingletonClass D]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem actual_discrete_conditional_mean_is_the_countable_probability_mass_sum
    (Z : Ω → D) (Y : Ω → B) (hZ : Measurable Z) (hY : Measurable Y)
    (value : D → ℝ) (hValue : Measurable value)
    (hInt : Integrable (fun ω => value (Z ω)) μ) :
    μ[(fun ω => value (Z ω)) | mB.comap Y] =ᵐ[μ]
      fun ω => ∑' x : D, value x*(condDistrib Z Y μ (Y ω)).real {x} := by
  have hMap : Integrable (fun q : B×D => value q.2)
      (μ.map (fun ω => (Y ω,Z ω))) := by
    exact (integrable_map_measure (hValue.comp measurable_snd).aestronglyMeasurable
      (hY.aemeasurable.prodMk hZ.aemeasurable)).mpr hInt
  have hKernel := hMap.condDistrib_ae hY.aemeasurable hZ.aemeasurable
  have hMean := condExp_ae_eq_integral_condDistrib hY hZ.aemeasurable
    hValue.stronglyMeasurable hInt
  filter_upwards [hMean,hKernel] with ω hmean hint
  rw [hmean,integral_countable hint]
  simp only [smul_eq_mul,mul_comm]
end DiscreteConditional

section PositiveEvent
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem actual_positive_probability_event_has_a_normalized_conditional_law
    (A : Set Ω) (hA : 0 < μ.real A) :
    IsProbabilityMeasure (ProbabilityTheory.cond μ A) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  intro hz
  simp [measureReal_def,hz] at hA

theorem actual_positive_event_mean_has_the_printed_multiplicative_identity
    (X : Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A) (hX : Integrable X μ)
    (hPos : 0 < μ.real A) :
    (∫ ω, X ω*A.indicator (fun _ => (1:ℝ)) ω ∂μ) =
      μ.real A * (∫ ω, X ω ∂ProbabilityTheory.cond μ A) := by
  rw [actual_event_conditioned_mean_is_the_exact_probability_ratio X A hA hX]
  field_simp
end PositiveEvent
end SafeLearning.CompleteAppliedConditionalExpectationMaterial31

namespace SafeLearning.CompleteAppliedConditionalExpectationMaterial31
section FiniteConditionalMean
variable {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem actual_conditional_law_has_finite_first_moment_at_almost_every_observation
    (X : Ω → ℝ) (Y : Ω → B) (hY : Measurable Y) (hX : Integrable X μ) :
    ∀ᵐ y ∂μ.map Y, Integrable (id : ℝ → ℝ) (condDistrib X Y μ y) := by
  have hMap : Integrable (fun q : B×ℝ => q.2) (μ.map (fun ω => (Y ω,X ω))) :=
    (integrable_map_measure measurable_snd.aestronglyMeasurable
      (hY.aemeasurable.prodMk hX.aestronglyMeasurable.aemeasurable)).mpr hX
  exact hMap.condDistrib_ae_map hY.aemeasurable hX.aestronglyMeasurable.aemeasurable
end FiniteConditionalMean
end SafeLearning.CompleteAppliedConditionalExpectationMaterial31

namespace SafeLearning.CompleteAppliedConditionalExpectationMaterial31
section GivenDensityVersion
variable {Ω B : Type*} [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace B]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem actual_any_given_conditional_density_has_the_printed_integral_mean
    (X : Ω → ℝ) (Y : Ω → B) (y : B) (density : ℝ → ℝ≥0∞)
    (hDensity : Measurable density)
    (hLaw : condDistrib X Y μ y = volume.withDensity density) :
    (∫ x : ℝ, x*(density x).toReal) = ∫ x : ℝ, x ∂condDistrib X Y μ y := by
  have hMap : Measure.map (id : ℝ → ℝ) (condDistrib X Y μ y)=volume.withDensity density :=
    by simpa only [Measure.map_id] using hLaw
  letI : HasPDF (id : ℝ → ℝ) (condDistrib X Y μ y) volume :=
    hasPDF_of_map_eq_withDensity aemeasurable_id density hDensity.aemeasurable hMap
  have hPdf : pdf (id : ℝ → ℝ) (condDistrib X Y μ y) volume =ᵐ[volume] density :=
    (pdf.eq_of_map_eq_withDensity density hDensity.aemeasurable).mp hMap
  calc
    (∫ x : ℝ, x*(density x).toReal) =
        ∫ x : ℝ, x*actualConditionalDensity X Y μ y x := by
      apply integral_congr_ae
      filter_upwards [hPdf] with x hx
      simp only [actualConditionalDensity,hx]
    _ = _ := actual_conditional_density_integral_is_the_actual_conditional_law_mean X Y y

theorem actual_given_density_version_defines_the_conditional_mean_after_observation
    (X : Ω → ℝ) (Y : Ω → B) (hY : Measurable Y) (hX : Integrable X μ)
    (density : B → ℝ → ℝ≥0∞) (hDensity : ∀ y, Measurable (density y))
    (hLaw : ∀ᵐ y ∂μ.map Y, condDistrib X Y μ y=volume.withDensity (density y)) :
    μ[X | mB.comap Y] =ᵐ[μ]
      fun ω => ∫ x : ℝ, x*(density (Y ω) x).toReal := by
  have hLawObserved := ae_of_ae_map hY.aemeasurable hLaw
  filter_upwards [actual_conditional_mean_is_the_regular_conditional_law_integral X Y hY hX,
    hLawObserved] with ω hmean hlaw
  rw [hmean]
  exact (actual_any_given_conditional_density_has_the_printed_integral_mean
    X Y (Y ω) (density (Y ω)) (hDensity (Y ω)) hlaw).symm
end GivenDensityVersion

section ExactDiscreteTower
variable {Ω B D : Type*} [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace B]
variable [Countable B] [MeasurableSingletonClass B]
variable [MeasurableSpace D] [StandardBorelSpace D] [Nonempty D]
variable [Countable D] [MeasurableSingletonClass D]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem actual_discrete_weighted_tower_has_the_exact_printed_joint_sum
    (Z : Ω → D) (Y : Ω → B) (hZ : Measurable Z) (hY : Measurable Y)
    (value : D → ℝ) (hValue : Measurable value)
    (hInt : Integrable (fun ω => value (Z ω)) μ) :
    (∑' y : B, (μ.map Y).real {y}*
      (∑' x : D, value x*(condDistrib Z Y μ y).real {x})) =
      (∑' q : B×D, value q.2*(μ.map (fun ω => (Y ω,Z ω))).real {q}) ∧
    (∑' q : B×D, value q.2*(μ.map (fun ω => (Y ω,Z ω))).real {q}) =
      ∫ ω, value (Z ω) ∂μ := by
  have hMap : Integrable (fun q : B×D => value q.2) (μ.map (fun ω => (Y ω,Z ω))) :=
    (integrable_map_measure (hValue.comp measurable_snd).aestronglyMeasurable
      (hY.aemeasurable.prodMk hZ.aemeasurable)).mpr hInt
  have hKernel := hMap.condDistrib_ae_map hY.aemeasurable hZ.aemeasurable
  have hGInt := hMap.integral_condDistrib_map hY.aemeasurable hZ.aemeasurable
  have hMean := condExp_ae_eq_integral_condDistrib hY hZ.aemeasurable
    hValue.stronglyMeasurable hInt
  have hNull : (μ.map Y) {y | ¬Integrable value (condDistrib Z Y μ y)}=0 :=
    ae_iff.mp hKernel
  have hAt (y : B) (hy : (μ.map Y) {y}≠0) : Integrable value (condDistrib Z Y μ y) := by
    by_contra hnot
    have hsub : {y} ⊆ {z | ¬Integrable value (condDistrib Z Y μ z)} := by
      intro z hz; have he : z=y := Set.mem_singleton_iff.mp hz; subst z; exact hnot
    apply hy
    exact le_antisymm ((measure_mono hsub).trans_eq hNull) (zero_le _)
  have hMarginal :
      (∑' y : B, (μ.map Y).real {y}*
        (∑' x : D, value x*(condDistrib Z Y μ y).real {x})) =
        ∫ ω, value (Z ω) ∂μ := by
    calc
      _ = ∑' y : B, (μ.map Y).real {y}*(∫ x : D, value x ∂condDistrib Z Y μ y) := by
        apply tsum_congr
        intro y
        by_cases hy : (μ.map Y) {y}=0
        · simp [measureReal_def,hy]
        · rw [integral_countable (hAt y hy)]
          simp only [smul_eq_mul,mul_comm]
      _ = ∫ y : B, (∫ x : D, value x ∂condDistrib Z Y μ y) ∂μ.map Y := by
        simpa only [smul_eq_mul] using (integral_countable hGInt).symm
      _ = ∫ ω, (∫ x : D, value x ∂condDistrib Z Y μ (Y ω)) ∂μ :=
        integral_map hY.aemeasurable hGInt.aestronglyMeasurable
      _ = ∫ ω, (μ[(fun ω => value (Z ω)) | mB.comap Y]) ω ∂μ :=
        integral_congr_ae hMean.symm
      _ = _ := integral_condExp hY.comap_le
  have hJoint :
      (∑' q : B×D, value q.2*(μ.map (fun ω => (Y ω,Z ω))).real {q}) =
        ∫ ω, value (Z ω) ∂μ := by
    calc
      _ = ∫ q : B×D, value q.2 ∂μ.map (fun ω => (Y ω,Z ω)) := by
        simpa only [smul_eq_mul,mul_comm] using (integral_countable hMap).symm
      _ = _ := integral_map (hY.aemeasurable.prodMk hZ.aemeasurable)
        (hValue.comp measurable_snd).aestronglyMeasurable
  exact ⟨hMarginal.trans hJoint.symm,hJoint⟩
end ExactDiscreteTower
end SafeLearning.CompleteAppliedConditionalExpectationMaterial31
