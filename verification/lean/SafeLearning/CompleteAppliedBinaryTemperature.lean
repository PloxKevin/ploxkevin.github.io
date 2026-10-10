import SafeLearning.CompleteAppliedTemperatureSoftmax

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory InformationTheory Set Filter
namespace SafeLearning.CompleteAppliedBinaryTemperature
open SafeLearning.CompleteAppliedTemperatureSoftmax
open SafeLearning.CompleteAppliedFiniteEntropy SafeLearning.CompleteAppliedInformation
open SafeLearning.CompleteFoundationsExponentialLesson

def actualBinaryScores : Fin 2 → ℝ := ![0,1]
def actualUniformBinaryLaw : PMF (Fin 2) := PMF.uniformOfFintype (Fin 2)

theorem actual_binary_softmax_and_soft_value_have_the_literal_formulas (temperature : ℝ) :
    (actualTemperatureLaw actualBinaryScores temperature 0).toReal=
      1/(1+Real.exp (1/temperature)) ∧
      (actualTemperatureLaw actualBinaryScores temperature 1).toReal=
        Real.exp (1/temperature)/(1+Real.exp (1/temperature)) ∧
      actualTemperatureValue actualBinaryScores temperature=
        temperature*Real.log (1+Real.exp (1/temperature)) := by
  rw [actual_temperature_law_has_the_literal_normalized_exponential_masses,
    actual_temperature_law_has_the_literal_normalized_exponential_masses]
  norm_num [actualPartition,actualBinaryScores,Fin.sum_univ_two,actualTemperatureValue]

theorem actual_binary_soft_value_maximum_bounds_and_limit :
    (∀ temperature>0, 1 ≤ actualTemperatureValue actualBinaryScores temperature ∧
      actualTemperatureValue actualBinaryScores temperature ≤ 1+temperature*Real.log 2) ∧
      Tendsto (actualTemperatureValue actualBinaryScores) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hm : actualMaximum actualBinaryScores=1 := by
    obtain ⟨⟨i,hi⟩,hb⟩ := actual_finite_maximum_is_attained_and_bounds_every_entry actualBinaryScores
    have hl : 1≤actualMaximum actualBinaryScores := by simpa [actualBinaryScores] using hb 1
    have hu : actualMaximum actualBinaryScores≤1 := by rw [hi];fin_cases i <;> norm_num [actualBinaryScores]
    exact le_antisymm hu hl
  simpa only [hm,Nat.cast_ofNat] using actual_temperature_value_has_the_source_maximum_gap_and_true_zero_temperature_limit actualBinaryScores

theorem actual_binary_softmax_negative_exponential_form (temperature : ℝ) :
    (actualTemperatureLaw actualBinaryScores temperature 0).toReal=
      Real.exp (-1/temperature)/(1+Real.exp (-1/temperature)) ∧
      (actualTemperatureLaw actualBinaryScores temperature 1).toReal=
        1/(1+Real.exp (-1/temperature)) := by
  have he : Real.exp (-1/temperature)=(Real.exp (1/temperature))⁻¹ := by
    rw [neg_div,Real.exp_neg]
  rw [actual_binary_softmax_and_soft_value_have_the_literal_formulas temperature |>.1,
    (actual_binary_softmax_and_soft_value_have_the_literal_formulas temperature).2.1,he]
  have hp := Real.exp_pos (1/temperature)
  constructor <;> field_simp <;> ring

theorem actual_binary_softmax_tends_to_the_actual_greedy_point_mass :
    Tendsto (fun temperature => (actualTemperatureLaw actualBinaryScores temperature 0).toReal)
      (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      Tendsto (fun temperature => (actualTemperatureLaw actualBinaryScores temperature 1).toReal)
        (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hinv : Tendsto (fun temperature : ℝ => -(temperature⁻¹)) (𝓝[>] 0) atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero
  have he : Tendsto (fun temperature : ℝ => Real.exp (-1/temperature)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [neg_div,one_div,Function.comp_def] using Real.tendsto_exp_atBot.comp hinv
  constructor
  · have hc : ContinuousAt (fun x : ℝ => x/(1+x)) 0 :=
      continuousAt_id.div (continuousAt_const.add continuousAt_id) (by norm_num)
    have h := hc.tendsto.comp he
    have hx : (fun temperature => (actualTemperatureLaw actualBinaryScores temperature 0).toReal)=
        (fun temperature => Real.exp (-1/temperature)/(1+Real.exp (-1/temperature))) :=
      funext (fun temperature => (actual_binary_softmax_negative_exponential_form temperature).1)
    rw [hx]
    simpa only [Function.comp_def,add_zero,zero_div] using h
  · have hc : ContinuousAt (fun x : ℝ => 1/(1+x)) 0 :=
      continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)
    have h := hc.tendsto.comp he
    have hx : (fun temperature => (actualTemperatureLaw actualBinaryScores temperature 1).toReal)=
        (fun temperature => 1/(1+Real.exp (-1/temperature))) :=
      funext (fun temperature => (actual_binary_softmax_negative_exponential_form temperature).2)
    rw [hx]
    simpa only [Function.comp_def,add_zero,div_one] using h

theorem actual_uniform_binary_entropy_expected_score_and_true_variational_identity
    (temperature : ℝ) (ht : 0 < temperature) :
    (∫ i,actualBinaryScores i ∂actualUniformBinaryLaw.toMeasure)=1/2 ∧
      shannonEntropy actualUniformBinaryLaw=Real.log 2 ∧
      actualTemperatureObjective actualBinaryScores temperature actualUniformBinaryLaw=
        1/2+temperature*Real.log 2 ∧
      (1/2+temperature*Real.log 2)=actualTemperatureValue actualBinaryScores temperature-
        temperature*(klDiv actualUniformBinaryLaw.toMeasure
          (actualTemperatureLaw actualBinaryScores temperature).toMeasure).toReal := by
  have hm : ∀ i : Fin 2,(actualUniformBinaryLaw i).toReal=1/2 := by
    intro i
    simpa only [actualUniformBinaryLaw,inv_eq_one_div,Nat.cast_ofNat] using actual_uniform_mass i
  have he : (∫ i,actualBinaryScores i ∂actualUniformBinaryLaw.toMeasure)=1/2 := by
    rw [PMF.integral_eq_sum]
    norm_num [Fin.sum_univ_two,hm,actualBinaryScores]
  have hh : shannonEntropy actualUniformBinaryLaw=Real.log 2 := by
    rw [actual_entropy_sum]
    simp only [hm,Fin.sum_univ_two]
    rw [Real.log_div (by norm_num : (1:ℝ)≠0) (by norm_num : (2:ℝ)≠0),Real.log_one]
    ring
  have ho : actualTemperatureObjective actualBinaryScores temperature actualUniformBinaryLaw=
      1/2+temperature*Real.log 2 := by rw [actualTemperatureObjective,he,hh]
  refine ⟨he,hh,ho,?_⟩
  have h := actual_expected_score_plus_temperature_entropy_is_value_minus_true_kl
    actualBinaryScores temperature ht actualUniformBinaryLaw
  rw [ho] at h
  linarith

theorem actual_full_support_softmax_cannot_assign_zero_probability_to_an_unsafe_action
    {n : ℕ} [NeZero n] (scores : Fin n → ℝ) (temperature : ℝ) (unsafeSet : Set (Fin n))
    (action : Fin n) (ha : action ∈ unsafeSet) :
    0 < (actualTemperatureLaw scores temperature).toMeasure unsafeSet := by
  have hp : 0 < (actualTemperatureLaw scores temperature).toMeasure {action} := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton action)]
    exact pos_iff_ne_zero.mpr (actual_temperature_law_has_full_support_and_positive_real_masses scores temperature action).1
  exact hp.trans_le (measure_mono (singleton_subset_iff.mpr ha))

end SafeLearning.CompleteAppliedBinaryTemperature
