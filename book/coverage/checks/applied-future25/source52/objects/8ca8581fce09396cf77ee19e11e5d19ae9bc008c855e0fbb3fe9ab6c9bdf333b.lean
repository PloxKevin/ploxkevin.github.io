import SafeLearning.CompleteAppliedSoftmaxLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory
namespace SafeLearning.CompleteAppliedSoftmaxConsequences
open SafeLearning.CompleteAppliedTemperatureSoftmax

variable {n : ℕ} [NeZero n]

theorem actual_softmax_mass_is_the_literal_exponential_of_score_minus_soft_value
    (scores : Fin n → ℝ) (temperature : ℝ) (ht : 0<temperature) (i : Fin n) :
    (actualTemperatureLaw scores temperature i).toReal=
      Real.exp ((scores i-actualTemperatureValue scores temperature)/temperature) := by
  rw [actual_temperature_law_has_the_literal_normalized_exponential_masses]
  have he : (scores i-actualTemperatureValue scores temperature)/temperature=
      scores i/temperature-Real.log (actualPartition scores temperature) := by
    unfold actualTemperatureValue
    field_simp
  rw [he,Real.exp_sub,Real.exp_log (actual_partition_is_strictly_positive scores temperature)]

theorem actual_temperature_scaled_score_exponential_tends_to_one_at_high_temperature
    (scores : Fin n → ℝ) (i : Fin n) :
    Tendsto (fun temperature : ℝ => Real.exp (scores i/temperature)) atTop (𝓝 1) := by
  have hi : Tendsto (fun temperature : ℝ => temperature⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hs : Tendsto (fun temperature : ℝ => scores i/temperature) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul (scores i)
  simpa only [Real.exp_zero,Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp hs

theorem actual_softmax_tends_to_the_uniform_law_at_high_temperature
    (scores : Fin n → ℝ) (i : Fin n) :
    Tendsto (fun temperature => (actualTemperatureLaw scores temperature i).toReal)
      atTop (𝓝 (1/(n:ℝ))) := by
  have hsum := tendsto_finsetSum Finset.univ
    (fun j _ => actual_temperature_scaled_score_exponential_tends_to_one_at_high_temperature scores j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hsum
  have hn : (n:ℝ)≠0 := by exact_mod_cast NeZero.ne n
  have hc : ContinuousAt (fun pair : ℝ×ℝ => pair.1/pair.2) (1,(n:ℝ)) :=
    continuousAt_fst.div continuousAt_snd hn
  have hr := hc.tendsto.comp
    ((actual_temperature_scaled_score_exponential_tends_to_one_at_high_temperature scores i).prodMk_nhds hsum)
  have he : (fun temperature => (actualTemperatureLaw scores temperature i).toReal)=
      (fun temperature => Real.exp (scores i/temperature)/
        (∑ j,Real.exp (scores j/temperature))) := by
    funext temperature
    exact actual_temperature_law_has_the_literal_normalized_exponential_masses scores temperature i
  rw [he]
  simpa only [Function.comp_def] using hr

end SafeLearning.CompleteAppliedSoftmaxConsequences
