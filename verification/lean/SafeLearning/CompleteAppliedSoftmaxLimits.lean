import SafeLearning.CompleteAppliedTemperatureSoftmax

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set Filter
namespace SafeLearning.CompleteAppliedSoftmaxLimits
open SafeLearning.CompleteAppliedTemperatureSoftmax
open SafeLearning.CompleteFoundationsExponentialLesson

variable {n : ℕ} [NeZero n]

def actualMaximizers (scores : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => scores i=actualMaximum scores)

theorem actual_maximizing_action_set_is_nonempty (scores : Fin n → ℝ) :
    0<(actualMaximizers scores).card := by
  classical
  obtain ⟨⟨i,hi⟩,_⟩ := actual_finite_maximum_is_attained_and_bounds_every_entry scores
  apply Finset.card_pos.mpr
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi.symm⟩⟩

theorem actual_softmax_masses_equal_the_maximum_shifted_exponential_ratios
    (scores : Fin n → ℝ) (temperature : ℝ) (i : Fin n) :
    (actualTemperatureLaw scores temperature i).toReal=
      Real.exp ((scores i-actualMaximum scores)/temperature)/
        (∑ j,Real.exp ((scores j-actualMaximum scores)/temperature)) := by
  rw [actual_temperature_law_has_the_literal_normalized_exponential_masses]
  have he (j : Fin n) : Real.exp ((scores j-actualMaximum scores)/temperature)=
      Real.exp (scores j/temperature)/Real.exp (actualMaximum scores/temperature) := by
    rw [sub_div,Real.exp_sub]
  simp only [he,← Finset.sum_div]
  unfold actualPartition
  field_simp

theorem actual_shifted_exponential_mass_has_the_limit_one_exactly_at_maximizers
    (scores : Fin n → ℝ) (i : Fin n) :
    Tendsto (fun temperature : ℝ => Real.exp ((scores i-actualMaximum scores)/temperature))
      (𝓝[>] (0:ℝ)) (𝓝 (if scores i=actualMaximum scores then 1 else 0)) := by
  classical
  by_cases hi : scores i=actualMaximum scores
  · simp only [hi,sub_self,zero_div,Real.exp_zero,ite_true]
    exact tendsto_const_nhds
  · have hm := (actual_finite_maximum_is_attained_and_bounds_every_entry scores).2 i
    have hgap : 0<actualMaximum scores-scores i := sub_pos.mpr (lt_of_le_of_ne hm hi)
    have hinv : Tendsto (fun temperature : ℝ => -(temperature⁻¹)) (𝓝[>] 0) atBot :=
      tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero
    have hmul := hinv.const_mul_atBot hgap
    have harg : Tendsto (fun temperature : ℝ => (scores i-actualMaximum scores)/temperature)
        (𝓝[>] 0) atBot := by
      convert hmul using 1
      funext temperature
      rw [div_eq_mul_inv]
      ring
    simpa only [hi,ite_false,Function.comp_def] using Real.tendsto_exp_atBot.comp harg

theorem actual_softmax_tends_to_uniform_mass_on_all_and_only_maximizers
    (scores : Fin n → ℝ) (i : Fin n) :
    Tendsto (fun temperature => (actualTemperatureLaw scores temperature i).toReal)
      (𝓝[>] (0:ℝ))
      (𝓝 (if scores i=actualMaximum scores then 1/(actualMaximizers scores).card else 0)) := by
  classical
  have hsum := tendsto_finset_sum Finset.univ
    (fun j _ => actual_shifted_exponential_mass_has_the_limit_one_exactly_at_maximizers scores j)
  have hcount : (∑ j : Fin n,if scores j=actualMaximum scores then (1:ℝ) else 0)=
      (actualMaximizers scores).card := by
    exact Finset.sum_boole (fun j => scores j=actualMaximum scores) Finset.univ
  rw [hcount] at hsum
  have hc : ((actualMaximizers scores).card:ℝ)≠0 := by
    exact_mod_cast (actual_maximizing_action_set_is_nonempty scores).ne'
  have hquot : ContinuousAt (fun pair : ℝ×ℝ => pair.1/pair.2)
      (if scores i=actualMaximum scores then 1 else 0,((actualMaximizers scores).card:ℝ)) :=
    continuousAt_fst.div continuousAt_snd hc
  have hr := hquot.tendsto.comp
    ((actual_shifted_exponential_mass_has_the_limit_one_exactly_at_maximizers scores i).prodMk_nhds hsum)
  have he : (fun temperature => (actualTemperatureLaw scores temperature i).toReal)=
      (fun temperature => Real.exp ((scores i-actualMaximum scores)/temperature)/
        (∑ j,Real.exp ((scores j-actualMaximum scores)/temperature))) :=
    funext (fun temperature => actual_softmax_masses_equal_the_maximum_shifted_exponential_ratios scores temperature i)
  rw [he]
  by_cases hi : scores i=actualMaximum scores <;>
    simpa only [hi,ite_true,ite_false,zero_div,Function.comp_def] using hr

end SafeLearning.CompleteAppliedSoftmaxLimits
