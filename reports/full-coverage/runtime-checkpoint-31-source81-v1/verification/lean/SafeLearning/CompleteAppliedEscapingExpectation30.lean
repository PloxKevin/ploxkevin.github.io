import Mathlib.Probability.HasLaw
import SafeLearning.CompleteAppliedUniformDefinitions
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace SafeLearning.CompleteAppliedEscapingExpectation30
open CompleteAppliedUniformDefinitions

-- Natural index n denotes the source's positive index n+1.
def shrinkingSpike (n : ℕ) : ℝ → ℝ :=
  (Iio (1 / ((n : ℝ) + 1))).indicator (fun _ => (n : ℝ) + 1)

def unitUniform : Measure ℝ := actualUniformLaw 0 1

instance : IsProbabilityMeasure unitUniform :=
  actual_uniform_law_is_a_probability_measure 0 1 (by norm_num)

theorem actual_spike_is_measurable (n : ℕ) : Measurable (shrinkingSpike n) :=
  measurable_const.indicator measurableSet_Iio

theorem actual_spike_is_nonnegative (n : ℕ) (u : ℝ) : 0 ≤ shrinkingSpike n u := by
  by_cases h : u ∈ Iio (1 / ((n : ℝ) + 1))
  · simp only [shrinkingSpike, indicator_of_mem h]
    positivity
  · simp only [shrinkingSpike, indicator_of_notMem h, le_refl]

theorem actual_spike_is_integrable (n : ℕ) : Integrable (shrinkingSpike n) unitUniform :=
  (integrable_const ((n : ℝ) + 1)).indicator measurableSet_Iio

theorem actual_uniform_strict_unit_cdf (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) :
    unitUniform.real (Iio c) = c := by
  rw [unitUniform, measureReal_def,
    actual_uniform_probability_is_length_ratio 0 1 (by norm_num) (Iio c) measurableSet_Iio]
  have he : Iio c ∩ Icc (0 : ℝ) 1 = Ico (0 : ℝ) c := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · intro h
      exact ⟨h.2.1, h.1⟩
    · intro h
      exact ⟨h.2, h.1, le_trans h.2.le hc.2⟩
  rw [he, Real.volume_Ico]
  norm_num
  exact hc.1

theorem actual_every_positive_index_spike_has_mean_one (n : ℕ) :
    (∫ u, shrinkingSpike n u ∂unitUniform) = 1 := by
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hc : 1 / ((n : ℝ) + 1) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_iff₀ hden).mpr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  rw [shrinkingSpike, integral_indicator_const _ measurableSet_Iio,
    actual_uniform_strict_unit_cdf _ hc, smul_eq_mul]
  exact one_div_mul_cancel hden.ne'

theorem actual_unit_uniform_input_is_positive_almost_surely :
    ∀ᵐ u ∂unitUniform, 0 < u := by
  have hz : unitUniform (Iic (0 : ℝ)) = 0 := by
    rw [unitUniform, actual_uniform_probability_is_length_ratio 0 1 (by norm_num)
      (Iic (0 : ℝ)) measurableSet_Iic]
    have he : Iic (0 : ℝ) ∩ Icc (0 : ℝ) 1 = {0} := by
      ext u
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_singleton_iff]
      constructor
      · intro h
        exact le_antisymm h.1 h.2.1
      · intro h
        subst u
        norm_num
    rw [he, measure_singleton]
    simp
  have he : {u : ℝ | ¬ 0 < u} = Iic (0 : ℝ) := by
    ext u
    simp
  rw [ae_iff, he]
  exact hz

theorem actual_each_positive_input_has_an_eventually_zero_spike (u : ℝ) (hu : 0 < u) :
    ∀ᶠ n : ℕ in atTop, shrinkingSpike n u = 0 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1/u)
  filter_upwards [eventually_ge_atTop k] with n hn
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hnu : 1/u < (n : ℝ) + 1 := by linarith
  have hp : 1 < ((n : ℝ) + 1) * u := (div_lt_iff₀ hu).mp hnu
  have hs : 1 / ((n : ℝ) + 1) < u := (div_lt_iff₀ hden).mpr (by nlinarith)
  exact indicator_of_notMem (show u ∉ Iio (1 / ((n : ℝ) + 1)) from not_lt.mpr hs.le) _

theorem actual_spikes_tend_to_zero_for_every_positive_input (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n => shrinkingSpike n u) atTop (𝓝 0) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
  filter_upwards [actual_each_positive_input_has_an_eventually_zero_spike u hu] with n hn
  exact hn.symm

theorem actual_spikes_tend_to_zero_almost_surely :
    ∀ᵐ u ∂unitUniform, Tendsto (fun n => shrinkingSpike n u) atTop (𝓝 0) := by
  filter_upwards [actual_unit_uniform_input_is_positive_almost_surely] with u hu
  exact actual_spikes_tend_to_zero_for_every_positive_input u hu

theorem actual_no_integrable_function_dominates_every_spike_almost_surely :
    ¬ ∃ Y : ℝ → ℝ, Integrable Y unitUniform ∧
      ∀ n, ∀ᵐ u ∂unitUniform, shrinkingSpike n u ≤ Y u := by
  rintro ⟨Y, hY, hbound⟩
  have hnorm : ∀ n, ∀ᵐ u ∂unitUniform, ‖shrinkingSpike n u‖ ≤ Y u := by
    intro n
    filter_upwards [hbound n] with u hu
    simpa only [Real.norm_eq_abs, abs_of_nonneg (actual_spike_is_nonnegative n u)] using hu
  have hlim := tendsto_integral_of_dominated_convergence Y
    (fun n => (actual_spike_is_measurable n).aestronglyMeasurable) hY hnorm
    actual_spikes_tend_to_zero_almost_surely
  have hzero : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [actual_every_positive_index_spike_has_mean_one, integral_zero] using hlim
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  norm_num at hbad


-- Pull the counterexample back to any probability space carrying the literal
-- uniform random variable. The dominating Y may depend on the original omega.
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : Ω → ℝ}

theorem actual_uniform_random_variable_has_probability_source_measure
    (hU : HasLaw U unitUniform μ) : IsProbabilityMeasure μ :=
  hU.isProbabilityMeasure

theorem actual_uniform_random_variable_spikes_are_integrable
    (hU : HasLaw U unitUniform μ) (n : ℕ) :
    Integrable (fun ω => shrinkingSpike n (U ω)) μ := by
  simpa only [Function.comp_def] using
    hU.integrable_comp (actual_spike_is_integrable n)

theorem actual_uniform_random_variable_spikes_have_mean_one
    (hU : HasLaw U unitUniform μ) (n : ℕ) :
    (∫ ω, shrinkingSpike n (U ω) ∂μ) = 1 := by
  change (∫ ω, (shrinkingSpike n ∘ U) ω ∂μ) = 1
  rw [hU.integral_comp (actual_spike_is_measurable n).aestronglyMeasurable]
  exact actual_every_positive_index_spike_has_mean_one n

theorem actual_uniform_random_variable_is_positive_almost_surely
    (hU : HasLaw U unitUniform μ) : ∀ᵐ ω ∂μ, 0 < U ω := by
  have hp : ∀ᵐ u ∂μ.map U, 0 < u := by
    rw [hU.map_eq]
    exact actual_unit_uniform_input_is_positive_almost_surely
  exact (ae_map_iff hU.aemeasurable
    (show MeasurableSet {u : ℝ | 0 < u} from measurableSet_Ioi)).mp hp

theorem actual_uniform_random_variable_spikes_tend_to_zero_almost_surely
    (hU : HasLaw U unitUniform μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => shrinkingSpike n (U ω)) atTop (𝓝 0) := by
  filter_upwards [actual_uniform_random_variable_is_positive_almost_surely hU] with ω hω
  exact actual_spikes_tend_to_zero_for_every_positive_input (U ω) hω

theorem actual_no_integrable_original_space_variable_dominates_every_spike
    (hU : HasLaw U unitUniform μ) :
    ¬ ∃ Y : Ω → ℝ, Integrable Y μ ∧
      ∀ n, ∀ᵐ ω ∂μ, shrinkingSpike n (U ω) ≤ Y ω := by
  rintro ⟨Y, hY, hbound⟩
  have hnorm : ∀ n, ∀ᵐ ω ∂μ, ‖shrinkingSpike n (U ω)‖ ≤ Y ω := by
    intro n
    filter_upwards [hbound n] with ω hω
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (actual_spike_is_nonnegative n (U ω))] using hω
  have hlim := tendsto_integral_of_dominated_convergence Y
    (fun n => (actual_uniform_random_variable_spikes_are_integrable hU n).aestronglyMeasurable)
    hY hnorm (actual_uniform_random_variable_spikes_tend_to_zero_almost_surely hU)
  have hz : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [actual_uniform_random_variable_spikes_have_mean_one hU, integral_zero] using hlim
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  norm_num at hbad

-- Exact printed positive-index formula: n = 0 is outside its source scope.
def sourcePositiveSpike (n : ℕ) : ℝ → ℝ :=
  (Iio (1 / (n : ℝ))).indicator (fun _ => (n : ℝ))

theorem actual_printed_positive_index_equals_the_shifted_sequence
    (n : ℕ) (hn : 1 ≤ n) : sourcePositiveSpike n = shrinkingSpike (n - 1) := by
  have hN : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hR : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hN
  simp only [sourcePositiveSpike, shrinkingSpike, hR]

theorem actual_printed_spike_has_mean_one_at_every_positive_index
    (hU : HasLaw U unitUniform μ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ ω, sourcePositiveSpike n (U ω) ∂μ) = 1 := by
  rw [actual_printed_positive_index_equals_the_shifted_sequence n hn]
  exact actual_uniform_random_variable_spikes_have_mean_one hU (n - 1)

theorem actual_no_integrable_variable_dominates_all_printed_positive_spikes
    (hU : HasLaw U unitUniform μ) :
    ¬ ∃ Y : Ω → ℝ, Integrable Y μ ∧
      ∀ n, 1 ≤ n → ∀ᵐ ω ∂μ, sourcePositiveSpike n (U ω) ≤ Y ω := by
  rintro ⟨Y, hY, hbound⟩
  apply actual_no_integrable_original_space_variable_dominates_every_spike hU
  refine ⟨Y, hY, ?_⟩
  intro n
  have hb := hbound (n + 1) (by omega)
  simpa only [sourcePositiveSpike, shrinkingSpike, Nat.cast_add, Nat.cast_one] using hb


theorem actual_printed_spikes_are_eventually_zero_at_every_positive_input
    (u : ℝ) (hu : 0 < u) :
    ∀ᶠ n : ℕ in atTop, sourcePositiveSpike n u = 0 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1/u)
  filter_upwards [eventually_ge_atTop k] with n hn
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
  have hnu : 1/u < (n : ℝ) := lt_of_lt_of_le hk hkn
  have hden : 0 < (n : ℝ) := lt_trans (one_div_pos.mpr hu) hnu
  have hp : 1 < (n : ℝ) * u := (div_lt_iff₀ hu).mp hnu
  have hs : 1 / (n : ℝ) < u := (div_lt_iff₀ hden).mpr (by nlinarith)
  exact indicator_of_notMem
    (show u ∉ Iio (1 / (n : ℝ)) from not_lt.mpr hs.le) _

theorem actual_printed_spikes_tend_to_zero_almost_surely
    (hU : HasLaw U unitUniform μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => sourcePositiveSpike n (U ω)) atTop (𝓝 0) := by
  filter_upwards [actual_uniform_random_variable_is_positive_almost_surely hU] with ω hω
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
  filter_upwards [actual_printed_spikes_are_eventually_zero_at_every_positive_input (U ω) hω] with n hn
  exact hn.symm

theorem actual_printed_random_variable_escape_counterexample
    (hU : HasLaw U unitUniform μ) :
    (∀ n, 1 ≤ n → (∫ ω, sourcePositiveSpike n (U ω) ∂μ) = 1) ∧
    (∀ᵐ ω ∂μ, Tendsto (fun n => sourcePositiveSpike n (U ω)) atTop (𝓝 0)) ∧
    ¬ ∃ Y : Ω → ℝ, Integrable Y μ ∧
      ∀ n, 1 ≤ n → ∀ᵐ ω ∂μ, sourcePositiveSpike n (U ω) ≤ Y ω := by
  exact ⟨fun n hn => actual_printed_spike_has_mean_one_at_every_positive_index hU n hn,
    actual_printed_spikes_tend_to_zero_almost_surely hU,
    actual_no_integrable_variable_dominates_all_printed_positive_spikes hU⟩


theorem actual_printed_spike_is_zero_once_index_exceeds_input_reciprocal
    (u : ℝ) (hu : 0 < u) (n : ℕ) (hn : 1/u < (n : ℝ)) :
    sourcePositiveSpike n u = 0 := by
  have hden : 0 < (n : ℝ) := lt_trans (one_div_pos.mpr hu) hn
  have hp : 1 < (n : ℝ) * u := (div_lt_iff₀ hu).mp hn
  have hs : 1 / (n : ℝ) < u := (div_lt_iff₀ hden).mpr (by nlinarith)
  exact indicator_of_notMem
    (show u ∉ Iio (1 / (n : ℝ)) from not_lt.mpr hs.le) _

theorem actual_printed_expectation_limit_exchange_fails
    (hU : HasLaw U unitUniform μ) :
    ¬ Tendsto (fun n => ∫ ω, sourcePositiveSpike n (U ω) ∂μ)
      atTop (𝓝 (∫ _ : Ω, (0 : ℝ) ∂μ)) := by
  intro hzero
  have hone : Tendsto (fun n => ∫ ω, sourcePositiveSpike n (U ω) ∂μ)
      atTop (𝓝 (1 : ℝ)) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (actual_printed_spike_has_mean_one_at_every_positive_index hU n hn).symm
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique hone (by simpa only [integral_zero] using hzero)
  norm_num at hbad

end SafeLearning.CompleteAppliedEscapingExpectation30
