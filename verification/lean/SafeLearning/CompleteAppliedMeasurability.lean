import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedMeasurability

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

theorem actual_measurability_is_preimages_of_all_legitimate_events
    (f : Ω → X) : Measurable f ↔ ∀ s,MeasurableSet s → MeasurableSet (f ⁻¹' s) := by
  rfl

theorem actual_legitimate_events_are_closed_under_complements_and_countable_unions
    (s : ℕ → Set Ω) (hs : ∀ n,MeasurableSet (s n)) :
    (∀ n,MeasurableSet (s n)ᶜ) ∧ MeasurableSet (⋃ n,s n) :=
  ⟨fun n => (hs n).compl,MeasurableSet.iUnion hs⟩

theorem actual_composition_with_any_continuous_real_map_preserves_measurability
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : Ω → Y) (hf : Measurable f) (g : Y → ℝ) (hg : Continuous g) :
    Measurable (g ∘ f) := hg.measurable.comp hf

theorem actual_every_countable_box_is_measurable_and_has_a_measurable_indicator
    {I : Type*} [Countable I] (lower upper : I → ℝ) :
    MeasurableSet (Set.pi univ (fun i => Icc (lower i) (upper i))) ∧
      Measurable ((Set.pi univ (fun i => Icc (lower i) (upper i))).indicator
        (fun _ : I → ℝ => (1 : ℝ))) := by
  have hm : MeasurableSet (Set.pi univ (fun i => Icc (lower i) (upper i))) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  exact ⟨hm,measurable_const.indicator hm⟩

theorem actual_real_sums_products_maxima_and_minima_are_measurable
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => f ω+g ω) ∧ Measurable (fun ω => f ω*g ω) ∧
      Measurable (fun ω => max (f ω) (g ω)) ∧ Measurable (fun ω => min (f ω) (g ω)) := by
  exact ⟨hf.add hg,hf.mul hg,hf.max hg,hf.min hg⟩

theorem actual_finite_sums_and_products_are_measurable
    {I : Type*} (s : Finset I) (f : I → Ω → ℝ) (hf : ∀ i∈s,Measurable (f i)) :
    Measurable (fun ω => ∑ i∈s,f i ω) ∧ Measurable (fun ω => ∏ i∈s,f i ω) := by
  exact ⟨Finset.measurable_sum s hf,Finset.measurable_prod s hf⟩

theorem actual_pointwise_limits_of_measurable_real_functions_are_measurable
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (hf : ∀ n,Measurable (f n))
    (hl : ∀ ω,Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Measurable g :=
  measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hl)

theorem actual_measurable_controller_and_state_give_measurable_control_events
    (state : Ω → X) (hstate : Measurable state) (policy : X → ℝ)
    (hpolicy : Measurable policy) (event : Set ℝ) (hevent : MeasurableSet event) :
    MeasurableSet {ω | policy (state ω)∈event} :=
  (hpolicy.comp hstate) hevent

theorem actual_measurable_transition_kernel_gives_measurable_next_event_probabilities
    (kernel : Kernel Ω X) (event : Set X) (hevent : MeasurableSet event) :
    Measurable (fun ω => kernel ω event) := kernel.measurable_coe hevent

end SafeLearning.CompleteAppliedMeasurability
