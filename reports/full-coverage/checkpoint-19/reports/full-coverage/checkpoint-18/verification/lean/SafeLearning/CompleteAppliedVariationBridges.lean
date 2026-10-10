import SafeLearning.CompleteAppliedFiniteVariation
import SafeLearning.CompleteAppliedMeasurePinsker
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedVariationBridges
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedFiniteEntropy
open SafeLearning.CompleteAppliedFiniteVariation SafeLearning.CompleteAppliedMeasurePinsker
open SafeLearning.CompleteAppliedTwoAtomRisk SafeLearning.CompleteAppliedBinaryPinsker
open scoped ENNReal NNReal Classical

def strictPositiveEvent {n : ℕ} (p q : PMF (Fin n)) : Set (Fin n) :=
  {i | (q i).toReal < (p i).toReal}

theorem actual_strict_event_attains_finite_TV {n : ℕ} (p q : PMF (Fin n)) :
    |p.toMeasure.real (strictPositiveEvent p q)-q.toMeasure.real (strictPositiveEvent p q)|=
      totalVariation p q := by
  have hz : ∑ i,((p i).toReal-(q i).toReal)=0 := by
    rw [Finset.sum_sub_distrib,actual_finite_weights_sum,actual_finite_weights_sum]
    ring
  rw [actual_event_difference_sum,actual_finite_total_variation]
  have he : (∑ i,if i∈strictPositiveEvent p q then (p i).toReal-(q i).toReal else 0)=
      ∑ i,max ((p i).toReal-(q i).toReal) 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (q i).toReal < (p i).toReal
    · simp [strictPositiveEvent,h,max_eq_left (sub_nonneg.mpr h.le)]
    · simp [strictPositiveEvent,h,max_eq_right (sub_nonpos.mpr (le_of_not_gt h))]
  rw [he,abs_of_nonneg (Finset.sum_nonneg (fun i _ => le_max_right _ _)),
    zero_sum_positive_mass _ hz]

theorem actual_strict_event_indicator_preserves_TV {n : ℕ} (p q : PMF (Fin n)) :
    totalVariation (costLaw (eventParameter p.toMeasure (strictPositiveEvent p q)))
      (costLaw (eventParameter q.toMeasure (strictPositiveEvent p q)))=totalVariation p q := by
  rw [actual_binary_total_variation]
  exact actual_strict_event_attains_finite_TV p q

theorem actual_measurable_TV_symmetric {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) : measurableTotalVariation μ ν=measurableTotalVariation ν μ := by
  unfold measurableTotalVariation
  congr 1
  ext d
  constructor <;> rintro ⟨E,hE,hd⟩ <;> refine ⟨E,hE,?_⟩
  all_goals rw [abs_sub_comm];exact hd

theorem actual_arbitrary_measure_pinsker_both_directions {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2*measurableTotalVariation μ ν^2) ≤ klDiv μ ν ∧
    ENNReal.ofReal (2*measurableTotalVariation μ ν^2) ≤ klDiv ν μ := by
  refine ⟨actual_measure_pinsker_squared μ ν,?_⟩
  rw [actual_measurable_TV_symmetric μ ν]
  exact actual_measure_pinsker_squared ν μ

end SafeLearning.CompleteAppliedVariationBridges
