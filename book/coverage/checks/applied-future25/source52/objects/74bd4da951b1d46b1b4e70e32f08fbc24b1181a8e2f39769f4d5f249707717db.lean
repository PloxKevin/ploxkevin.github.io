import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace SafeLearning.CompleteAppliedThreeEqualConditionalOutcomes25

/-- Any three equally likely retained atoms become equiprobable after conditioning.
The retained-event mass is derived by true finite measure additivity. -/
theorem actual_three_equal_retained_outcomes_have_conditional_probability_one_third
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset Ω) (hs : s.card = 3)
    (q : ℝ) (hq : 0 < q) (hm : ∀ i ∈ s, μ.real {i} = q) (i : Ω) (hi : i ∈ s) :
    (μ[| (s : Set Ω)]).real {i} = 1/3 := by
  classical
  have hsum : μ.real (s : Set Ω) = 3*q := by
    rw [← sum_measureReal_singleton]
    calc
      (∑ j ∈ s, μ.real {j}) = ∑ _j ∈ s, q :=
        Finset.sum_congr rfl (fun j hj => hm j hj)
      _ = 3*q := by simp [hs]
  have hsubset : ({i} : Set Ω) ⊆ (s : Set Ω) := singleton_subset_iff.mpr hi
  have h := congrArg ENNReal.toReal (cond_apply s.measurableSet μ ({i} : Set Ω))
  rw [inter_eq_right.mpr hsubset] at h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def] at h
  rw [h, hm i hi, hsum]
  field_simp [ne_of_gt hq]
  <;> ring

end SafeLearning.CompleteAppliedThreeEqualConditionalOutcomes25
