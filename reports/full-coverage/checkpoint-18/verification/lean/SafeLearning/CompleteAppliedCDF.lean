import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedCDF
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal

theorem actual_cdf_is_the_true_lower_event_probability
    (law : Measure ℝ) [IsProbabilityMeasure law] (point : ℝ) :
    cdf law point = law.real (Iic point) := cdf_eq_real law point

theorem actual_cdf_is_nondecreasing_right_continuous_and_has_the_two_limits
    (law : Measure ℝ) [IsProbabilityMeasure law] :
    Monotone (cdf law) ∧
      (∀ point,ContinuousWithinAt (cdf law) (Ici point) point) ∧
      Tendsto (cdf law) atBot (𝓝 0) ∧ Tendsto (cdf law) atTop (𝓝 1) :=
  ⟨monotone_cdf law,(cdf law).right_continuous,tendsto_cdf_atBot law,
    tendsto_cdf_atTop law⟩

theorem actual_cdf_jump_height_is_the_true_atom_probability
    (law : Measure ℝ) [IsProbabilityMeasure law] (point : ℝ) :
    law.real {point} = cdf law point-leftLim (cdf law) point := by
  have h := (cdf law).measure_singleton point
  rw [measure_cdf law] at h
  rw [measureReal_def,h]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr ((cdf law).mono.leftLim_le le_rfl))

theorem actual_cdf_jump_has_given_height_iff_the_atom_has_given_probability
    (law : Measure ℝ) [IsProbabilityMeasure law] (point : ℝ) (mass : ℝ) :
    cdf law point-leftLim (cdf law) point = mass ↔ law.real {point} = mass := by
  rw [actual_cdf_jump_height_is_the_true_atom_probability law point]

theorem actual_positive_cdf_jump_iff_a_positive_atom
    (law : Measure ℝ) [IsProbabilityMeasure law] (point : ℝ) :
    0 < cdf law point-leftLim (cdf law) point ↔ 0 < law.real {point} := by
  rw [actual_cdf_jump_height_is_the_true_atom_probability law point]

end SafeLearning.CompleteAppliedCDF
