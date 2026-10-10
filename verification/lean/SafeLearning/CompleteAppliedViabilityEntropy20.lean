import SafeLearning.CompleteAppliedTemperatureSoftmax

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory InformationTheory
namespace SafeLearning.CompleteAppliedViabilityEntropy20
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedFiniteEntropy
open SafeLearning.CompleteAppliedTemperatureSoftmax

def safeUniform : PMF (Fin 4) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (if i.val < 3 then (1/3 : ℝ) else 0)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> norm_num)]
    norm_num [Fin.sum_univ_succ])

theorem actual_safe_uniform_has_three_equal_masses_and_zero_critical_mass :
    (∀ i : Fin 4, (safeUniform i).toReal = if i.val < 3 then (1/3 : ℝ) else 0) ∧
      safeUniform.toMeasure ({3} : Set (Fin 4)) = 0 := by
  constructor
  · intro i
    by_cases h : i.val < 3 <;> simp [safeUniform,PMF.ofFintype_apply,h]
  · rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
    norm_num [safeUniform,PMF.ofFintype_apply]

theorem actual_safe_uniform_entropy_is_log_three : shannonEntropy safeUniform = Real.log 3 := by
  rw [actual_entropy_sum]
  simp only [actual_safe_uniform_has_three_equal_masses_and_zero_critical_mass.1]
  norm_num [Fin.sum_univ_succ]
  rw [show (1/3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,Real.log_inv]
  ring

theorem actual_full_uniform_entropy_and_true_critical_probability :
    shannonEntropy (PMF.uniformOfFintype (Fin 4)) = Real.log 4 ∧
      (PMF.uniformOfFintype (Fin 4)).toMeasure ({3} : Set (Fin 4)) = 1/4 := by
  constructor
  · exact (actual_maximum_entropy_iff_uniform _).2 rfl
  · rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
    norm_num [PMF.uniformOfFintype_apply]

theorem actual_source_entropy_roundings :
    |Real.log 3-109861/10^5| < 1/(2*10^5) ∧
      |Real.log 4-138629/10^5| < 1/(2*10^5) := by
  have h3 : |Real.log 3-109861228867/10^11| ≤ 1/10^10 := by
    convert Real.log_three_near_10 using 1 <;> norm_num
  have h4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  have hl3 := abs_le.mp h3
  rw [h4]
  constructor <;> rw [abs_lt] <;> constructor <;>
    linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]

theorem actual_finite_score_softmax_assigns_positive_critical_probability
    (scores : Fin 4 → ℝ) (temperature : ℝ) (_ht : 0 < temperature) :
    0 < (actualTemperatureLaw scores temperature 3).toReal ∧
      actualTemperatureLaw scores temperature 3 ≠ 0 := by
  exact (actual_temperature_law_has_full_support_and_positive_real_masses scores temperature 3).symm

end SafeLearning.CompleteAppliedViabilityEntropy20
