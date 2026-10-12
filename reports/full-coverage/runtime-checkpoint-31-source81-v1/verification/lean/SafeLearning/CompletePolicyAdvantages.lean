import Mathlib

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SafeLearning.CompletePolicyAdvantages

def policy (q : unitInterval) : PMF (Fin 2) := PMF.ofFintype
  (fun i => ENNReal.ofReal ((![q, 1 - (q : ℝ)] : Fin 2 → ℝ) i))
  (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add q.2.1 (sub_nonneg.mpr q.2.2)]
    simp)

def oldParameter : unitInterval := ⟨1 / 4, by norm_num⟩
def newParameter : unitInterval := ⟨1 / 2, by norm_num⟩
def actionValue : Fin 2 → ℝ := ![5, 1]
def stateValue : ℝ := ∫ i, actionValue i ∂(policy oldParameter).toMeasure
def advantage (i : Fin 2) : ℝ := actionValue i - stateValue

theorem genuine_binary_policy_integral (q : unitInterval) (f : Fin 2 → ℝ) :
    (∫ i, f i ∂(policy q).toMeasure) =
      (q : ℝ) * f 0 + (1 - (q : ℝ)) * f 1 := by
  rw [PMF.integral_eq_sum]
  simp only [policy, PMF.ofFintype_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ENNReal.toReal_ofReal q.2.1, ENNReal.toReal_ofReal (sub_nonneg.mpr q.2.2)]
  simp only [smul_eq_mul]

theorem general_actual_policy_advantage_centered (q : unitInterval) (f : Fin 2 → ℝ) :
    (∫ i, (f i - ∫ j, f j ∂(policy q).toMeasure) ∂(policy q).toMeasure) = 0 := by
  rw [genuine_binary_policy_integral, genuine_binary_policy_integral]
  ring

theorem source_state_value_and_advantages :
    stateValue = 2 ∧ advantage 0 = 3 ∧ advantage 1 = -1 := by
  have hv : stateValue = 2 := by
    rw [stateValue, genuine_binary_policy_integral]
    norm_num [oldParameter, actionValue]
  norm_num [advantage, actionValue, hv]

theorem actual_old_and_new_advantage_expectations :
    (∫ i, advantage i ∂(policy oldParameter).toMeasure) = 0 ∧
      (∫ i, advantage i ∂(policy newParameter).toMeasure) = 1 := by
  rw [genuine_binary_policy_integral, genuine_binary_policy_integral]
  norm_num [source_state_value_and_advantages.2.1,
    source_state_value_and_advantages.2.2, oldParameter, newParameter]

theorem genuine_probability_shift_toward_better_action :
    policy oldParameter 0 = 1 / 4 ∧ policy newParameter 0 = 1 / 2 ∧
      policy oldParameter 0 < policy newParameter 0 ∧
      actionValue 0 > stateValue := by
  norm_num [policy, oldParameter, newParameter, actionValue,
    source_state_value_and_advantages.1, ENNReal.ofReal_div_of_pos]

end SafeLearning.CompletePolicyAdvantages
