import Mathlib

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SafeLearning.CompletePolicyDivergence

def oldLaw : PMF (Fin 2) := PMF.ofFintype
  (fun i => ENNReal.ofReal ((![1 / 2, 1 / 2] : Fin 2 → ℝ) i))
  (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)
def newLaw : PMF (Fin 2) := PMF.ofFintype
  (fun i => ENNReal.ofReal ((![3 / 4, 1 / 4] : Fin 2 → ℝ) i))
  (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)
def totalVariation (first second : PMF (Fin 2)) : ℝ :=
  (1 / 2) * ∑ i, |(first i).toReal - (second i).toReal|
def divergence (first second : PMF (Fin 2)) : ℝ :=
  ∫ i, Real.log ((first i).toReal / (second i).toReal) ∂first.toMeasure

theorem actual_total_variation : totalVariation newLaw oldLaw = 1 / 4 := by
  norm_num [totalVariation, newLaw, oldLaw, Fin.sum_univ_two, ENNReal.toReal_div]

theorem actual_forward_and_reverse_KL :
    divergence newLaw oldLaw = (3 / 4) * Real.log (3 / 2) + (1 / 4) * Real.log (1 / 2) ∧
      divergence oldLaw newLaw = (1 / 2) * Real.log (2 / 3) + (1 / 2) * Real.log 2 := by
  constructor <;>
    norm_num [divergence, PMF.integral_eq_sum, newLaw, oldLaw, Fin.sum_univ_two,
      smul_eq_mul] <;>
    simp [Real.log_div] <;> ring

theorem identical_policy_divergences_vanish (law : PMF (Fin 2)) :
    totalVariation law law = 0 ∧ divergence law law = 0 := by
  constructor
  · simp [totalVariation]
  · rw [divergence, PMF.integral_eq_sum]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases h : (law i).toReal = 0
    · simp [h]
    · simp [div_self h]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem log_three_halves_enclosure :
    (4054651080 / 10000000000 : ℝ) < Real.log (3 / 2) ∧
      Real.log (3 / 2) < 4054651082 / 10000000000 := by
  have hb₁ := Real.exp_bound (x := (4054651080 / 10000000000 : ℝ))
    (by norm_num) (n := 14) (by norm_num)
  have hb₂ := Real.exp_bound (x := (4054651082 / 10000000000 : ℝ))
    (by norm_num) (n := 14) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb₁ hb₂
  have h₁ : Real.exp (4054651080 / 10000000000 : ℝ) < 3 / 2 := by
    linarith [(abs_le.mp hb₁).2]
  have h₂ : (3 / 2 : ℝ) < Real.exp (4054651082 / 10000000000 : ℝ) := by
    linarith [(abs_le.mp hb₂).1]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)] at h₁ h₂
  exact ⟨Real.exp_lt_exp.mp h₁, Real.exp_lt_exp.mp h₂⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem log_two_enclosure :
    (6931471805 / 10000000000 : ℝ) < Real.log 2 ∧
      Real.log 2 < 6931471806 / 10000000000 := by
  have hb₁ := Real.exp_bound (x := (6931471805 / 10000000000 : ℝ))
    (by norm_num) (n := 14) (by norm_num)
  have hb₂ := Real.exp_bound (x := (6931471806 / 10000000000 : ℝ))
    (by norm_num) (n := 14) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb₁ hb₂
  have h₁ : Real.exp (6931471805 / 10000000000 : ℝ) < 2 := by
    linarith [(abs_le.mp hb₁).2]
  have h₂ : (2 : ℝ) < Real.exp (6931471806 / 10000000000 : ℝ) := by
    linarith [(abs_le.mp hb₂).1]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h₁ h₂
  exact ⟨Real.exp_lt_exp.mp h₁, Real.exp_lt_exp.mp h₂⟩

theorem actual_KL_six_decimal_rounding_and_asymmetry :
    |divergence newLaw oldLaw - (130812 / 1000000 : ℝ)| < 1 / 2000000 ∧
      divergence newLaw oldLaw < divergence oldLaw newLaw := by
  obtain ⟨ha, hb⟩ := log_three_halves_enclosure
  obtain ⟨hc, hd⟩ := log_two_enclosure
  obtain ⟨hf, hr⟩ := actual_forward_and_reverse_KL
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have htwo : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
    rw [show (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hhalf] at hf
  rw [htwo] at hr
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  · linarith

end SafeLearning.CompletePolicyDivergence
