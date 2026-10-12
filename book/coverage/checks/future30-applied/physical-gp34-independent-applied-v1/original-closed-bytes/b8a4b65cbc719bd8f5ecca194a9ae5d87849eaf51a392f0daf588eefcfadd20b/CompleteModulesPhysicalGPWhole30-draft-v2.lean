import SafeLearning.CompleteModulesMatrixGP
import SafeLearning.CompleteModulesBook

set_option autoImplicit false
noncomputable section
open Matrix Filter
open scoped BigOperators Topology Matrix

namespace SafeLearning.CompleteModulesPhysicalGPWhole30

def onesMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1
def repeatedGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := 4 • onesMatrix n
def repeatedQuery (n : ℕ) : Fin n → ℝ := fun _ => 4
def repeatedLabels (n : ℕ) : Fin n → ℝ := fun _ => 2
def repeatedRidgeInverse (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (4 / (1 + 4 * (n : ℝ))) • onesMatrix n
def repeatedMean (n : ℕ) : ℝ :=
  CompleteModulesMatrixGP.posteriorMean (repeatedGram n) (repeatedQuery n)
    (repeatedLabels n) 1
def repeatedVariance (n : ℕ) : ℝ :=
  CompleteModulesMatrixGP.posteriorVariance (repeatedGram n) (repeatedQuery n) 4 1
def repeatedUpper (n : ℕ) : ℝ := repeatedMean n + 2 * Real.sqrt (repeatedVariance n)

theorem ones_matrix_square (n : ℕ) :
    onesMatrix n * onesMatrix n = (n : ℝ) • onesMatrix n := by
  ext i j
  simp [onesMatrix, Matrix.mul_apply]

theorem repeated_ridge_right_inverse (n : ℕ) :
    CompleteModulesMatrixGP.ridgeMatrix (repeatedGram n) 1 * repeatedRidgeInverse n = 1 := by
  have hd : (1 + 4 * (n : ℝ)) ≠ 0 := by positivity
  have hc : (4 : ℝ) - 4 / (1 + 4 * (n : ℝ)) -
      4 * (4 / (1 + 4 * (n : ℝ))) * n = 0 := by
    field_simp
    ring
  simp only [CompleteModulesMatrixGP.ridgeMatrix, repeatedGram, repeatedRidgeInverse,
    one_smul, add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, ones_matrix_square]
  calc
    _ = 1 + ((4 : ℝ) - 4 / (1 + 4 * (n : ℝ)) -
        4 * (4 / (1 + 4 * (n : ℝ))) * n) • onesMatrix n := by module
    _ = 1 := by rw [hc]; simp

theorem repeated_ridge_actual_inverse (n : ℕ) :
    (CompleteModulesMatrixGP.ridgeMatrix (repeatedGram n) 1)⁻¹ =
      repeatedRidgeInverse n :=
  Matrix.inv_eq_right_inv (repeated_ridge_right_inverse n)

theorem repeated_inverse_constant_action (n : ℕ) (r : ℝ) :
    repeatedRidgeInverse n *ᵥ (fun _ : Fin n => r) =
      fun _ => r / (1 + 4 * (n : ℝ)) := by
  have hd : (1 + 4 * (n : ℝ)) ≠ 0 := by positivity
  rw [repeatedRidgeInverse, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  simp [Matrix.mulVec, dotProduct, onesMatrix]
  field_simp
  ring

theorem repeated_actual_posterior (n : ℕ) :
    repeatedMean n = 8 * (n : ℝ) / (1 + 4 * n) ∧
    repeatedVariance n = 4 / (1 + 4 * (n : ℝ)) := by
  have hd : (1 + 4 * (n : ℝ)) ≠ 0 := by positivity
  constructor
  · rw [repeatedMean, CompleteModulesMatrixGP.posteriorMean,
      repeated_ridge_actual_inverse, repeatedLabels, repeated_inverse_constant_action]
    simp [repeatedQuery, dotProduct]
    ring
  · rw [repeatedVariance, CompleteModulesMatrixGP.posteriorVariance,
      repeated_ridge_actual_inverse]
    change 4 - (fun _ : Fin n => (4 : ℝ)) ⬝ᵥ
      (repeatedRidgeInverse n *ᵥ (fun _ => (4 : ℝ))) = _
    rw [repeated_inverse_constant_action]
    simp [dotProduct]
    field_simp
    ring

theorem repeated_regularized_solution_unique (n : ℕ) (a : Fin n → ℝ) (r : ℝ)
    (h : CompleteModulesMatrixGP.ridgeMatrix (repeatedGram n) 1 *ᵥ a = fun _ => r) :
    a = fun _ => r / (1 + 4 * (n : ℝ)) := by
  rw [CompleteModulesMatrixGP.ridgeMatrix, repeatedGram, Matrix.add_mulVec,
    Matrix.smul_mulVec, one_smul, Matrix.one_mulVec] at h
  apply funext
  have hs : ∀ i, a i + 4 * (∑ j, a j) = r := by
    intro i
    have hi := congrFun h i
    simpa [Matrix.mulVec, dotProduct, onesMatrix, add_comm] using hi
  simpa using CompleteModulesBook.constant_kernel_regularized_unique a r hs

theorem repeated_variance_positive (n : ℕ) : 0 < repeatedVariance n := by
  rw [(repeated_actual_posterior n).2]
  positivity

theorem repeated_variance_strictly_decreases {m n : ℕ} (h : m < n) :
    repeatedVariance n < repeatedVariance m := by
  rw [(repeated_actual_posterior n).2, (repeated_actual_posterior m).2]
  have hm : 0 < 1 + 4 * (m : ℝ) := by positivity
  have hn : 0 < 1 + 4 * (n : ℝ) := by positivity
  rw [div_lt_div_iff₀ hn hm]
  exact_mod_cast (by omega : 4 * (1 + 4 * m) < 4 * (1 + 4 * n))

theorem repeated_posterior_ratio_forms (n : ℕ) :
    repeatedMean n = 2 * ((n : ℝ) / (n + 1 / 4)) ∧
    repeatedVariance n = 4 - 4 * ((n : ℝ) / (n + 1 / 4)) := by
  have hd : (1 + 4 * (n : ℝ)) ≠ 0 := by positivity
  have he : (n : ℝ) + 1 / 4 ≠ 0 := by positivity
  rw [(repeated_actual_posterior n).1, (repeated_actual_posterior n).2]
  constructor <;> field_simp <;> ring

theorem repeated_mean_tends_to_reading :
    Tendsto repeatedMean atTop (𝓝 2) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
    (tendsto_natCast_div_add_atTop (1 / 4 : ℝ))
  simpa only [mul_one] using h.congr (fun n => (repeated_posterior_ratio_forms n).1.symm)

theorem repeated_variance_tends_to_zero :
    Tendsto repeatedVariance atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
  have h := hc.sub (hc.mul (tendsto_natCast_div_add_atTop (1 / 4 : ℝ)))
  convert h.congr (fun n => (repeated_posterior_ratio_forms n).2.symm) using 1 <;> norm_num

theorem repeated_mean_not_zero (n : ℕ) (hn : 0 < n) : 0 < repeatedMean n := by
  rw [(repeated_actual_posterior n).1]
  positivity

theorem repeated_three_exact_posterior :
    repeatedMean 3 = 24 / 13 ∧ repeatedVariance 3 = 4 / 13 := by
  convert repeated_actual_posterior 3 using 1 <;> norm_num

theorem repeated_three_six_decimal_roundings :
    (18461535 / 10000000 : ℝ) < repeatedMean 3 ∧
    repeatedMean 3 < 18461545 / 10000000 ∧
    (29555535 / 10000000 : ℝ) < repeatedUpper 3 ∧
    repeatedUpper 3 < 29555545 / 10000000 ∧
    (599555535 / 10000000 : ℝ) < 57 + repeatedUpper 3 ∧
    57 + repeatedUpper 3 < 599555545 / 10000000 := by
  rw [repeatedUpper, repeated_three_exact_posterior.1, repeated_three_exact_posterior.2]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 13)
  have hn := Real.sqrt_nonneg (4 / 13 : ℝ)
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem repeated_three_conditional_heating (f : ℝ)
    (hf : |f - repeatedMean 3| ≤ 2 * Real.sqrt (repeatedVariance 3)) :
    57 + f < 60 := by
  have hu : 57 + repeatedUpper 3 < 60 := by
    rw [repeatedUpper, repeated_three_exact_posterior.1, repeated_three_exact_posterior.2]
    simpa only [add_assoc] using CompleteModulesBook.repeated_gp_three_accept
  have hfu := (abs_le.mp hf).2
  unfold repeatedUpper at hu
  linarith

def midpointGram : Matrix (Fin 2) (Fin 2) ℝ := !![4, 2; 2, 4]
def midpointQuery : Fin 2 → ℝ := ![3, 3]
def midpointLabels : Fin 2 → ℝ := ![2, 0]
def midpointInverse : Matrix (Fin 2) (Fin 2) ℝ := !![5 / 21, -2 / 21; -2 / 21, 5 / 21]
def midpointMean : ℝ := CompleteModulesMatrixGP.posteriorMean
  midpointGram midpointQuery midpointLabels 1
def midpointVariance : ℝ := CompleteModulesMatrixGP.posteriorVariance
  midpointGram midpointQuery 4 1
def midpointSigma : ℝ := Real.sqrt midpointVariance
def midpointUpper : ℝ := midpointMean + 2 * midpointSigma
def physicalUpper : ℝ := midpointUpper + 2 / 5
def largestPhysicalNominal : ℝ := 60 - physicalUpper

theorem midpoint_actual_inverse :
    (CompleteModulesMatrixGP.ridgeMatrix midpointGram 1)⁻¹ = midpointInverse := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [CompleteModulesMatrixGP.ridgeMatrix, midpointGram, midpointInverse,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem midpoint_actual_posterior : midpointMean = 6 / 7 ∧ midpointVariance = 10 / 7 := by
  constructor <;>
    norm_num [midpointMean, midpointVariance, CompleteModulesMatrixGP.posteriorMean,
      CompleteModulesMatrixGP.posteriorVariance, midpoint_actual_inverse,
      midpointQuery, midpointLabels, midpointInverse, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

theorem midpoint_sigma_positive : 0 < midpointSigma := by
  rw [midpointSigma, midpoint_actual_posterior.2]
  positivity

theorem physical_upper_exact : physicalUpper = 6 / 7 + 2 * Real.sqrt (10 / 7) + 2 / 5 := by
  simp [physicalUpper, midpointUpper, midpointSigma, midpoint_actual_posterior]

theorem physical_residual_greatest :
    IsGreatest {r : ℝ | ∃ f b : ℝ,
      |f - midpointMean| ≤ 2 * midpointSigma ∧ |b| ≤ 2 / 5 ∧ r = f + b}
      physicalUpper := by
  constructor
  · refine ⟨midpointMean + 2 * midpointSigma, 2 / 5, ?_, ?_, ?_⟩
    · rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg (by norm_num) midpoint_sigma_positive.le)]
    · norm_num
    · rfl
  · rintro r ⟨f, b, hf, hb, rfl⟩
    have hfu := (abs_le.mp hf).2
    have hbu := (abs_le.mp hb).2
    dsimp [physicalUpper, midpointUpper]
    linarith

theorem all_admissible_residuals_safe_iff (nominal : ℝ) :
    (∀ f b : ℝ, |f - midpointMean| ≤ 2 * midpointSigma → |b| ≤ 2 / 5 →
      nominal + f + b ≤ 60) ↔ nominal ≤ largestPhysicalNominal := by
  constructor
  · intro h
    have hw := h (midpointMean + 2 * midpointSigma) (2 / 5)
      (by rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg (by norm_num) midpoint_sigma_positive.le)]) (by norm_num)
    dsimp [largestPhysicalNominal, physicalUpper, midpointUpper]
    linarith
  · intro h f b hf hb
    have hfu := (abs_le.mp hf).2
    have hbu := (abs_le.mp hb).2
    dsimp [largestPhysicalNominal, physicalUpper, midpointUpper] at h
    linarith

theorem physical_56_point_5_rejected_by_attained_residual :
    ∃ f b : ℝ, |f - midpointMean| ≤ 2 * midpointSigma ∧ |b| ≤ 2 / 5 ∧
      60 < (113 / 2 : ℝ) + f + b := by
  refine ⟨midpointMean + 2 * midpointSigma, 2 / 5, ?_, by norm_num, ?_⟩
  · rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg (by norm_num) midpoint_sigma_positive.le)]
  · rw [midpoint_actual_posterior.1, midpointSigma, midpoint_actual_posterior.2]
    nlinarith [CompleteModulesBook.midpoint_discrepancy_reject]

theorem physical_six_decimal_roundings :
    (36475995 / 10000000 : ℝ) < physicalUpper ∧ physicalUpper < 36476005 / 10000000 ∧
    (601475995 / 10000000 : ℝ) < 113 / 2 + physicalUpper ∧
    113 / 2 + physicalUpper < 601476005 / 10000000 ∧
    (563523995 / 10000000 : ℝ) < largestPhysicalNominal ∧
    largestPhysicalNominal < 563524005 / 10000000 := by
  rw [physical_upper_exact]
  dsimp [largestPhysicalNominal]
  rw [physical_upper_exact]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10 / 7)
  have hn := Real.sqrt_nonneg (10 / 7 : ℝ)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem rounded_midpoint_upper_is_strictly_too_small :
    (3247600 / 1000000 : ℝ) < midpointUpper := by
  rw [midpointUpper, midpointSigma, midpoint_actual_posterior.1, midpoint_actual_posterior.2]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10 / 7)
  have hn := Real.sqrt_nonneg (10 / 7 : ℝ)
  nlinarith

theorem repeated_mean_error_identity (n : ℕ) :
    2 - repeatedMean n = repeatedVariance n / 2 := by
  have hd : (1 + 4 * (n : ℝ)) ≠ 0 := by positivity
  rw [(repeated_actual_posterior n).1, (repeated_actual_posterior n).2]
  field_simp
  ring

theorem repeated_true_function_in_assumed_envelope (n : ℕ) :
    |2 - repeatedMean n| ≤ 2 * Real.sqrt (repeatedVariance n) := by
  have hv := repeated_variance_positive n
  have hv4 : repeatedVariance n ≤ 4 := by
    rw [(repeated_actual_posterior n).2]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (R := ℝ) n]
  rw [repeated_mean_error_identity, abs_of_pos (by positivity)]
  have hs := Real.sq_sqrt hv.le
  have hn := Real.sqrt_nonneg (repeatedVariance n)
  nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hv4)]

def persistentDiscrepancy : Fin 2 → ℝ := ![0, 2 / 5]
def modeledFunction : Fin 2 → ℝ := fun _ => 2
def physicalFunction (z : Fin 2) : ℝ := modeledFunction z + persistentDiscrepancy z

theorem persistent_discrepancy_meets_bound (z : Fin 2) :
    |persistentDiscrepancy z| ≤ 2 / 5 := by
  fin_cases z <;> norm_num [persistentDiscrepancy]

theorem repeated_observations_fit_same_physical_data (n : ℕ) (i : Fin n) :
    repeatedLabels n i = physicalFunction 0 := by
  norm_num [repeatedLabels, physicalFunction, modeledFunction, persistentDiscrepancy]

theorem persistent_discrepancy_target_and_envelope (n : ℕ) :
    (∀ z : Fin 2, |modeledFunction z - repeatedMean n| ≤
      2 * Real.sqrt (repeatedVariance n)) ∧
    persistentDiscrepancy 1 = 2 / 5 ∧ physicalFunction 1 = 12 / 5 := by
  refine ⟨fun _ => repeated_true_function_in_assumed_envelope n, ?_, ?_⟩ <;>
    norm_num [persistentDiscrepancy, physicalFunction, modeledFunction]

theorem unmodeled_discrepancy_survives_vanishing_variance :
    Tendsto repeatedVariance atTop (𝓝 0) ∧
    (∀ n : ℕ, persistentDiscrepancy 1 = 2 / 5 ∧
      ∀ i : Fin n, repeatedLabels n i = physicalFunction 0) := by
  refine ⟨repeated_variance_tends_to_zero, fun n => ⟨?_, ?_⟩⟩
  · norm_num [persistentDiscrepancy]
  · exact repeated_observations_fit_same_physical_data n

end SafeLearning.CompleteModulesPhysicalGPWhole30
