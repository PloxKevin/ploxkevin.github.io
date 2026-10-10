import SafeLearning.CompleteModulesSafeOptFiniteInformationBound
import SafeLearning.CompleteModulesSafeOptLogPowerGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter
open scoped BigOperators Matrix Topology

namespace SafeLearning.CompleteModulesSafeOptFiniteInformationGrowth

open CompleteModulesSafeOptGPInformationBudget CompleteModulesSafeOptFiniteInformationBound
open CompleteModulesSafeOptLogPowerGrowth

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The source Sui/Srinivas convention bounds the squared RKHS norm by B
and uses this squared half-width multiplier; no concentration is asserted. -/
def actualSourceSuiSquaredWidthMultiplier (kernel : X → X → ℝ) (lambda B delta : ℝ) (T : ℕ) : ℝ :=
  2 * B + 300 * actualFiniteMaximumKernelInformationGain kernel lambda T *
    (Real.log ((T : ℝ) / delta)) ^ 3

/-- A derived finite-domain upper envelope for every source multiplier up
to horizon T. Its extra positive shift is explicit and permits an exact
generous integer horizon without asserting source minimal t-star equality. -/
def actualFiniteSuiSquaredWidthEnvelope (lambda B delta : ℝ) (T : ℕ) : ℝ :=
  2 * B + 300 * ((Fintype.card X : ℝ) / 2) * Real.log (1 + (T : ℝ) / lambda) *
    (Real.log (((T : ℝ) + 1) / delta)) ^ 3

private theorem actual_envelope_nonnegative (lambda B delta : ℝ)
    (hlambda : 0 < lambda) (hB : 0 ≤ B) (hdelta : 0 < delta) (hdeltaone : delta ≤ 1) (T : ℕ) :
    0 ≤ actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta T := by
  have hl : 0 ≤ Real.log (1 + (T : ℝ) / lambda) :=
    Real.log_nonneg (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg T) hlambda.le))
  have hd : 0 ≤ Real.log (((T : ℝ) + 1) / delta) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hdelta]
    have ht : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
    linarith
  unfold actualFiniteSuiSquaredWidthEnvelope
  positivity

/-- Every positive source round through T has its actual Sui multiplier
bounded by the computed finite envelope, using the derived Gamma bound. -/
theorem actual_source_sui_squared_width_is_bounded_by_the_finite_horizon_envelope
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (hnormalized : ∀ x, kernel x x ≤ 1) (lambda B delta : ℝ)
    (hlambda : 0 < lambda) (hB : 0 ≤ B) (hdelta : 0 < delta) (hdeltaone : delta ≤ 1)
    (t T : ℕ) (ht : 0 < t) (htT : t ≤ T) :
    actualSourceSuiSquaredWidthMultiplier kernel lambda B delta t ≤
      actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta T := by
  have hg := actual_normalized_finite_kernel_maximum_information_has_the_cardinality_log_bound
    kernel hkernel hnormalized lambda hlambda t
  have htR : 1 ≤ (t : ℝ) := by exact_mod_cast ht
  have hT : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
  have hlogt : 0 ≤ Real.log ((t : ℝ) / delta) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hdelta]
    linarith
  have hlogupper : Real.log ((t : ℝ) / delta) ≤ Real.log (((T : ℝ) + 1) / delta) :=
    Real.log_le_log (div_pos (by linarith) hdelta) (by gcongr; linarith)
  have hinfo : actualFiniteMaximumKernelInformationGain kernel lambda t ≤
      ((Fintype.card X : ℝ) / 2) * Real.log (1 + (T : ℝ) / lambda) := by
    apply hg.2.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log (by positivity)
    gcongr
  unfold actualSourceSuiSquaredWidthMultiplier actualFiniteSuiSquaredWidthEnvelope
  have hlogT : 0 ≤ Real.log (1 + (T : ℝ) / lambda) :=
    Real.log_nonneg (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg T) hlambda.le))
  have hp := mul_le_mul hinfo (pow_le_pow_left₀ hlogt hlogupper 3)
    (pow_nonneg hlogt 3) (mul_nonneg (by positivity) hlogT)
  nlinarith

private theorem actual_finite_envelope_information_product_has_a_log_polynomial_bound
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (hnormalized : ∀ x, kernel x x ≤ 1) (lambda B delta : ℝ)
    (hlambda : 0 < lambda) (hB : 0 ≤ B) (hdelta : 0 < delta) (hdeltaone : delta ≤ 1)
    (T : ℕ) :
    0 ≤ actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta T *
      actualFiniteMaximumKernelInformationGain kernel lambda T ∧
    actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta T *
      actualFiniteMaximumKernelInformationGain kernel lambda T ≤
      (2 * B * ((Fintype.card X : ℝ) / 2)) * Real.log ((2 + lambda⁻¹ + delta⁻¹) * ((T : ℝ) + 1)) +
      (300 * ((Fintype.card X : ℝ) / 2) ^ 2) *
        (Real.log ((2 + lambda⁻¹ + delta⁻¹) * ((T : ℝ) + 1))) ^ 5 := by
  let a := 2 + lambda⁻¹ + delta⁻¹
  let L := Real.log (a * ((T : ℝ) + 1))
  let c := (Fintype.card X : ℝ) / 2
  have hlambdaInv : 0 ≤ lambda⁻¹ := inv_nonneg.mpr hlambda.le
  have hdeltaInv : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
  have ha : 1 ≤ a := by dsimp only [a]; linarith
  have hapos : 0 < a := by linarith
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have ht : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  have hL : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hll : 0 ≤ Real.log (1 + (T : ℝ) / lambda) :=
    Real.log_nonneg (le_add_of_nonneg_right (div_nonneg ht hlambda.le))
  have hld : 0 ≤ Real.log (((T : ℝ) + 1) / delta) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hdelta]
    linarith
  have hllL : Real.log (1 + (T : ℝ) / lambda) ≤ L := by
    apply Real.log_le_log (by positivity)
    have h := mul_le_mul_of_nonneg_right (show lambda⁻¹ ≤ a by dsimp only [a]; linarith) ht
    rw [div_eq_mul_inv]
    nlinarith
  have hldL : Real.log (((T : ℝ) + 1) / delta) ≤ L := by
    apply Real.log_le_log (div_pos (by positivity) hdelta)
    have h := mul_le_mul_of_nonneg_right (show delta⁻¹ ≤ a by dsimp only [a]; linarith)
      (show 0 ≤ (T : ℝ) + 1 by positivity)
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hg := actual_normalized_finite_kernel_maximum_information_has_the_cardinality_log_bound
    kernel hkernel hnormalized lambda hlambda T
  have hgL : actualFiniteMaximumKernelInformationGain kernel lambda T ≤ c * L :=
    hg.2.trans (mul_le_mul_of_nonneg_left hllL hc)
  have henvelope : actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta T ≤
      2 * B + 300 * c * L ^ 4 := by
    have hp := mul_le_mul hllL (pow_le_pow_left₀ hld hldL 3)
      (pow_nonneg hld 3) hL
    have hscaled := mul_le_mul_of_nonneg_left hp (show 0 ≤ 300 * c by positivity)
    unfold actualFiniteSuiSquaredWidthEnvelope
    dsimp only [c, L] at hscaled ⊢
    nlinarith
  have henv0 := actual_envelope_nonnegative (X := X) lambda B delta hlambda hB hdelta hdeltaone T
  refine ⟨mul_nonneg henv0 hg.1, ?_⟩
  have hp := mul_le_mul henvelope hgL hg.1 (by positivity : 0 ≤ 2 * B + 300 * c * L ^ 4)
  calc
    _ ≤ (2 * B + 300 * c * L ^ 4) * (c * L) := hp
    _ = _ := by dsimp only [c, L, a]; ring

/-- The actual finite-kernel information gain times its derived uniform
source-width envelope is genuinely sublinear in integer sample time. -/
theorem actual_finite_sui_width_envelope_times_maximum_information_is_sublinear
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (hnormalized : ∀ x, kernel x x ≤ 1) (lambda B delta : ℝ)
    (hlambda : 0 < lambda) (hB : 0 ≤ B) (hdelta : 0 < delta) (hdeltaone : delta ≤ 1) :
    Tendsto (fun T : ℕ => actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta T *
      actualFiniteMaximumKernelInformationGain kernel lambda T / (T : ℝ)) atTop (𝓝 0) := by
  let a := 2 + lambda⁻¹ + delta⁻¹
  have ha : 0 < a := by dsimp only [a]; positivity
  have h1 := actual_shifted_scaled_log_power_divided_by_integer_time_tends_to_zero a ha 1
  have h5 := actual_shifted_scaled_log_power_divided_by_integer_time_tends_to_zero a ha 5
  have hdom := (h1.const_mul (2 * B * ((Fintype.card X : ℝ) / 2))).add
    (h5.const_mul (300 * ((Fintype.card X : ℝ) / 2) ^ 2))
  simp only [pow_one, mul_zero, add_zero] at hdom
  apply tendsto_const_nhds.squeeze' hdom
  · filter_upwards [eventually_ge_atTop 1] with T hT
    exact div_nonneg
      (actual_finite_envelope_information_product_has_a_log_polynomial_bound
        kernel hkernel hnormalized lambda B delta hlambda hB hdelta hdeltaone T).1 (Nat.cast_nonneg T)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have h := div_le_div_of_nonneg_right
      (actual_finite_envelope_information_product_has_a_log_polynomial_bound
        kernel hkernel hnormalized lambda B delta hlambda hB hdelta hdeltaone T).2 (Nat.cast_nonneg T)
    simpa only [a, add_div, mul_div_assoc] using h

/-- Consequently the literal source multiplier times the actual Gamma,
which grows by a log-cubed factor, is also genuinely sublinear. -/
theorem actual_source_sui_squared_width_times_maximum_information_is_sublinear
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (hnormalized : ∀ x, kernel x x ≤ 1) (lambda B delta : ℝ)
    (hlambda : 0 < lambda) (hB : 0 ≤ B) (hdelta : 0 < delta) (hdeltaone : delta ≤ 1) :
    Tendsto (fun T : ℕ => actualSourceSuiSquaredWidthMultiplier kernel lambda B delta T *
      actualFiniteMaximumKernelInformationGain kernel lambda T / (T : ℝ)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.squeeze'
    (actual_finite_sui_width_envelope_times_maximum_information_is_sublinear
      kernel hkernel hnormalized lambda B delta hlambda hB hdelta hdeltaone)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hg := actual_normalized_finite_kernel_maximum_information_has_the_cardinality_log_bound
      kernel hkernel hnormalized lambda hlambda T
    have hgamma : 0 ≤ actualFiniteMaximumKernelInformationGain kernel lambda T := hg.1
    have hlog : 0 ≤ Real.log ((T : ℝ) / delta) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hdelta]
      have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
      linarith
    unfold actualSourceSuiSquaredWidthMultiplier
    positivity
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hg := actual_normalized_finite_kernel_maximum_information_has_the_cardinality_log_bound
      kernel hkernel hnormalized lambda hlambda T
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (actual_source_sui_squared_width_is_bounded_by_the_finite_horizon_envelope
          kernel hkernel hnormalized lambda B delta hlambda hB hdelta hdeltaone T T (by omega) le_rfl) hg.1)
      (Nat.cast_nonneg T)

/-- A finite exact integer width-budget horizon exists for every positive
window count and epsilon. The derived envelope also bounds every actual
positive source-round standard-deviation multiplier through that horizon.
This supplies sufficient rounding, not the displayed minimal t-star. -/
theorem actual_finite_source_sui_run_has_a_positive_exact_integer_budget_horizon
    (kernel : X → X → ℝ) (hkernel : (Matrix.of kernel).PosSemidef)
    (hnormalized : ∀ x, kernel x x ≤ 1) (lambda B delta : ℝ)
    (hlambda : 0 < lambda) (hB : 0 ≤ B) (hdelta : 0 < delta) (hdeltaone : delta ≤ 1)
    (windows : ℕ) (hwindows : 0 < windows) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ horizon : ℕ,
      0 < horizon / windows ∧
      8 * (Real.sqrt (actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta horizon)) ^ 2 *
          actualFiniteMaximumKernelInformationGain kernel lambda horizon / Real.log (1 + lambda⁻¹) ≤
        ((horizon / windows : ℕ) : ℝ) * epsilon ^ 2 ∧
      windows * max 1 ⌈(8 * (Real.sqrt (actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta horizon)) ^ 2 *
          actualFiniteMaximumKernelInformationGain kernel lambda horizon / Real.log (1 + lambda⁻¹)) / epsilon ^ 2⌉₊ ≤ horizon ∧
      ∀ t : ℕ, 0 < t → t ≤ horizon →
        Real.sqrt (actualSourceSuiSquaredWidthMultiplier kernel lambda B delta t) ≤
          Real.sqrt (actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta horizon) := by
  let budget : ℕ → ℝ := fun T => 8 * actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta T *
    actualFiniteMaximumKernelInformationGain kernel lambda T / Real.log (1 + lambda⁻¹)
  have hratio : Tendsto (fun T : ℕ => budget T / (T : ℝ)) atTop (𝓝 0) := by
    have h := (actual_finite_sui_width_envelope_times_maximum_information_is_sublinear
      kernel hkernel hnormalized lambda B delta hlambda hB hdelta hdeltaone).const_mul
        (8 / Real.log (1 + lambda⁻¹))
    simp only [mul_zero] at h
    convert h using 1
    ext T
    dsimp only [budget]
    ring
  obtain ⟨horizon, hpositive, hwidth, hrounded⟩ :=
    actual_sublinear_width_budget_has_an_exact_positive_rounded_integer_horizon
      budget hratio windows hwindows epsilon hepsilon
  have hsquare : (Real.sqrt (actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta horizon)) ^ 2 =
      actualFiniteSuiSquaredWidthEnvelope (X := X) lambda B delta horizon :=
    Real.sq_sqrt (actual_envelope_nonnegative (X := X) lambda B delta hlambda hB hdelta hdeltaone horizon)
  refine ⟨horizon, hpositive, ?_, ?_, ?_⟩
  · simpa only [hsquare] using hwidth
  · simpa only [hsquare] using hrounded
  · intro t ht htH
    exact Real.sqrt_le_sqrt
      (actual_source_sui_squared_width_is_bounded_by_the_finite_horizon_envelope
        kernel hkernel hnormalized lambda B delta hlambda hB hdelta hdeltaone t horizon ht htH)

end SafeLearning.CompleteModulesSafeOptFiniteInformationGrowth
