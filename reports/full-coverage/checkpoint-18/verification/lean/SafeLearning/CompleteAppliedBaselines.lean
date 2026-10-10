import SafeLearning.CompleteAppliedBandit
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedBaselines
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedBandit
open scoped ENNReal NNReal

def gradientSample {Ω : Type*} (reward score : Ω → ℝ) (baseline : ℝ) (omega : Ω) : ℝ :=
  (reward omega - baseline) * score omega

theorem actual_general_baseline_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reward score : Ω → ℝ)
    (hscore : Integrable score μ) (hreward : Integrable (fun omega => reward omega * score omega) μ)
    (hzero : (∫ omega, score omega ∂μ) = 0) (baseline : ℝ) :
    (∫ omega, gradientSample reward score baseline omega ∂μ) =
      ∫ omega, reward omega * score omega ∂μ := by
  have he : gradientSample reward score baseline =
      (fun omega => reward omega * score omega - baseline * score omega) := by
    ext omega
    unfold gradientSample
    ring
  rw [he, integral_sub hreward (hscore.const_mul baseline), integral_const_mul, hzero]
  ring

theorem actual_baseline_variance_quadratic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X score : Ω → ℝ)
    (hX : MemLp X 2 μ) (hscore : MemLp score 2 μ) (baseline : ℝ) :
    variance (fun omega => X omega - baseline * score omega) μ =
      variance X μ - 2 * baseline * covariance X score μ + baseline ^ 2 * variance score μ := by
  rw [variance_fun_sub hX (hscore.const_mul baseline), covariance_const_mul_right,
    variance_const_mul]
  ring

theorem actual_variance_minimizing_baseline {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X score : Ω → ℝ)
    (hX : MemLp X 2 μ) (hscore : MemLp score 2 μ) (hpositive : 0 < variance score μ)
    (baseline : ℝ) :
    let optimal := covariance X score μ / variance score μ
    variance (fun omega => X omega - optimal * score omega) μ ≤
      variance (fun omega => X omega - baseline * score omega) μ ∧
    (variance (fun omega => X omega - baseline * score omega) μ =
      variance (fun omega => X omega - optimal * score omega) μ ↔ baseline = optimal) := by
  dsimp only
  have hgap : variance (fun omega => X omega - baseline * score omega) μ -
      variance (fun omega => X omega - (covariance X score μ / variance score μ) * score omega) μ =
      variance score μ * (baseline - covariance X score μ / variance score μ) ^ 2 := by
    rw [actual_baseline_variance_quadratic μ X score hX hscore,
      actual_baseline_variance_quadratic μ X score hX hscore]
    field_simp
    ring
  constructor
  · have hh := mul_nonneg hpositive.le
      (sq_nonneg (baseline - covariance X score μ / variance score μ))
    linarith
  · constructor
    · intro he
      have hz : (baseline - covariance X score μ / variance score μ) ^ 2 = 0 := by
        apply (mul_eq_zero.mp (show variance score μ *
          (baseline - covariance X score μ / variance score μ) ^ 2 = 0 by linarith)).resolve_left
        exact hpositive.ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    · intro he
      rw [he]

theorem actual_general_score_weighted_baseline_formula {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (reward score : Ω → ℝ)
    (hproduct : MemLp (fun omega => reward omega * score omega) 2 μ)
    (hscore : MemLp score 2 μ) (hzero : (∫ omega, score omega ∂μ) = 0) :
    covariance (fun omega => reward omega * score omega) score μ / variance score μ =
      (∫ omega, reward omega * score omega ^ 2 ∂μ) / (∫ omega, score omega ^ 2 ∂μ) := by
  rw [covariance_eq_sub hproduct hscore, variance_eq_sub hscore, hzero]
  simp only [mul_zero, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun omega => by simp only [Pi.mul_apply]; ring)

theorem actual_general_gradient_variance_moment_formula {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (reward score : Ω → ℝ)
    (hproduct : MemLp (fun omega => reward omega * score omega) 2 μ)
    (hscore : MemLp score 2 μ) (hzero : (∫ omega, score omega ∂μ) = 0) (baseline : ℝ) :
    variance (gradientSample reward score baseline) μ =
      (∫ omega, reward omega ^ 2 * score omega ^ 2 ∂μ) -
        2 * baseline * (∫ omega, reward omega * score omega ^ 2 ∂μ) +
        baseline ^ 2 * (∫ omega, score omega ^ 2 ∂μ) -
        (∫ omega, reward omega * score omega ∂μ) ^ 2 := by
  have he : gradientSample reward score baseline =
      (fun omega => reward omega * score omega - baseline * score omega) := by
    ext omega
    unfold gradientSample
    ring
  rw [he, actual_baseline_variance_quadratic μ _ _ hproduct hscore,
    variance_eq_sub hproduct, variance_eq_sub hscore, covariance_eq_sub hproduct hscore, hzero]
  simp only [Pi.pow_apply, Pi.mul_apply, mul_zero, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hcross : (∫ omega, (reward omega * score omega) * score omega ∂μ) =
      ∫ omega, reward omega * score omega ^ 2 ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun omega => by ring)
  have hsq : (∫ omega, (reward omega * score omega) ^ 2 ∂μ) =
      ∫ omega, reward omega ^ 2 * score omega ^ 2 ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun omega => by ring)
  rw [hcross, hsq]
  ring

theorem actual_general_score_weighted_variance_minimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (reward score : Ω → ℝ)
    (hproduct : MemLp (fun omega => reward omega * score omega) 2 μ)
    (hscore : MemLp score 2 μ) (hzero : (∫ omega, score omega ∂μ) = 0)
    (hpositive : 0 < ∫ omega, score omega ^ 2 ∂μ) (baseline : ℝ) :
    let optimal := (∫ omega, reward omega * score omega ^ 2 ∂μ) /
      (∫ omega, score omega ^ 2 ∂μ)
    variance (gradientSample reward score optimal) μ ≤ variance (gradientSample reward score baseline) μ ∧
    (variance (gradientSample reward score baseline) μ = variance (gradientSample reward score optimal) μ ↔
      baseline = optimal) := by
  dsimp only
  have hv : variance score μ = ∫ omega, score omega ^ 2 ∂μ := by
    rw [variance_eq_sub hscore, hzero]
    simp only [Pi.pow_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
  have he (b : ℝ) : gradientSample reward score b =
      (fun omega => reward omega * score omega - b * score omega) := by
    ext omega
    unfold gradientSample
    ring
  have hmin := actual_variance_minimizing_baseline μ (fun omega => reward omega * score omega) score
    hproduct hscore (by simpa only [hv] using hpositive) baseline
  rw [actual_general_score_weighted_baseline_formula μ reward score hproduct hscore hzero] at hmin
  simpa only [← he] using hmin

theorem finite_variance_is_actual_variance {n : ℕ} (law : PMF (Fin n)) (X : Fin n → ℝ) :
    finiteVariance law X = variance X law.toMeasure := by
  rw [variance_eq_integral (measurable_of_finite X).aemeasurable]
  simp only [← finite_expectation_is_actual_integral, finiteVariance]

def unitReward : Fin 2 → ℝ := ![1, 0]
def unitGradient (theta baseline : ℝ) (i : Fin 2) : ℝ :=
  gradientSample unitReward (score theta) baseline i

theorem unit_gradient_actual_mean (theta baseline : ℝ) :
    finiteExpectation (policy theta) (unitGradient theta baseline) =
      Real.sigmoid theta * (1 - Real.sigmoid theta) := by
  rw [binary_expectation]
  simp only [unitGradient, gradientSample, unitReward, score,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem unit_gradient_actual_second_moment (theta baseline : ℝ) :
    finiteExpectation (policy theta) (fun i => (unitGradient theta baseline i) ^ 2) =
      Real.sigmoid theta * (1 - baseline) ^ 2 * (1 - Real.sigmoid theta) ^ 2 +
        (1 - Real.sigmoid theta) * baseline ^ 2 * Real.sigmoid theta ^ 2 := by
  rw [binary_expectation]
  simp only [unitGradient, gradientSample, unitReward, score,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem unit_gradient_second_moment_actual_derivative (theta baseline : ℝ) :
    HasDerivAt (fun b => finiteExpectation (policy theta) (fun i => (unitGradient theta b i) ^ 2))
      (2 * Real.sigmoid theta * (1 - Real.sigmoid theta) *
        (baseline - (1 - Real.sigmoid theta))) baseline := by
  simp only [unit_gradient_actual_second_moment]
  convert (((hasDerivAt_const baseline 1).sub (hasDerivAt_id baseline)).pow 2
    |>.const_mul (Real.sigmoid theta) |>.mul_const ((1 - Real.sigmoid theta) ^ 2)).add
    (((hasDerivAt_id baseline).pow 2).const_mul (1 - Real.sigmoid theta)
      |>.mul_const (Real.sigmoid theta ^ 2)) using 1
  · ext b
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    ring

theorem unit_gradient_actual_variance (theta baseline : ℝ) :
    finiteVariance (policy theta) (unitGradient theta baseline) =
      Real.sigmoid theta * (1 - Real.sigmoid theta) *
        (baseline - (1 - Real.sigmoid theta)) ^ 2 := by
  unfold finiteVariance
  rw [unit_gradient_actual_mean, binary_expectation]
  simp only [unitGradient, gradientSample, unitReward, score,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem unit_gradient_optimal_baseline_constant (theta : ℝ) :
    (∀ i, unitGradient theta (1 - Real.sigmoid theta) i =
      Real.sigmoid theta * (1 - Real.sigmoid theta)) ∧
    finiteVariance (policy theta) (unitGradient theta (1 - Real.sigmoid theta)) = 0 ∧
    ∀ baseline, finiteVariance (policy theta) (unitGradient theta (1 - Real.sigmoid theta)) ≤
      finiteVariance (policy theta) (unitGradient theta baseline) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [unitGradient, gradientSample, unitReward, score] <;> ring
  · simp [unit_gradient_actual_variance]
  · intro baseline
    simp only [unit_gradient_actual_variance, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    exact mul_nonneg (mul_nonneg (Real.sigmoid_pos theta).le
      (sub_pos.mpr (Real.sigmoid_lt_one theta)).le) (sq_nonneg _)

theorem unit_gradient_unique_optimal_baseline (theta baseline : ℝ) :
    finiteVariance (policy theta) (unitGradient theta baseline) = 0 ↔
      baseline = 1 - Real.sigmoid theta := by
  rw [unit_gradient_actual_variance]
  have hp : Real.sigmoid theta * (1 - Real.sigmoid theta) ≠ 0 :=
    (mul_pos (Real.sigmoid_pos theta) (sub_pos.mpr (Real.sigmoid_lt_one theta))).ne'
  rw [mul_eq_zero]
  simp [hp, sq_eq_zero_iff, sub_eq_zero]

theorem unit_score_squared_moments (theta : ℝ) :
    finiteExpectation (policy theta) (fun i => unitReward i * (score theta i) ^ 2) =
      Real.sigmoid theta * (1 - Real.sigmoid theta) ^ 2 ∧
    finiteExpectation (policy theta) (fun i => (score theta i) ^ 2) =
      Real.sigmoid theta * (1 - Real.sigmoid theta) := by
  constructor <;> rw [binary_expectation] <;>
    simp only [unitReward, score, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

theorem actual_unit_score_weighted_baseline_ratio (theta : ℝ) :
    finiteExpectation (policy theta) (fun i => unitReward i * (score theta i) ^ 2) /
      finiteExpectation (policy theta) (fun i => (score theta i) ^ 2) =
        1 - Real.sigmoid theta := by
  rw [(unit_score_squared_moments theta).1, (unit_score_squared_moments theta).2]
  have hp : Real.sigmoid theta ≠ 0 := (Real.sigmoid_pos theta).ne'
  have hq : 1 - Real.sigmoid theta ≠ 0 := (sub_pos.mpr (Real.sigmoid_lt_one theta)).ne'
  field_simp <;> ring

theorem four_fifths_parameter : Real.sigmoid (Real.log 4) = (4 / 5 : ℝ) := by
  rw [Real.sigmoid_def, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  norm_num

theorem four_fifths_actual_variance_comparison :
    unitGradient (Real.log 4) 0 0 = 1 / 5 ∧ unitGradient (Real.log 4) 0 1 = 0 ∧
    unitGradient (Real.log 4) (4 / 5) 0 = 1 / 25 ∧
    unitGradient (Real.log 4) (4 / 5) 1 = 16 / 25 ∧
    finiteVariance (policy (Real.log 4)) (unitGradient (Real.log 4) 0) = 4 / 625 ∧
    finiteVariance (policy (Real.log 4)) (unitGradient (Real.log 4) (4 / 5)) = 36 / 625 ∧
    finiteVariance (policy (Real.log 4)) (unitGradient (Real.log 4) (1 / 5)) = 0 ∧
    finiteVariance (policy (Real.log 4)) (unitGradient (Real.log 4) (4 / 5)) =
      9 * finiteVariance (policy (Real.log 4)) (unitGradient (Real.log 4) 0) := by
  norm_num [unitGradient, gradientSample, unitReward, score,
    unit_gradient_actual_variance, four_fifths_parameter]

end SafeLearning.CompleteAppliedBaselines
