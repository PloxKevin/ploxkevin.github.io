import SafeLearning.CompleteAppliedFiniteClaims
import SafeLearning.CompleteAppliedElementary
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedBandit
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedFiniteClaims
open scoped NNReal ENNReal

def policy (theta : ℝ) : PMF (Fin 2) := PMF.ofFintype
  (fun i => ENNReal.ofReal ((![Real.sigmoid theta, 1 - Real.sigmoid theta] : Fin 2 → ℝ) i))
  (by
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_zero, add_zero]
    change ENNReal.ofReal (Real.sigmoid theta) + ENNReal.ofReal (1 - Real.sigmoid theta) = 1
    rw [← ENNReal.ofReal_add (Real.sigmoid_pos theta).le
      (sub_nonneg.mpr (Real.sigmoid_lt_one theta).le)]
    simp)

def score (theta : ℝ) : Fin 2 → ℝ := ![1 - Real.sigmoid theta, -Real.sigmoid theta]
def advantage (theta : ℝ) (baseline : ℝ) (i : Fin 2) : ℝ := actionReward i - baseline

theorem finite_expectation_is_actual_integral {n : ℕ} (law : PMF (Fin n)) (X : Fin n → ℝ) :
    finiteExpectation law X = ∫ i, X i ∂law.toMeasure := by
  rw [PMF.integral_eq_sum]
  rfl

theorem binary_expectation (theta : ℝ) (X : Fin 2 → ℝ) :
    finiteExpectation (policy theta) X = Real.sigmoid theta * X 0 +
      (1 - Real.sigmoid theta) * X 1 := by
  simp only [finiteExpectation, policy, PMF.ofFintype_apply, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_zero, add_zero]
  change (ENNReal.ofReal (Real.sigmoid theta)).toReal * X 0 +
    (ENNReal.ofReal (1 - Real.sigmoid theta)).toReal * X 1 = _
  rw [ENNReal.toReal_ofReal (Real.sigmoid_pos theta).le,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.sigmoid_lt_one theta).le)]

theorem actual_expected_reward (theta : ℝ) :
    finiteExpectation (policy theta) actionReward = 4 * Real.sigmoid theta := by
  rw [binary_expectation]
  simp [actionReward]
  ring

theorem sigmoid_probability_derivative (theta : ℝ) :
    HasDerivAt Real.sigmoid (Real.sigmoid theta * (1 - Real.sigmoid theta)) theta :=
  Real.hasDerivAt_sigmoid theta

theorem both_actual_log_probability_scores (theta : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (Real.sigmoid t)) (score theta 0) theta ∧
      HasDerivAt (fun t : ℝ => Real.log (1 - Real.sigmoid t)) (score theta 1) theta := by
  constructor
  · simpa [score] using SafeLearning.CompleteAppliedElementary.score_log_sigmoid theta
  · have hn : 1 - Real.sigmoid theta ≠ 0 := (sub_pos.mpr (Real.sigmoid_lt_one theta)).ne'
    have hd := ((hasDerivAt_const theta 1).sub (Real.hasDerivAt_sigmoid theta)).log hn
    simp only [Pi.sub_apply] at hd
    have he : (0 - Real.sigmoid theta * (1 - Real.sigmoid theta)) /
        (1 - Real.sigmoid theta) = score theta 1 := by
      simp only [score, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp
      ring
    rw [he] at hd
    exact hd

theorem actual_reward_derivative (theta : ℝ) :
    HasDerivAt (fun t => finiteExpectation (policy t) actionReward)
      (4 * Real.sigmoid theta * (1 - Real.sigmoid theta)) theta := by
  simpa only [actual_expected_reward] using
    SafeLearning.CompleteAppliedElementary.reward_sigmoid_derivative theta

theorem actual_score_identity (theta : ℝ) : finiteExpectation (policy theta) (score theta) = 0 := by
  rw [binary_expectation]
  simp only [score, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem any_constant_baseline_same_gradient (theta baseline : ℝ) :
    finiteExpectation (policy theta) (fun i => advantage theta baseline i * score theta i) =
      4 * Real.sigmoid theta * (1 - Real.sigmoid theta) ∧
    finiteExpectation (policy theta) (fun i => actionReward i * score theta i) =
      4 * Real.sigmoid theta * (1 - Real.sigmoid theta) := by
  constructor <;> rw [binary_expectation] <;>
    simp only [advantage, actionReward, score, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

theorem actual_value_advantage_centered (theta : ℝ) :
    finiteExpectation (policy theta) (advantage theta
      (finiteExpectation (policy theta) actionReward)) = 0 := by
  rw [actual_expected_reward, binary_expectation]
  simp only [advantage, actionReward, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem quarter_sigmoid_parameter : Real.sigmoid (-Real.log 3) = (1 / 4 : ℝ) := by
  rw [Real.sigmoid_def]
  norm_num [Real.exp_log]

theorem quarter_reward_and_scores :
    finiteExpectation (policy (-Real.log 3)) actionReward = 1 ∧
      score (-Real.log 3) 0 = 3 / 4 ∧ score (-Real.log 3) 1 = -1 / 4 ∧
      HasDerivAt (fun t => finiteExpectation (policy t) actionReward) (3 / 4) (-Real.log 3) := by
  have hd := actual_reward_derivative (-Real.log 3)
  rw [quarter_sigmoid_parameter] at hd
  norm_num [actual_expected_reward, score, quarter_sigmoid_parameter] at hd ⊢
  exact hd

theorem quarter_actual_advantages :
    advantage (-Real.log 3) 1 0 = 3 ∧ advantage (-Real.log 3) 1 1 = -1 ∧
      finiteExpectation (policy (-Real.log 3)) (advantage (-Real.log 3) 1) = 0 ∧
      finiteExpectation (policy (-Real.log 3))
        (fun i => advantage (-Real.log 3) 1 i * score (-Real.log 3) i) = 3 / 4 ∧
      (1 / 4 : ℝ) * 3 * (3 / 4) = 9 / 16 ∧
      (3 / 4 : ℝ) * (-1) * (-1 / 4) = 3 / 16 := by
  norm_num [advantage, actionReward, binary_expectation, score, quarter_sigmoid_parameter]

end SafeLearning.CompleteAppliedBandit
