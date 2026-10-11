import SafeLearning.CompleteModulesLandscapeSmallInformationPSD
import SafeLearning.CompleteModulesLandscapeSuiArithmetic

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace SafeLearning.CompleteModulesLandscapeSuiQuadratic
open Matrix
open scoped BigOperators
open CompleteModulesLandscapeSmallInformationPSD CompleteModulesLandscapeSuiArithmetic
open CompleteFoundationsTelescopingModels

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual regularized inverse quadratic is nonnegative for every
real vector, by positive definiteness derived from the actual PSD matrix. -/
theorem actual_positive_regularized_psd_inverse_quadratic_is_nonnegative
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (lambda : ℝ) (hlambda : 0 < lambda)
    (S : ι → ℝ) : 0 ≤ S ⬝ᵥ ((lambda • 1 + A)⁻¹ *ᵥ S) := by
  have hp : (lambda • (1 : Matrix ι ι ℝ) + A).PosDef :=
    (Matrix.PosDef.one.smul hlambda).add_posSemidef hA
  simpa only [star_trivial] using hp.inv.posSemidef.dotProduct_mulVec_nonneg S

/-- The usual actual normalized quadratic budget implies the printed
300 coefficient when the genuine information upper bound is at least one half. -/
theorem actual_large_information_inverse_budget_implies_source_three_hundred_bound
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (S : ι → ℝ)
    (R lambda Gamma delta : ℝ) (hR : 0 < R) (hlambda : 0 < lambda)
    (hscale : R ^ 2 ≤ lambda) (hGamma : 1 / 2 ≤ Gamma)
    (hd : 0 < delta) (hdone : delta < 1) (t : ℕ) (ht : 2 ≤ t)
    (hinfo : Real.log (1 + lambda⁻¹ • A).det ≤ 2 * Gamma)
    (hnoise : (1 / R ^ 2) * (S ⬝ᵥ ((lambda • 1 + A)⁻¹ *ᵥ S)) <
      Real.log (1 + lambda⁻¹ • A).det + 2 * Real.log (1 / failureShare delta (t - 2))) :
    2 * ((S ⬝ᵥ ((lambda • 1 + A)⁻¹ *ᵥ S)) / lambda) ≤
      300 * Gamma * (Real.log ((t : ℝ) / delta)) ^ 3 := by
  let q := S ⬝ᵥ ((lambda • 1 + A)⁻¹ *ᵥ S)
  let l := Real.log ((t : ℝ) / delta)
  have hq : 0 ≤ q := actual_positive_regularized_psd_inverse_quadratic_is_nonnegative A hA lambda hlambda S
  have hr : 0 < R ^ 2 := sq_pos_of_pos hR
  have hl : (2 / 3 : ℝ) ≤ l := actual_source_round_log_is_at_least_two_thirds delta hd hdone t ht
  have hlog : Real.log (1 / failureShare delta (t - 2)) ≤ 2 * l := by
    simpa only [one_div] using actual_source_failure_allocation_log_is_bounded_by_twice_the_source_log delta hd hdone t ht
  have hn : q / R ^ 2 ≤ 2 * Gamma + 4 * l := by
    have hh : q / R ^ 2 < Real.log (1 + lambda⁻¹ • A).det + 2 * Real.log (1 / failureShare delta (t - 2)) := by
      simpa only [q, one_div, div_eq_mul_inv, mul_comm] using hnoise
    linarith
  have hdiv : q / lambda ≤ q / R ^ 2 := div_le_div_of_nonneg_left hq hr hscale
  have hpoly := actual_four_plus_sixteen_log_is_bounded_by_three_hundred_log_cubed l hl
  have hg : 0 ≤ Gamma := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hmiddle : 2 * (q / lambda) ≤ Gamma * (4 + 16 * l) := by
    nlinarith [mul_nonneg (show 0 ≤ Gamma - 1 / 2 by linarith) hl0]
  exact hmiddle.trans (by nlinarith [mul_le_mul_of_nonneg_left hpoly hg])

/-- For genuinely small positive information, use the derived rescaled
log determinant and exact inverse comparison. The same printed coefficient
then bounds the actual original-regularizer quadratic. -/
theorem actual_small_information_inverse_budget_implies_source_three_hundred_bound
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (S : ι → ℝ)
    (R lambda Gamma delta : ℝ) (hR : 0 < R) (hlambda : 0 < lambda)
    (hscale : R ^ 2 ≤ lambda) (hGamma : 0 < Gamma) (hhalf : Gamma ≤ 1 / 2)
    (hd : 0 < delta) (hdone : delta < 1) (t : ℕ) (ht : 2 ≤ t)
    (hinfo : Real.log (1 + lambda⁻¹ • A).det ≤ 2 * Gamma)
    (hnoise : (1 / R ^ 2) * (S ⬝ᵥ (((lambda * Gamma) • 1 + A)⁻¹ *ᵥ S)) <
      Real.log (1 + (lambda * Gamma)⁻¹ • A).det + 2 * Real.log (1 / failureShare delta (t - 2))) :
    2 * ((S ⬝ᵥ ((lambda • 1 + A)⁻¹ *ᵥ S)) / lambda) ≤
      300 * Gamma * (Real.log ((t : ℝ) / delta)) ^ 3 := by
  let q := S ⬝ᵥ ((lambda • 1 + A)⁻¹ *ᵥ S)
  let qsmall := S ⬝ᵥ (((lambda * Gamma) • 1 + A)⁻¹ *ᵥ S)
  let l := Real.log ((t : ℝ) / delta)
  have hq : 0 ≤ q := actual_positive_regularized_psd_inverse_quadratic_is_nonnegative A hA lambda hlambda S
  have hr : 0 < R ^ 2 := sq_pos_of_pos hR
  have hl : (2 / 3 : ℝ) ≤ l := actual_source_round_log_is_at_least_two_thirds delta hd hdone t ht
  have hlog : Real.log (1 / failureShare delta (t - 2)) ≤ 2 * l := by
    simpa only [one_div] using actual_source_failure_allocation_log_is_bounded_by_twice_the_source_log delta hd hdone t ht
  have hdsmall := actual_small_psd_logdet_implies_gamma_regularized_logdet_at_most_four A hA lambda Gamma hlambda hGamma hhalf hinfo
  have hn : qsmall / R ^ 2 ≤ 4 + 4 * l := by
    have hh : qsmall / R ^ 2 < Real.log (1 + (lambda * Gamma)⁻¹ • A).det + 2 * Real.log (1 / failureShare delta (t - 2)) := by
      simpa only [qsmall, one_div, div_eq_mul_inv, mul_comm] using hnoise
    linarith
  have hc := actual_small_psd_logdet_implies_actual_inverse_quadratic_comparison A hA lambda Gamma hlambda hGamma hhalf hinfo S
  have hcdiv : q / R ^ 2 ≤ 5 * Gamma * (qsmall / R ^ 2) := by
    have hh := div_le_div_of_nonneg_right hc hr.le
    simpa only [q, qsmall, mul_div_assoc] using hh
  have hn' := mul_le_mul_of_nonneg_left hn (show 0 ≤ 5 * Gamma by positivity)
  have hdiv : q / lambda ≤ q / R ^ 2 := div_le_div_of_nonneg_left hq hr hscale
  have hpoly := actual_forty_times_one_plus_log_is_bounded_by_three_hundred_log_cubed l hl
  have hmiddle : 2 * (q / lambda) ≤ Gamma * (40 * (1 + l)) := by nlinarith
  exact hmiddle.trans (by nlinarith [mul_le_mul_of_nonneg_left hpoly hGamma.le])

end SafeLearning.CompleteModulesLandscapeSuiQuadratic
