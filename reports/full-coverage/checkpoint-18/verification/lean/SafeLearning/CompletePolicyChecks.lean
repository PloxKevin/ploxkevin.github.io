import Mathlib

set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace SafeLearning.CompletePolicyChecks

def linearResidual (x : Fin 2 → ℝ) : ℝ :=
  -1 / 5 + dotProduct (![1, 0] : Fin 2 → ℝ) x

theorem actual_affine_residual (x : Fin 2 → ℝ) :
    linearResidual x = -1 / 5 + x 0 := by
  simp [linearResidual, dotProduct, Fin.sum_univ_two]

theorem actual_linearized_tests :
    linearResidual ![3 / 10, 1 / 10] = 1 / 10 ∧
      ¬ linearResidual ![3 / 10, 1 / 10] ≤ 0 ∧
      linearResidual ![1 / 10, 1 / 10] = -1 / 10 ∧
      linearResidual ![1 / 10, 1 / 10] ≤ 0 := by
  norm_num [actual_affine_residual]

def nonlinearResidual (x : Fin 2 → ℝ) : ℝ := linearResidual x + 20 * x 0 ^ 2

theorem actual_curvature_counterexample :
    linearResidual ![1 / 10, 1 / 10] ≤ 0 ∧
      0 < nonlinearResidual ![1 / 10, 1 / 10] := by
  norm_num [nonlinearResidual, actual_affine_residual]

theorem actual_error_margin_transfer (trueResidual : (Fin 2 → ℝ) → ℝ)
    (x : Fin 2 → ℝ) (error : ℝ)
    (herror : trueResidual x - linearResidual x ≤ error)
    (hmargin : linearResidual x ≤ -error) : trueResidual x ≤ 0 := by
  linarith

def surrogateBound (gamma epsilon variation : ℝ) : ℝ :=
  2 * gamma * epsilon * variation / (1 - gamma) ^ 2

theorem actual_discount_bound_values :
    surrogateBound (9 / 10) (1 / 2) (1 / 100) = 9 / 10 ∧
      surrogateBound (1 / 2) (1 / 2) (1 / 100) = 1 / 50 ∧
      surrogateBound (9 / 10) (1 / 2) (1 / 100) =
        45 * surrogateBound (1 / 2) (1 / 2) (1 / 100) := by
  norm_num [surrogateBound]

theorem surrogate_upper_bound_allows_zero_actual_error :
    (0 : ℝ) ≤ surrogateBound (9 / 10) (1 / 2) (1 / 100) ∧
      0 < surrogateBound (9 / 10) (1 / 2) (1 / 100) := by
  norm_num [surrogateBound]

theorem actual_pessimistic_cost_checks :
    (7 : ℝ) + 2 = 9 ∧ ¬ (7 : ℝ) + 2 ≤ 8 ∧
      (5 : ℝ) + 2 = 7 ∧ (5 : ℝ) + 2 ≤ 8 ∧
      (7 : ℝ) ≤ 7 + 2 ∧ (7 : ℝ) ≤ 8 ∧
      (9 : ℝ) ≤ 7 + 2 ∧ ¬ (9 : ℝ) ≤ 8 := by
  norm_num

theorem valid_upper_bound_transfers_feasibility (cost estimate error budget : ℝ)
    (hu : cost ≤ estimate + error) (hc : estimate + error ≤ budget) :
    cost ≤ budget := le_trans hu hc

theorem actual_confidence_event_transfers_to_feasibility
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (event : Set Ω)
    (cost estimate : Ω → ℝ) (error budget confidence : ℝ)
    (hm : MeasurableSet {ω | cost ω ≤ budget})
    (hp : confidence ≤ μ.real event)
    (hu : ∀ ω ∈ event, cost ω ≤ estimate ω + error)
    (hc : ∀ ω ∈ event, estimate ω + error ≤ budget) :
    confidence ≤ μ.real {ω | cost ω ≤ budget} := by
  exact hp.trans (measureReal_mono (fun ω hω => le_trans (hu ω hω) (hc ω hω)))

end SafeLearning.CompletePolicyChecks
