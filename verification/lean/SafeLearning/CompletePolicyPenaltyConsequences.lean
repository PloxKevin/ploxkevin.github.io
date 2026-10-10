import SafeLearning.CompleteFoundationsExactPenaltyModels

set_option autoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompletePolicyPenaltyConsequences

open SafeLearning.CompleteFoundationsPenaltyModels SafeLearning.CompleteFoundationsExactPenaltyModels

theorem actual_hard_constraint_unique_minimum (x : ℝ) (hx : constraint x ≤ 0) :
    objective 1 ≤ objective x ∧ (objective x = objective 1 ↔ x = 1) := by
  dsimp [constraint] at hx
  have h1 : objective 1 = 1 := by norm_num [objective]
  rw [h1]
  unfold objective
  constructor
  · nlinarith [sq_nonneg (x - 1)]
  · constructor <;> intro h <;> nlinarith [sq_nonneg (x - 1)]

theorem actual_unconstrained_minimum_is_infeasible :
    (∀ x : ℝ, objective 2 ≤ objective x) ∧ ¬ constraint 2 ≤ 0 := by
  constructor
  · intro x
    norm_num [objective]
    exact sq_nonneg _
  · norm_num [constraint]

theorem actual_hard_source_kkt_multiplier :
    constraint 1 = 0 ∧ (0 : ℝ) ≤ 2 ∧ (2 : ℝ) * constraint 1 = 0 ∧
    HasDerivAt (fun x : ℝ => objective x + 2 * constraint x) 0 1 := by
  refine ⟨by norm_num [constraint], by norm_num, by norm_num [constraint], ?_⟩
  convert (actual_objective_derivative 1).add ((actual_constraint_derivative 1).const_mul 2)
    using 1 <;> norm_num

theorem actual_relu_left_branch_decreasing (κ : ℝ) :
    StrictAntiOn (exactPenalty κ) (Iic 1) := by
  intro x hx y hy hxy
  rw [(actual_exact_penalty_branches κ x).1 hx,
    (actual_exact_penalty_branches κ y).1 hy]
  apply actual_objective_decreases_to_branch_endpoint
    (show x ∈ Iic 2 by simp only [mem_Iic] at hx ⊢;linarith)
    (show y ∈ Iic 2 by simp only [mem_Iic] at hy ⊢;linarith) hxy

theorem actual_relu_upper_weight_right_branch_increasing (κ : ℝ) (hκ : 2 ≤ κ) :
    StrictMonoOn (exactPenalty κ) (Ioi 1) := by
  intro x hx y hy hxy
  rw [(actual_exact_penalty_branches κ x).2 (by exact hx.le),
    (actual_exact_penalty_branches κ y).2 (by exact hy.le)]
  have hp := mul_pos (sub_pos.mpr hxy) (show 0 < x + y + κ - 4 by
    simp only [mem_Ioi] at hx hy;linarith)
  dsimp [objective]
  nlinarith

theorem actual_relu_source_numeric_weight_one :
    (∀ x : ℝ, exactPenalty 1 (3 / 2) ≤ exactPenalty 1 x) ∧
      constraint (3 / 2) = 1 / 2 := by
  constructor
  · intro x
    have h := (actual_exact_penalty_below_weight_global_unique 1
      (by norm_num) (by norm_num) x).1
    norm_num [exactPenalty, objective] at h ⊢
    exact h
  · norm_num [constraint]

theorem actual_quadratic_source_violation_values :
    candidate 10 - 1 = 1 / 6 ∧ candidate 100 - 1 = 1 / 51 ∧
      (1665 / 10000 : ℝ) < candidate 10 - 1 ∧ candidate 10 - 1 < 1675 / 10000 ∧
      (195 / 10000 : ℝ) < candidate 100 - 1 ∧ candidate 100 - 1 < 205 / 10000 := by
  norm_num [candidate]

def linearPenalty (κ x : ℝ) : ℝ := -x + κ * max x 0

theorem actual_linear_hard_minimum_and_multiplier :
    (∀ x : ℝ, x ≤ 0 → 0 ≤ -x) ∧
      HasDerivAt (fun x : ℝ => -x + 1 * x) 0 0 := by
  refine ⟨fun x hx => neg_nonneg.mpr hx, ?_⟩
  have he : (fun x : ℝ => -x + 1 * x) = fun _ => (0 : ℝ) := by funext x;ring
  rw [he]
  exact hasDerivAt_const _ _

theorem actual_linear_equal_threshold_all_minima (x : ℝ) :
    linearPenalty 1 x = max (-x) 0 ∧ 0 ≤ linearPenalty 1 x ∧
      (linearPenalty 1 x = 0 ↔ 0 ≤ x) := by
  by_cases hx : 0 ≤ x
  · simp [linearPenalty, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), hx]
  · have hneg : x < 0 := lt_of_not_ge hx
    have hpos : 0 < -x := neg_pos.mpr hneg
    simp [linearPenalty, max_eq_right hneg.le, max_eq_left hpos.le, hx, ne_of_gt hpos, hneg.le]

theorem actual_linear_strict_threshold_unique_minimum (κ x : ℝ) (hκ : 1 < κ) :
    0 ≤ linearPenalty κ x ∧ (linearPenalty κ x = 0 ↔ x = 0) := by
  by_cases hx : 0 ≤ x
  · have he : linearPenalty κ x = (κ - 1) * x := by
      rw [linearPenalty, max_eq_left hx]
      ring
    rw [he]
    refine ⟨mul_nonneg (by linarith) hx, ?_⟩
    rw [mul_eq_zero]
    simp [show κ - 1 ≠ 0 by linarith]
  · have hneg : x < 0 := lt_of_not_ge hx
    have hpos : 0 < -x := neg_pos.mpr hneg
    simp [linearPenalty, max_eq_right hneg.le, hx, ne_of_gt hpos, ne_of_lt hneg, hneg.le]

theorem actual_linear_below_threshold_unbounded (κ bound : ℝ) (hκ : κ < 1) :
    ∃ x : ℝ, linearPenalty κ x < bound := by
  have hd : 0 < 1 - κ := by linarith
  let x : ℝ := (|bound| + 1) / (1 - κ)
  have hx : 0 < x := div_pos (by positivity) hd
  have he : linearPenalty κ x = -(|bound| + 1) := by
    rw [linearPenalty, max_eq_left hx.le]
    dsimp [x]
    field_simp
    <;> ring
  refine ⟨x, ?_⟩
  rw [he]
  linarith [neg_abs_le bound]

theorem actual_capped_penalty_schedule (κ ρ cap : ℝ) (hκ : 0 ≤ κ)
    (hρ : 1 ≤ ρ) (hcap : κ ≤ cap) : κ ≤ min (ρ * κ) cap ∧ min (ρ * κ) cap ≤ cap := by
  refine ⟨le_min ?_ hcap, min_le_right _ _⟩
  nlinarith

end SafeLearning.CompletePolicyPenaltyConsequences
