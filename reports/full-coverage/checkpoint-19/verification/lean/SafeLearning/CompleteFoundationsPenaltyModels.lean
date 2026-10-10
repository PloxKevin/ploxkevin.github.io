import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsPenaltyModels

def objective (x : ℝ) : ℝ := (x-2)^2
def constraint (x : ℝ) : ℝ := x-1
def quadraticPenalty (rho x : ℝ) : ℝ := objective x+rho/2*(max (x-1) 0)^2
def candidate (rho : ℝ) : ℝ := (4+rho)/(2+rho)

theorem actual_objective_derivative (x : ℝ) : HasDerivAt objective (2*(x-2)) x := by
  unfold objective
  convert ((hasDerivAt_id x).sub_const 2).pow 2 using 1
  · rfl
  · norm_num [id_eq]

theorem actual_constraint_derivative (x : ℝ) : HasDerivAt constraint 1 x := by
  unfold constraint
  exact (hasDerivAt_id x).sub_const 1

theorem actual_penalty_branch_formulas (rho x : ℝ) :
    (x ≤ 1 → quadraticPenalty rho x=objective x) ∧
    (1 ≤ x → quadraticPenalty rho x=objective x+rho/2*(x-1)^2) := by
  constructor
  · intro h
    simp only [quadraticPenalty,max_eq_right (show x-1 ≤ 0 by linarith)]
    ring
  · intro h
    rw [quadraticPenalty,max_eq_left (show 0 ≤ x-1 by linarith)]

theorem actual_right_polynomial_derivative (rho x : ℝ) :
    HasDerivAt (fun y : ℝ => objective y+rho/2*(y-1)^2)
      (2*(x-2)+rho*(x-1)) x := by
  convert (actual_objective_derivative x).add
    ((((hasDerivAt_id x).sub_const 1).pow 2).const_mul (rho/2)) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem actual_penalty_derivative_below_one (rho x : ℝ) (hx : x < 1) :
    HasDerivAt (quadraticPenalty rho) (2*(x-2)) x := by
  apply (actual_objective_derivative x).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hx] with y hy
  exact (actual_penalty_branch_formulas rho y).1 hy.le

theorem actual_penalty_derivative_above_one (rho x : ℝ) (hx : 1 < x) :
    HasDerivAt (quadraticPenalty rho) (2*(x-2)+rho*(x-1)) x := by
  apply (actual_right_polynomial_derivative rho x).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact (actual_penalty_branch_formulas rho y).2 hy.le

theorem actual_right_polynomial_curvature (rho x : ℝ) :
    HasDerivAt (fun y : ℝ => 2*(y-2)+rho*(y-1)) (2+rho) x := by
  convert (((hasDerivAt_id x).sub_const 2).const_mul 2).add
    (((hasDerivAt_id x).sub_const 1).const_mul rho) using 1
  · rfl
  · simp

theorem actual_objective_decreases_to_branch_endpoint : StrictAntiOn objective (Iic 2) := by
  intro x hx y hy hxy
  change x ≤ 2 at hx
  change y ≤ 2 at hy
  have hp := mul_pos (sub_pos.mpr hxy) (show 0 < 4-x-y by linarith)
  dsimp [objective]
  nlinarith

theorem actual_penalty_candidate_violation (rho : ℝ) (hrho : 0 ≤ rho) :
    candidate rho-1=2/(2+rho) ∧ 1 < candidate rho := by
  have hd : 0 < 2+rho := by linarith
  have he : candidate rho-1=2/(2+rho) := by
    unfold candidate
    field_simp
    ring
  refine ⟨he,?_⟩
  have hp := div_pos (show (0 : ℝ) < 2 by norm_num) hd
  linarith

theorem actual_right_branch_completed_square (rho x : ℝ) (hrho : 0 ≤ rho) :
    objective x+rho/2*(x-1)^2=
      (2+rho)/2*(x-candidate rho)^2+rho/(2+rho) := by
  have hd : 2+rho ≠ 0 := by linarith
  unfold objective candidate
  field_simp
  <;> ring

theorem actual_penalty_generic_unique_global_optimum (rho : ℝ) (hrho : 0 ≤ rho) (x : ℝ) :
    rho/(2+rho) ≤ quadraticPenalty rho x ∧
      (quadraticPenalty rho x=rho/(2+rho) ↔ x=candidate rho) := by
  have hd : 0 < 2+rho := by linarith
  have hless : rho/(2+rho) < 1 := (div_lt_one hd).mpr (by linarith)
  by_cases hx : x ≤ 1
  · rw [(actual_penalty_branch_formulas rho x).1 hx]
    have hobj : 1 ≤ objective x := by dsimp [objective];nlinarith [sq_nonneg (x-1)]
    refine ⟨by linarith,?_⟩
    constructor
    · intro he
      linarith
    · intro he
      have hc := (actual_penalty_candidate_violation rho hrho).2
      rw [he] at hx
      linarith
  · rw [(actual_penalty_branch_formulas rho x).2 (by linarith),
      actual_right_branch_completed_square rho x hrho]
    have hp : 0 ≤ (2+rho)/2*(x-candidate rho)^2 := by positivity
    refine ⟨by linarith,?_⟩
    constructor
    · intro he
      have hz : (x-candidate rho)^2=0 := by nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    · rintro rfl
      simp

theorem actual_practice_penalty_derivative_and_curvature (x : ℝ) :
    HasDerivAt (fun y : ℝ => objective y+3*(y-1)^2) (8*x-10) x ∧
    HasDerivAt (fun y : ℝ => 8*y-10) 8 x ∧ (0 : ℝ) < 8 := by
  have h := actual_right_polynomial_derivative 6 x
  have hc := actual_right_polynomial_curvature 6 x
  refine ⟨?_,?_,by norm_num⟩
  · convert h using 1 <;> norm_num <;> ring
  · convert hc using 1
    · funext y
      ring
    · norm_num

theorem actual_penalty_second_derivative_above_one (rho x : ℝ) (hx : 1 < x) :
    HasDerivAt (deriv (quadraticPenalty rho)) (2+rho) x := by
  apply (actual_right_polynomial_curvature rho x).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact (actual_penalty_derivative_above_one rho y hy).deriv

theorem actual_candidate_true_stationarity (rho : ℝ) (hrho : 0 ≤ rho) :
    HasDerivAt (quadraticPenalty rho) 0 (candidate rho) := by
  have hd : 2+rho ≠ 0 := by linarith
  convert actual_penalty_derivative_above_one rho (candidate rho)
    (actual_penalty_candidate_violation rho hrho).2 using 1
  unfold candidate
  field_simp
  <;> ring

theorem actual_practice_penalty_values_and_infeasibility :
    candidate 6=5/4 ∧ quadraticPenalty 6 (5/4)=3/4 ∧
    objective (5/4)=9/16 ∧ max ((5/4 : ℝ)-1) 0=1/4 ∧
    quadraticPenalty 6 1=1 ∧ (3/4 : ℝ) < 1 ∧ constraint (5/4)=1/4 ∧
    ¬ constraint (5/4) ≤ 0 := by
  norm_num [candidate,quadraticPenalty,objective,constraint]

def epsilonKKT (x multiplier epsilon : ℝ) : Prop :=
  constraint x ≤ 0 ∧ 0 ≤ multiplier ∧
  ‖gradient objective x+multiplier*gradient constraint x‖ ≤ epsilon ∧
  multiplier*(-constraint x) ≤ epsilon

theorem actual_gradients_and_stationarity_residual (x multiplier : ℝ) :
    gradient objective x=2*(x-2) ∧ gradient constraint x=1 ∧
    ‖gradient objective x+multiplier*gradient constraint x‖=|2*(x-2)+multiplier| := by
  rw [(actual_objective_derivative x).hasGradientAt'.gradient,
    (actual_constraint_derivative x).hasGradientAt'.gradient]
  simp [Real.norm_eq_abs]

theorem actual_practice_approximate_kkt_numbers :
    constraint (9/10)= -1/10 ∧ (0 : ℝ) ≤ 11/5 ∧
    ‖gradient objective (9/10)+(11/5)*gradient constraint (9/10)‖=0 ∧
    (11/5 : ℝ)*(-constraint (9/10))=11/50 ∧
    constraint (9/10) < 0 ∧ (0 : ℝ) < 11/5 := by
  rw [(actual_gradients_and_stationarity_residual (9/10) (11/5)).2.2]
  norm_num [constraint]

theorem actual_practice_minimal_epsilon (epsilon : ℝ) :
    epsilonKKT (9/10) (11/5) epsilon ↔ 11/50 ≤ epsilon := by
  unfold epsilonKKT
  rw [(actual_gradients_and_stationarity_residual (9/10) (11/5)).2.2]
  norm_num [constraint]
  intro he
  linarith

theorem actual_practice_not_exact_kkt_despite_zero_stationarity :
    ¬ epsilonKKT (9/10) (11/5) 0 ∧
    (11/5 : ℝ)*constraint (9/10) ≠ 0 := by
  rw [actual_practice_minimal_epsilon]
  norm_num [constraint]

end SafeLearning.CompleteFoundationsPenaltyModels
