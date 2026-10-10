import Mathlib

open Matrix
namespace SafeLearning.CompleteChowLP21

def transition : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1/5, 4/5; 0, 0, 1/2; 0, 1/10, 0]

def fundamental : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 28/95, 18/19; 0, 20/19, 10/19; 0, 2/19, 20/19]

def constraintCost : Fin 3 → ℝ := ![0, 1, 0]
def baselineValue : Fin 3 → ℝ := ![28/95, 20/19, 2/19]

theorem actual_left_inverse : (1-transition)*fundamental = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transition, fundamental, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.sub_apply]

theorem actual_right_inverse : fundamental*(1-transition) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transition, fundamental, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.sub_apply]

theorem actual_value_solves_full_bellman_equation :
    baselineValue = constraintCost + transition.mulVec baselineValue := by
  ext i
  fin_cases i <;> norm_num [baselineValue, constraintCost, transition,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem actual_inverse_cost_vector :
    fundamental.mulVec constraintCost = baselineValue := by
  ext i
  fin_cases i <;> norm_num [fundamental, constraintCost, baselineValue,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def weightedSlack (e : Fin 3 → ℝ) : ℝ := e 0 + 28/95*e 1 + 18/19*e 2
def objective (e : Fin 3 → ℝ) : ℝ := e 0 + e 1 + e 2
def lpFeasible (e : Fin 3 → ℝ) : Prop :=
  (∀ i, 0 ≤ e i) ∧ weightedSlack e ≤ 39/190
def vertex : Fin 3 → ℝ := ![0, 39/56, 0]
def constantSlack : Fin 3 → ℝ := fun _ => 13/142
def vertexLyapunov : Fin 3 → ℝ := ![1/2, 25/14, 5/28]
def constantLyapunov : Fin 3 → ℝ := ![1/2, 85/71, 15/71]

theorem actual_lp_coefficients_are_the_exact_first_row (e : Fin 3 → ℝ) :
    (fundamental.mulVec e) 0 = weightedSlack e := by
  norm_num [fundamental, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, weightedSlack]

theorem actual_vertex_feasible_and_attained :
    lpFeasible vertex ∧ objective vertex = 39/56 := by
  constructor
  · constructor
    · intro i; fin_cases i <;> norm_num [vertex]
    · norm_num [weightedSlack, vertex]
  · norm_num [objective, vertex]

theorem actual_vertex_is_globally_optimal (e : Fin 3 → ℝ) (he : lpFeasible e) :
    objective e ≤ objective vertex := by
  obtain ⟨hpos, hbudget⟩ := he
  have h0 := hpos 0
  have h2 := hpos 2
  dsimp [weightedSlack] at hbudget
  norm_num [objective, vertex]
  nlinarith

theorem actual_vertex_is_the_unique_global_optimum
    (e : Fin 3 → ℝ) (he : lpFeasible e) (hobj : objective e = objective vertex) :
    e = vertex := by
  obtain ⟨hpos, hbudget⟩ := he
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  norm_num [objective, vertex] at hobj
  dsimp [weightedSlack] at hbudget
  have e0 : e 0 = 0 := by nlinarith
  have e2 : e 2 = 0 := by nlinarith
  have e1 : e 1 = 39/56 := by linarith
  ext i
  fin_cases i <;> simpa [vertex] using (by assumption : e _ = _)

theorem actual_vertex_lyapunov_equation :
    vertexLyapunov = constraintCost + vertex + transition.mulVec vertexLyapunov := by
  ext i
  fin_cases i <;> norm_num [vertexLyapunov, constraintCost, vertex, transition,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem actual_constant_is_exact_slack_per_total_visit_coefficient :
    (39/190 : ℝ) / (1 + 28/95 + 18/19) = 13/142 := by norm_num

theorem actual_constant_feasible_and_budget_tight :
    lpFeasible constantSlack ∧ weightedSlack constantSlack = 39/190 := by
  constructor
  · constructor
    · intro i; norm_num [constantSlack]
    · norm_num [weightedSlack, constantSlack]
  · norm_num [weightedSlack, constantSlack]

theorem actual_constant_lyapunov_equation :
    constantLyapunov = constraintCost + constantSlack + transition.mulVec constantLyapunov := by
  ext i
  fin_cases i <;> norm_num [constantLyapunov, constraintCost, constantSlack, transition,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def fastTransition (p : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1/5 + 2/5*p, 4/5*(1-p); 0, 0, 1/2; 0, 1/10, 0]
def mixedValue (p : ℝ) : Fin 3 → ℝ := ![28/95+32/95*p, 20/19, 2/19]
def localLyapunovFeasible (e l : Fin 3 → ℝ) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ p*((e 0 + 3/5*l 1) - (e 0 + 1/5*l 1 + 4/5*l 2)) ≤ e 0

theorem actual_mixed_value_solves_full_bellman_equation (p : ℝ) :
    mixedValue p = constraintCost + (fastTransition p).mulVec (mixedValue p) := by
  ext i
  fin_cases i <;> norm_num [mixedValue, constraintCost, fastTransition,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem actual_vertex_local_constraint_iff_zero (p : ℝ) :
    localLyapunovFeasible vertex vertexLyapunov p ↔ p = 0 := by
  norm_num [localLyapunovFeasible, vertex, vertexLyapunov]
  constructor
  · rintro ⟨h0, _, h⟩; linarith
  · intro h; subst p; norm_num

theorem actual_constant_local_constraint_iff (p : ℝ) :
    localLyapunovFeasible constantSlack constantLyapunov p ↔
      0 ≤ p ∧ p ≤ 13/44 := by
  norm_num [localLyapunovFeasible, constantSlack, constantLyapunov]
  constructor
  · rintro ⟨h0, _, h⟩; exact ⟨h0, by linarith⟩
  · rintro ⟨h0, h⟩; exact ⟨h0, by linarith, by linarith⟩

theorem actual_value_budget_iff (p : ℝ) :
    mixedValue p 0 ≤ 1/2 ↔ p ≤ 39/64 := by
  norm_num [mixedValue]
  constructor <;> intro h <;> linarith

theorem actual_source_prices_and_policy_cost :
    (3/5 : ℝ)*(25/14) = 15/14 ∧
    13/142 + 3/5*(85/71) = 115/142 ∧
    (115/142 - 1/2 : ℝ) = 22/71 ∧
    mixedValue (13/44) 0 = 412/1045 ∧
    (13/44 : ℝ) < 39/64 ∧ mixedValue 1 0 > 1/2 := by
  norm_num [mixedValue]

end SafeLearning.CompleteChowLP21
