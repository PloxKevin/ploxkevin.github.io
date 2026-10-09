import Mathlib
import SafeLearning.CompleteCoreBook

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SafeLearning.CompletePolicyMetricPrices

abbrev Plane := EuclideanSpace ℝ (Fin 2)
def vector (x y : ℝ) : Plane := WithLp.toLp 2 ![x,y]
def H : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,4]
def trustCost (v : Plane) : ℝ := (1 / 2) * dotProduct (WithLp.ofLp v) (H *ᵥ WithLp.ofLp v)
def reward (v : Plane) : ℝ := 2 * v 0 + v 1

theorem genuine_trust_quadratic (v : Plane) : trustCost v = (v 0 ^ 2 + 4 * v 1 ^ 2) / 2 := by
  simp [trustCost,H,dotProduct,Matrix.mulVec,Fin.sum_univ_two]
  ring

theorem actual_candidate_euclidean_lengths :
    ‖vector (1/2) 0‖ = 1/2 ∧ ‖vector 0 (1/2)‖ = 1/2 := by
  have h1 : ‖vector (1/2) 0‖ ^ 2 = (1/4 : ℝ) := by
    norm_num [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,vector]
  have h2 : ‖vector 0 (1/2)‖ ^ 2 = (1/4 : ℝ) := by
    norm_num [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,vector]
  constructor <;> nlinarith [norm_nonneg (vector (1/2) 0),norm_nonneg (vector 0 (1/2))]

theorem actual_same_distance_different_metric_reward_and_feasibility :
    trustCost (vector (1/2) 0) = 1/8 ∧ trustCost (vector 0 (1/2)) = 1/2 ∧
    reward (vector (1/2) 0) = 1 ∧ reward (vector 0 (1/2)) = 1/2 ∧
    ¬ (vector (1/2) 0) 0 ≤ 1/5 ∧ (vector 0 (1/2)) 0 ≤ 1/5 := by
  norm_num [genuine_trust_quadratic,reward,vector]

theorem actual_both_complementarity_products :
    (5 / (4 * Real.sqrt 6)) * (trustCost (vector (1/5) (Real.sqrt 6/5)) - 1/2) = 0 ∧
    (2 - 1/(4 * Real.sqrt 6)) * ((1/5 : ℝ) - 1/5) = 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  constructor
  · have ht : trustCost (vector (1/5) (Real.sqrt 6/5)) = 1/2 := by
      simp only [genuine_trust_quadratic,vector]
      norm_num
      nlinarith
    rw [ht]; ring
  · ring

def optimalValue (radius budget : ℝ) : ℝ := 2 * budget + Real.sqrt (2 * radius - budget ^ 2) / 2

theorem genuine_all_feasible_upper_bound (radius budget y0 x y : ℝ)
    (hy : 0 < y0) (hs : budget ^ 2 + 4 * y0 ^ 2 = 2 * radius)
    (hprice : 0 ≤ 2 - budget / (4 * y0))
    (htrust : x ^ 2 + 4 * y ^ 2 ≤ 2 * radius) (hbudget : x ≤ budget) :
    2 * x + y ≤ 2 * budget + y0 := by
  have hsupport : budget * x + 4 * y0 * y ≤ 2 * radius := by
    nlinarith [sq_nonneg (x-budget),sq_nonneg (y-y0)]
  have hdual := mul_le_mul_of_nonneg_left hbudget hprice
  have hweighted := mul_le_mul_of_nonneg_left hsupport (by positivity : 0 ≤ 1/(4*y0))
  have hid : (1/(4*y0))*(budget*x+4*y0*y)+(2-budget/(4*y0))*x=2*x+y := by
    field_simp; ring
  have hbound : (1/(4*y0))*(2*radius)+(2-budget/(4*y0))*budget=2*budget+y0 := by
    field_simp
    nlinarith
  linarith

theorem genuine_parametric_optimum (radius budget : ℝ)
    (hpositive : 0 < 2 * radius - budget ^ 2)
    (hprice : 0 ≤ 2 - budget / (2 * Real.sqrt (2 * radius - budget ^ 2))) :
    let y0 := Real.sqrt (2 * radius - budget ^ 2) / 2
    (budget ^ 2 + 4 * y0 ^ 2 = 2 * radius) ∧
      (2 * budget + y0 = optimalValue radius budget) ∧
      (∀ x y, x ^ 2 + 4 * y ^ 2 ≤ 2 * radius → x ≤ budget →
        2 * x + y ≤ optimalValue radius budget) := by
  dsimp only
  have hs := Real.sq_sqrt hpositive.le
  have hy : 0 < Real.sqrt (2*radius-budget^2)/2 := by positivity
  have hnorm : budget^2+4*(Real.sqrt (2*radius-budget^2)/2)^2=2*radius := by nlinarith
  refine ⟨hnorm,rfl,?_⟩
  intro x y ht hb
  apply genuine_all_feasible_upper_bound radius budget _ x y hy hnorm _ ht hb
  convert hprice using 1
  ring

theorem actual_radicand_sqrt : Real.sqrt (1 - (1/5 : ℝ)^2) = 2 * Real.sqrt 6 / 5 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 - (1/5 : ℝ)^2)
  have h6 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  nlinarith [Real.sqrt_nonneg (1-(1/5 : ℝ)^2),Real.sqrt_nonneg (6 : ℝ)]

theorem genuine_trust_radius_value_derivative :
    HasDerivAt (fun radius : ℝ => optimalValue radius (1/5))
      (5 / (4 * Real.sqrt 6)) (1/2) := by
  have h := (((hasDerivAt_id (1/2 : ℝ)).const_mul 2).sub_const ((1/5 : ℝ)^2)).sqrt
    (by norm_num : 2 * (1/2 : ℝ) - (1/5 : ℝ)^2 ≠ 0)
  have hd := (hasDerivAt_const (1/2 : ℝ) (2*(1/5 : ℝ))).add (h.div_const 2)
  convert hd using 1
  · rfl
  · dsimp
    rw [show 2*(1/2 : ℝ)=1 by norm_num,actual_radicand_sqrt]
    have hp := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)
    field_simp
    ring

theorem genuine_cost_budget_value_derivative :
    HasDerivAt (fun budget : ℝ => optimalValue (1/2) budget)
      (2 - 1/(4 * Real.sqrt 6)) (1/5) := by
  have h := ((hasDerivAt_const (1/5 : ℝ) (2*(1/2 : ℝ))).sub
    ((hasDerivAt_id (1/5 : ℝ)).pow 2)).sqrt
      (by norm_num : 2 * (1/2 : ℝ) - (1/5 : ℝ)^2 ≠ 0)
  have hd := ((hasDerivAt_id (1/5 : ℝ)).const_mul 2).add (h.div_const 2)
  convert hd using 1
  · rfl
  · dsimp
    rw [show 2*(1/2 : ℝ)=1 by norm_num,actual_radicand_sqrt]
    have hp := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)
    field_simp
    ring

end SafeLearning.CompletePolicyMetricPrices
