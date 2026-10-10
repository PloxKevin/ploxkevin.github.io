import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesQuadraticDual

def actualPrimalObjective (input : ℝ) : ℝ := (input-2)^2
def actualScalarLagrangian (input price : ℝ) : ℝ := actualPrimalObjective input+price*(input-1)
def actualDualFunction (price : ℝ) : ℝ := sInf (Set.range (fun input => actualScalarLagrangian input price))

theorem actual_source_constraint_is_affine (first second left right : ℝ)
    (hsum : left+right=1) :
    (left*first+right*second)-1=left*(first-1)+right*(second-1) := by
  nlinarith

theorem actual_source_unconstrained_minimizer_is_excluded : ¬((2:ℝ)≤1) := by
  norm_num

theorem actual_source_optimal_dual_price_recovers_primal : (2:ℝ)-2/2=1 := by
  norm_num

theorem actual_unconstrained_primal_unique_minimum (input : ℝ) :
    0 ≤ actualPrimalObjective input ∧ (actualPrimalObjective input=0 ↔ input=2) := by
  unfold actualPrimalObjective
  constructor
  · exact sq_nonneg (input-2)
  · constructor
    · intro h; nlinarith
    · intro h; rw [h]; norm_num

theorem actual_lagrangian_completed_square (input price : ℝ) :
    actualScalarLagrangian input price=(input-2+price/2)^2+price-price^2/4 := by
  unfold actualScalarLagrangian actualPrimalObjective
  ring

theorem actual_lagrangian_stationary_input_is_global_minimum (price : ℝ) :
    IsLeast (Set.range (fun input => actualScalarLagrangian input price)) (price-price^2/4) := by
  constructor
  · refine ⟨2-price/2,?_⟩
    change actualScalarLagrangian (2-price/2) price=price-price^2/4
    rw [actual_lagrangian_completed_square]
    ring
  · intro value hvalue
    obtain ⟨input,rfl⟩ := hvalue
    change price-price^2/4 ≤ actualScalarLagrangian input price
    rw [actual_lagrangian_completed_square]
    nlinarith [sq_nonneg (input-2+price/2)]

theorem actual_dual_function_is_true_unrestricted_infimum (price : ℝ) :
    actualDualFunction price=price-price^2/4 :=
  (actual_lagrangian_stationary_input_is_global_minimum price).csInf_eq

theorem actual_lagrangian_primal_derivative (input price : ℝ) :
    HasDerivAt (fun value => actualScalarLagrangian value price) (2*(input-2)+price) input := by
  have hd : HasDerivAt (fun value : ℝ => value-2) 1 input :=
    HasDerivAt.sub_const 2 (hasDerivAt_id input)
  have hs := HasDerivAt.pow hd 2
  have hc := HasDerivAt.const_mul price (HasDerivAt.sub_const 1 (hasDerivAt_id input))
  convert HasDerivAt.add hs hc using 1
  · funext value
    simp [actualScalarLagrangian,actualPrimalObjective]
  · simp

theorem actual_dual_function_derivative (price : ℝ) :
    HasDerivAt actualDualFunction (1-price/2) price := by
  have he : actualDualFunction=(fun value : ℝ => value-value^2/4) :=
    funext actual_dual_function_is_true_unrestricted_infimum
  rw [he]
  have hs := HasDerivAt.pow (hasDerivAt_id price) 2
  convert HasDerivAt.sub (hasDerivAt_id price) (HasDerivAt.div_const hs 4) using 1
  · funext value
    simp [div_eq_mul_inv]
  · simp
    ring

theorem actual_dual_function_is_concave : ConcaveOn ℝ Set.univ actualDualFunction := by
  constructor
  · exact convex_univ
  · intro first _ second _ left right hleft hright hsum
    simp only [smul_eq_mul,actual_dual_function_is_true_unrestricted_infimum]
    have he : right=1-left := by linarith
    have hg : (left*first+right*second-(left*first+right*second)^2/4)-
        (left*(first-first^2/4)+right*(second-second^2/4))=
          left*right*(first-second)^2/4 := by rw [he]; ring
    have hn : 0 ≤ left*right*(first-second)^2/4 := by positivity
    linarith

theorem actual_primal_objective_is_convex : ConvexOn ℝ Set.univ actualPrimalObjective := by
  constructor
  · exact convex_univ
  · intro first _ second _ left right hleft hright hsum
    simp only [smul_eq_mul,actualPrimalObjective]
    have he : right=1-left := by linarith
    have hg : (left*(first-2)^2+right*(second-2)^2)-(left*first+right*second-2)^2=
        left*right*(first-second)^2 := by rw [he]; ring
    have hn : 0 ≤ left*right*(first-second)^2 := by positivity
    linarith

theorem actual_primal_unique_global_optimum (input : ℝ) (hfeasible : input ≤ 1) :
    1 ≤ actualPrimalObjective input ∧ (actualPrimalObjective input=1 ↔ input=1) := by
  unfold actualPrimalObjective
  constructor
  · nlinarith [sq_nonneg (input-1)]
  · constructor
    · intro h; nlinarith [sq_nonneg (input-1)]
    · intro h; rw [h]; norm_num

theorem actual_dual_unique_global_maximum (price : ℝ) :
    actualDualFunction price ≤ 1 ∧ (actualDualFunction price=1 ↔ price=2) := by
  rw [actual_dual_function_is_true_unrestricted_infimum]
  constructor
  · nlinarith [sq_nonneg (price-2)]
  · constructor
    · intro h; nlinarith [sq_nonneg (price-2)]
    · intro h; rw [h]; norm_num

theorem actual_dual_gap_identity (price : ℝ) :
    1-actualDualFunction price=(price-2)^2/4 := by
  rw [actual_dual_function_is_true_unrestricted_infimum]
  ring

theorem actual_nonnegative_price_is_a_true_primal_lower_bound
    (input price : ℝ) (hfeasible : input ≤ 1) (hprice : 0 ≤ price) :
    actualDualFunction price ≤ actualPrimalObjective input := by
  have h := (actual_lagrangian_stationary_input_is_global_minimum price).2
    (Set.mem_range_self input)
  rw [← actual_dual_function_is_true_unrestricted_infimum] at h
  unfold actualScalarLagrangian at h
  have hp : price*(input-1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hprice (by linarith)
  linarith

theorem actual_kkt_conditions_determine_source_solution (input price : ℝ) :
    (input ≤ 1 ∧ 0 ≤ price ∧ 2*(input-2)+price=0 ∧ price*(input-1)=0) ↔
      (input=1 ∧ price=2) := by
  constructor
  · rintro ⟨hf,hp,hs,hc⟩
    rcases mul_eq_zero.mp hc with hz | hz
    · nlinarith
    · constructor <;> linarith
  · rintro ⟨rfl,rfl⟩
    norm_num

theorem actual_source_strict_feasibility_and_zero_gap :
    (0:ℝ)<1 ∧ actualPrimalObjective 1=1 ∧ actualDualFunction 2=1 ∧
      actualScalarLagrangian 1 2=1 ∧ (2:ℝ)≥0 := by
  norm_num [actualPrimalObjective,actual_dual_function_is_true_unrestricted_infimum,
    actualScalarLagrangian]

theorem actual_positive_relaxation_improves_the_source_optimum
    (allowance : ℝ) (hallowance : 0<allowance) (hsmall : allowance<1) :
    (1+allowance ≤ 1+allowance) ∧ actualPrimalObjective (1+allowance)<actualPrimalObjective 1 := by
  constructor
  · exact le_rfl
  · unfold actualPrimalObjective
    nlinarith

end SafeLearning.CompleteModulesQuadraticDual
