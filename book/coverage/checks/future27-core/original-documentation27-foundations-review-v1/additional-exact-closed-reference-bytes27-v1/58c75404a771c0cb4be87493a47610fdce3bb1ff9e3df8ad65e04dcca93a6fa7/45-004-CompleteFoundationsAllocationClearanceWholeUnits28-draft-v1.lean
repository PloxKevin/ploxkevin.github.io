import SafeLearning.CompleteFoundationsBook
import SafeLearning.CompleteFoundationsConstrainedModels

set_option autoImplicit false
noncomputable section
open Set
open scoped Matrix

namespace SafeLearning.CompleteFoundationsAllocationClearanceWholeUnits28
open CompleteFoundationsSpectralModels (E point norm_squared_coordinates applyMatrix)
open CompleteFoundationsConstrainedModels (weightedDistance)
open CompleteFoundationsBook (allocationCost allocationU allocationV allocationValue clearance)

def allocationTriangle : Set E := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0+x 1 ≤ 3}
def allocationObjective (x : E) : ℝ := allocationCost (x 0) (x 1)

theorem actual_allocation_objective_is_the_weighted_distance (x : E) :
    allocationObjective x=weightedDistance 1 4 3 1 x := by
  unfold allocationObjective allocationCost weightedDistance
  ring

theorem actual_allocation_hessian_and_strict_convexity :
    (∀ x : E,HasFDerivAt (gradient allocationObjective) (applyMatrix !![1,0;0,4]) x) ∧
    StrictConvexOn ℝ univ allocationObjective := by
  have he : allocationObjective=weightedDistance 1 4 3 1 :=
    funext actual_allocation_objective_is_the_weighted_distance
  rw [he]
  exact ⟨CompleteFoundationsConstrainedModels.actual_weighted_distance_hessian 1 4 3 1,
    CompleteFoundationsConstrainedModels.actual_weighted_distance_strict_convex 1 4 3 1
      (by norm_num) (by norm_num)⟩

theorem actual_allocation_hessian_is_positive_in_every_nonzero_direction (x : E) (hx : x≠0) :
    0 < inner ℝ x (applyMatrix !![1,0;0,4] x) := by
  have hcoord : x 0≠0 ∨ x 1≠0 := by
    by_contra hn
    push_neg at hn
    apply hx
    ext i
    fin_cases i <;> simp [hn]
  rw [CompleteFoundationsSpectralModels.matrix_coordinate_action,
    CompleteFoundationsSpectralModels.inner_coordinate_formula]
  simp [point]
  rcases hcoord with h0|h1
  · nlinarith [sq_pos_of_ne_zero h0,sq_nonneg (x 1)]
  · nlinarith [sq_nonneg (x 0),sq_pos_of_ne_zero h1]

theorem actual_feasible_allocation_triangle_is_closed_bounded_nonempty_and_convex :
    IsClosed allocationTriangle ∧ Bornology.IsBounded allocationTriangle ∧
      allocationTriangle.Nonempty ∧ Convex ℝ allocationTriangle := by
  have hc0 : Continuous (fun x : E => x 0) := by fun_prop
  have hc1 : Continuous (fun x : E => x 1) := by fun_prop
  have hclosed : IsClosed allocationTriangle :=
    (isClosed_le continuous_const hc0).inter
      ((isClosed_le continuous_const hc1).inter (isClosed_le (hc0.add hc1) continuous_const))
  have hbounded : Bornology.IsBounded allocationTriangle := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨5,?_⟩
    intro x hx
    rcases hx with ⟨h0,h1,hs⟩
    have h0up : x 0≤3 := by linarith
    have h1up : x 1≤3 := by linarith
    have hn := norm_squared_coordinates x
    nlinarith [norm_nonneg x]
  refine ⟨hclosed,hbounded,⟨point 0 0,by simp [allocationTriangle,point]⟩,?_⟩
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx0,hx1,hxs⟩
  rcases hy with ⟨hy0,hy1,hys⟩
  change 0 ≤ a*x 0+b*y 0 ∧ 0 ≤ a*x 1+b*y 1 ∧
    (a*x 0+b*y 0)+(a*x 1+b*y 1) ≤ 3
  refine ⟨by positivity,by positivity,?_⟩
  have hs : a*(x 0+x 1)+b*(y 0+y 1) ≤ a*3+b*3 :=
    add_le_add (mul_le_mul_of_nonneg_left hxs ha) (mul_le_mul_of_nonneg_left hys hb)
  nlinarith

theorem actual_compact_triangle_and_continuous_objective_attain_a_minimum :
    IsCompact allocationTriangle ∧ Continuous allocationObjective ∧
      ∃ x ∈ allocationTriangle,∀ y ∈ allocationTriangle,allocationObjective x ≤ allocationObjective y := by
  have htriangle := actual_feasible_allocation_triangle_is_closed_bounded_nonempty_and_convex
  have hk : IsCompact allocationTriangle := isCompact_iff_isClosed_bounded.mpr ⟨htriangle.1,htriangle.2.1⟩
  have hc : Continuous allocationObjective := by unfold allocationObjective allocationCost;fun_prop
  obtain ⟨x,hx,hmin⟩ := hk.exists_isMinOn htriangle.2.2.1 hc.continuousOn
  exact ⟨hk,hc,x,hx,hmin⟩

theorem actual_one_unit_second_error_is_four_times_the_first :
    allocationCost 2 1=1/2 ∧ allocationCost 3 0=2 ∧
      allocationCost 3 0=4*allocationCost 2 1 := by norm_num [allocationCost]

def allocationFinitePenalty (u v : ℝ) : ℝ :=
  allocationCost u v+(max (u+v-3) 0)^2/2

theorem actual_finite_allocation_penalty_prefers_an_infeasible_point :
    0 ≤ (23/9 : ℝ) ∧ 0 ≤ (8/9 : ℝ) ∧ (3 : ℝ)<23/9+8/9 ∧
      allocationFinitePenalty (23/9) (8/9)=2/9 ∧
      (∀ u v : ℝ,0 ≤ u → 0 ≤ v → u+v ≤ 3 →
        allocationFinitePenalty (23/9) (8/9)<allocationFinitePenalty u v) := by
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num [allocationFinitePenalty,allocationCost],?_⟩
  intro u v hu hv hbudget
  have h := (CompleteFoundationsBook.allocation_unique_optimum u v 3 (by norm_num) hbudget).1
  have hm : max (u+v-3) 0=0 := max_eq_right (by linarith)
  norm_num [allocationFinitePenalty,allocationCost,hm,allocationValue] at *
  linarith

theorem actual_every_slack_allocation_has_a_small_feasible_improving_move
    (u v : ℝ) (hu : 0≤u) (hv : 0≤v) (hs : u+v<3) :
    ∃ t : ℝ,0<t ∧ t<1 ∧
      0≤(1-t)*u+3*t ∧ 0≤(1-t)*v+t ∧
      ((1-t)*u+3*t)+((1-t)*v+t)<3 ∧
      allocationCost ((1-t)*u+3*t) ((1-t)*v+t)<allocationCost u v := by
  let t := (3-u-v)/(2*(4-u-v))
  have hden : 0<2*(4-u-v) := by linarith
  have ht : 0<t := div_pos (by linarith) hden
  have ht1 : t<1 := (div_lt_one hden).mpr (by linarith)
  have he : t*(4-u-v)=(3-u-v)/2 := by
    dsimp [t]
    field_simp [ne_of_gt hden,show 4-u-v≠0 by linarith]
    <;> ring
  have hloss : 0<allocationCost u v := by
    unfold allocationCost
    have hne : u≠3 := by linarith
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne),sq_nonneg (v-1)]
  have hcost : allocationCost ((1-t)*u+3*t) ((1-t)*v+t)=(1-t)^2*allocationCost u v := by
    unfold allocationCost
    ring
  refine ⟨t,ht,ht1,by positivity,by positivity,?_,?_⟩
  · nlinarith [he]
  · rw [hcost]
    have hfactor : (1-t)^2<1 := by nlinarith
    nlinarith

theorem actual_proportional_request_reduction_is_strictly_worse :
    (9/4 : ℝ)+(3/4)=3 ∧ allocationCost (9/4) (3/4)=13/32 ∧
      allocationCost (11/5) (4/5)=2/5 ∧ (2/5 : ℝ)<13/32 := by norm_num [allocationCost]

theorem actual_small_budget_nonnegative_active_set_has_unique_optimum
    (b u v : ℝ) (hb0 : 0≤b) (hb : b≤1/4) (hu : 0≤u) (hv : 0≤v) (hs : u+v≤b) :
    allocationCost 0 b≤allocationCost u v ∧
      (allocationCost u v=allocationCost 0 b ↔ u=0 ∧ v=b) := by
  have hi : allocationCost u v=allocationCost 0 b+
      u^2/2+2*(v-b)^2+(4-4*b)*(b-u-v)+(1-4*b)*u := by unfold allocationCost;ring
  have hbudget : 0≤(4-4*b)*(b-u-v) := mul_nonneg (by linarith) (by linarith)
  have hnonnegative : 0≤(1-4*b)*u := mul_nonneg (by linarith) hu
  constructor
  · nlinarith [sq_nonneg u,sq_nonneg (v-b)]
  · constructor
    · intro he
      have hzero : u=0 := by nlinarith [sq_nonneg u,sq_nonneg (v-b)]
      have hveq : v=b := by nlinarith [sq_nonneg u,sq_nonneg (v-b)]
      exact ⟨hzero,hveq⟩
    · rintro ⟨rfl,rfl⟩;rfl

theorem actual_large_budget_request_point_has_unique_optimum
    (b u v : ℝ) (hb : 4≤b) :
    (0 : ℝ)≤3 ∧ (0 : ℝ)≤1 ∧ (3 : ℝ)+1≤b ∧
      allocationCost 3 1≤allocationCost u v ∧
      (allocationCost u v=allocationCost 3 1 ↔ u=3 ∧ v=1) := by
  refine ⟨by norm_num,by norm_num,by linarith,?_,?_⟩
  · norm_num [allocationCost]
    positivity
  · norm_num [allocationCost]
    constructor
    · intro h;constructor <;> nlinarith [sq_nonneg (u-3),sq_nonneg (v-1)]
    · rintro ⟨rfl,rfl⟩;norm_num

theorem actual_negative_budget_has_no_nonnegative_allocation
    (b : ℝ) (hb : b<0) : ¬∃u v : ℝ,0≤u ∧ 0≤v ∧ u+v≤b := by
  rintro ⟨u,v,hu,hv,hs⟩
  linarith

theorem actual_clearance_derivative_at_every_command (a : ℝ) :
    HasDerivAt (fun a : ℝ => clearance a 0) (-1/5-a/5) a := by
  unfold clearance
  convert (((hasDerivAt_const a (3/10)).sub ((hasDerivAt_id a).div_const 5)).sub
    (((hasDerivAt_id a).pow 2).div_const 10)).add_const 0 using 1
  · rfl
  · simp only [id_eq];ring

def clearanceConstraint (d a : ℝ) : ℝ := a^2/10+a/5-1/5+d

theorem actual_clearance_constraint_derivative (d a : ℝ) :
    HasDerivAt (clearanceConstraint d) (a/5+1/5) a := by
  unfold clearanceConstraint
  convert (((((hasDerivAt_id a).pow 2).div_const 10).add
    ((hasDerivAt_id a).div_const 5)).sub_const (1/5)).add_const d using 1
  · rfl
  · simp only [id_eq];ring

theorem actual_clearance_constraint_is_convex (d : ℝ) :
    ConvexOn ℝ univ (clearanceConstraint d) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  change clearanceConstraint d (a*x+b*y)≤a*clearanceConstraint d x+b*clearanceConstraint d y
  have hgap : a*clearanceConstraint d x+b*clearanceConstraint d y-
      clearanceConstraint d (a*x+b*y)=a*b*(x-y)^2/10 := by
    have hb' : b=1-a := by linarith
    unfold clearanceConstraint
    rw [hb']
    ring
  have hn : 0≤a*b*(x-y)^2/10 := by positivity
  linarith

theorem actual_robust_clearance_is_the_single_convex_constraint
    (d a : ℝ) (hd : 0≤d) :
    (∀ w : ℝ,|w|≤d → 1/10≤clearance a w) ↔ clearanceConstraint d a≤0 := by
  rw [CompleteFoundationsBook.robust_clearance_exact a d hd]
  unfold clearanceConstraint
  constructor <;> intro h <;> nlinarith

end SafeLearning.CompleteFoundationsAllocationClearanceWholeUnits28
