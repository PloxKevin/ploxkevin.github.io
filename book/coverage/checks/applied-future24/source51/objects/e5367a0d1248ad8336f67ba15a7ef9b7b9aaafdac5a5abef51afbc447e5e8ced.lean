import SafeLearning.CompleteFoundationsConstrainedModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteFoundationsBoxedQP
open CompleteFoundationsCalculusModels (E)
open CompleteFoundationsSpectralModels (point norm_squared_coordinates)
open CompleteFoundationsConstrainedModels

def objective (a b : ℝ) (x : E) : ℝ := weightedDistance 1 1 a b x
def feasible (rhs : ℝ) : Set E :=
  {x | rhs ≤ x 0+2*x 1 ∧ |x 0| ≤ 3/2 ∧ |x 1| ≤ 3/2}
def constraint (rhs : ℝ) (i : Fin 5) (x : E) : ℝ :=
  ![rhs-x 0-2*x 1,x 0-3/2,-x 0-3/2,x 1-3/2,-x 1-3/2] i
def lagrangian (a b rhs : ℝ) (lambda : Fin 5 → ℝ) (x : E) : ℝ :=
  objective a b x+∑ i,lambda i*constraint rhs i x

theorem actual_norm_objective (a b : ℝ) (x : E) :
    objective a b x=‖x-point a b‖^2/2 := by
  rw [norm_squared_coordinates]
  simp [objective,weightedDistance,point]
  ring

theorem actual_objective_gradient (a b : ℝ) (x : E) :
    HasGradientAt (objective a b) (point (x 0-a) (x 1-b)) x := by
  unfold objective
  simpa only [one_mul] using actual_weighted_distance_gradient 1 1 a b x

theorem actual_objective_strictly_convex (a b : ℝ) :
    StrictConvexOn ℝ univ (objective a b) :=
  actual_weighted_distance_strict_convex 1 1 a b (by norm_num) (by norm_num)

theorem actual_constraints_iff (rhs : ℝ) (x : E) :
    x∈feasible rhs ↔ ∀ i,constraint rhs i x ≤ 0 := by
  constructor
  · intro hx i
    have h0 := hx.1
    have h1 := abs_le.mp hx.2.1
    have h2 := abs_le.mp hx.2.2
    fin_cases i <;> dsimp [constraint] <;> linarith
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    dsimp [constraint] at h0 h1 h2 h3 h4
    change rhs ≤ x 0+2*x 1 ∧ |x 0| ≤ 3/2 ∧ |x 1| ≤ 3/2
    rw [abs_le,abs_le]
    exact ⟨by linarith,⟨by linarith,by linarith⟩,by linarith,by linarith⟩

theorem actual_lagrangian_gradient (a b rhs : ℝ) (lambda : Fin 5 → ℝ) (x : E) :
    HasGradientAt (lagrangian a b rhs lambda)
      (point (x 0-a-lambda 0+lambda 1-lambda 2)
        (x 1-b-2*lambda 0+lambda 3-lambda 4)) x := by
  have h := (((((actual_objective_gradient a b x).hasFDerivAt.add
    ((actual_affine_constraint_gradient (-1) (-2) (-rhs) x).hasFDerivAt.const_mul (lambda 0))).add
    ((actual_affine_constraint_gradient 1 0 (3/2) x).hasFDerivAt.const_mul (lambda 1))).add
    ((actual_affine_constraint_gradient (-1) 0 (3/2) x).hasFDerivAt.const_mul (lambda 2))).add
    ((actual_affine_constraint_gradient 0 1 (3/2) x).hasFDerivAt.const_mul (lambda 3))).add
    ((actual_affine_constraint_gradient 0 (-1) (3/2) x).hasFDerivAt.const_mul (lambda 4))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · funext z
    simp [lagrangian,constraint,affineConstraint,Fin.sum_univ_succ]
    ring
  · ext z
    simp [point,InnerProductSpace.toDual_apply_apply,
      CompleteFoundationsSpectralModels.inner_coordinate_formula]
    ring

theorem actual_boxed_feasible_set_convex (rhs : ℝ) : Convex ℝ (feasible rhs) := by
  intro x hx y hy s t hs ht hst
  rcases hx with ⟨hx0,hx1,hx2⟩
  rcases hy with ⟨hy0,hy1,hy2⟩
  rw [abs_le] at hx1 hx2 hy1 hy2
  have ha := add_le_add (mul_le_mul_of_nonneg_left hx0 hs) (mul_le_mul_of_nonneg_left hy0 ht)
  have hb := add_le_add (mul_le_mul_of_nonneg_left hx1.1 hs) (mul_le_mul_of_nonneg_left hy1.1 ht)
  have hc := add_le_add (mul_le_mul_of_nonneg_left hx1.2 hs) (mul_le_mul_of_nonneg_left hy1.2 ht)
  have hd := add_le_add (mul_le_mul_of_nonneg_left hx2.1 hs) (mul_le_mul_of_nonneg_left hy2.1 ht)
  have he := add_le_add (mul_le_mul_of_nonneg_left hx2.2 hs) (mul_le_mul_of_nonneg_left hy2.2 ht)
  change rhs ≤ (s*x 0+t*y 0)+2*(s*x 1+t*y 1) ∧
    |s*x 0+t*y 0| ≤ 3/2 ∧ |s*x 1+t*y 1| ≤ 3/2
  rw [abs_le,abs_le]
  exact ⟨by nlinarith,by constructor <;> nlinarith,by constructor <;> nlinarith⟩

theorem actual_halfspace_only_zero_projection (x : E) (hx : 4 ≤ x 0+2*x 1) :
    8/5 ≤ objective 0 0 x ∧
      (objective 0 0 x=8/5 ↔ x=point (4/5) (8/5)) := by
  have he : objective 0 0 x-8/5=
      ((x 0-4/5)^2+(x 1-8/5)^2)/2+(4/5)*(x 0+2*x 1-4) := by
    dsimp [objective,weightedDistance]
    ring
  have h0 := sq_nonneg (x 0-4/5)
  have h1 := sq_nonneg (x 1-8/5)
  constructor
  · nlinarith
  · constructor
    · intro h
      have hx0 : x 0=4/5 := by nlinarith
      have hx1 : x 1=8/5 := by nlinarith
      ext i
      fin_cases i <;> simp [point,hx0,hx1]
    · rintro rfl
      norm_num [objective,weightedDistance,point]

theorem actual_zero_projection_violates_box :
    (point (4/5) (8/5) : E) 0+2*(point (4/5) (8/5)) 1=4 ∧
      ¬ point (4/5) (8/5)∈feasible 4 := by
  norm_num [feasible,point]

def zeroMultipliers : Fin 5 → ℝ := ![1,0,0,1/2,0]

theorem actual_zero_source_kkt :
    point 1 (3/2)∈feasible 4 ∧ objective 0 0 (point 1 (3/2))=13/8 ∧
    (∀ i,0 ≤ zeroMultipliers i) ∧
    (∀ i,zeroMultipliers i*constraint 4 i (point 1 (3/2))=0) ∧
    gradient (lagrangian 0 0 4 zeroMultipliers) (point 1 (3/2))=0 ∧
    constraint 4 0 (point 1 (3/2))=0 ∧
    constraint 4 3 (point 1 (3/2))=0 ∧
    constraint 4 1 (point 1 (3/2)) < 0 ∧
    constraint 4 2 (point 1 (3/2)) < 0 ∧
    constraint 4 4 (point 1 (3/2)) < 0 := by
  rw [(actual_lagrangian_gradient _ _ _ _ _).gradient]
  norm_num [feasible,objective,weightedDistance,zeroMultipliers,constraint,
    point,Fin.forall_fin_succ]
  ext i
  fin_cases i <;> simp [point]

theorem actual_zero_boxed_unique_global_optimum (x : E) (hx : x∈feasible 4) :
    13/8 ≤ objective 0 0 x ∧
      (objective 0 0 x=13/8 ↔ x=point 1 (3/2)) := by
  have ha := hx.1
  have hb := (abs_le.mp hx.2.2).2
  have he : objective 0 0 x-13/8=
    ((x 0-1)^2+(x 1-3/2)^2)/2+(x 0+2*x 1-4)+(1/2)*(3/2-x 1) := by
    dsimp [objective,weightedDistance]
    ring
  have h0 := sq_nonneg (x 0-1)
  have h1 := sq_nonneg (x 1-3/2)
  constructor
  · nlinarith
  · constructor
    · intro h
      have hx0 : x 0=1 := by nlinarith
      have hx1 : x 1=3/2 := by nlinarith
      ext i
      fin_cases i <;> simp [point,hx0,hx1]
    · rintro rfl
      norm_num [objective,weightedDistance,point]

theorem actual_box_maximum_and_infeasibility (rhs : ℝ) :
    (∀ x∈feasible rhs,rhs ≤ 9/2) ∧
    (9/2 : ℝ) < 5 ∧ feasible 5=∅ := by
  refine ⟨?_,by norm_num,?_⟩
  · intro x hx
    have h0 := (abs_le.mp hx.2.1).2
    have h1 := (abs_le.mp hx.2.2).2
    linarith [hx.1]
  · ext x
    simp only [Set.mem_empty_iff_false,iff_false]
    intro hx
    have h0 := (abs_le.mp hx.2.1).2
    have h1 := (abs_le.mp hx.2.2).2
    linarith [hx.1]

theorem actual_halfspace_only_reference_projection (x : E) (hx : 21/5 ≤ x 0+2*x 1) :
    1/250 ≤ objective 2 1 x ∧
      (objective 2 1 x=1/250 ↔ x=point (51/25) (27/25)) := by
  have he : objective 2 1 x-1/250=
      ((x 0-51/25)^2+(x 1-27/25)^2)/2+(1/25)*(x 0+2*x 1-21/5) := by
    dsimp [objective,weightedDistance]
    ring
  have h0 := sq_nonneg (x 0-51/25)
  have h1 := sq_nonneg (x 1-27/25)
  constructor
  · nlinarith
  · constructor
    · intro h
      have hx0 : x 0=51/25 := by nlinarith
      have hx1 : x 1=27/25 := by nlinarith
      ext i
      fin_cases i <;> simp [point,hx0,hx1]
    · rintro rfl
      norm_num [objective,weightedDistance,point]

def clip (x : E) : E := point (max (-3/2) (min (3/2) (x 0)))
  (max (-3/2) (min (3/2) (x 1)))

theorem actual_reference_projection_and_clipping :
    (point 2 1 : E) 0+2*(point 2 1) 1=4 ∧
    point (51/25) (27/25)=point 2 1+(1/25 : ℝ) • point 1 2 ∧
    (point (51/25) (27/25) : E) 0+2*(point (51/25) (27/25)) 1=21/5 ∧
    clip (point (51/25) (27/25))=point (3/2) (27/25) ∧
    (point (3/2) (27/25) : E) 0+2*(point (3/2) (27/25)) 1=183/50 ∧
    ¬ clip (point (51/25) (27/25))∈feasible (21/5) := by
  norm_num [clip,feasible,point]
  ext i
  fin_cases i <;> norm_num [point]

def referenceMultipliers : Fin 5 → ℝ := ![7/40,27/40,0,0,0]

theorem actual_reference_source_kkt :
    point (3/2) (27/20)∈feasible (21/5) ∧
    objective 2 1 (point (3/2) (27/20))=149/800 ∧
    (∀ i,0 ≤ referenceMultipliers i) ∧
    (∀ i,referenceMultipliers i*constraint (21/5) i (point (3/2) (27/20))=0) ∧
    gradient (lagrangian 2 1 (21/5) referenceMultipliers) (point (3/2) (27/20))=0 ∧
    gradient (objective 2 1) (point (3/2) (27/20))=point (-1/2) (7/20) ∧
    constraint (21/5) 0 (point (3/2) (27/20))=0 ∧
    constraint (21/5) 1 (point (3/2) (27/20))=0 ∧
    constraint (21/5) 2 (point (3/2) (27/20)) < 0 ∧
    constraint (21/5) 3 (point (3/2) (27/20)) < 0 ∧
    constraint (21/5) 4 (point (3/2) (27/20)) < 0 := by
  rw [(actual_lagrangian_gradient _ _ _ _ _).gradient,
    (actual_objective_gradient _ _ _).gradient]
  norm_num [feasible,objective,weightedDistance,referenceMultipliers,constraint,
    point,Fin.forall_fin_succ]
  ext i
  fin_cases i <;> simp [point]

theorem actual_reference_boxed_unique_global_optimum (x : E) (hx : x∈feasible (21/5)) :
    149/800 ≤ objective 2 1 x ∧
      (objective 2 1 x=149/800 ↔ x=point (3/2) (27/20)) := by
  have ha := hx.1
  have hb := (abs_le.mp hx.2.1).2
  have he : objective 2 1 x-149/800=
    ((x 0-3/2)^2+(x 1-27/20)^2)/2+(7/40)*(x 0+2*x 1-21/5)+
      (27/40)*(3/2-x 0) := by
    dsimp [objective,weightedDistance]
    ring
  have h0 := sq_nonneg (x 0-3/2)
  have h1 := sq_nonneg (x 1-27/20)
  constructor
  · nlinarith
  · constructor
    · intro h
      have hx0 : x 0=3/2 := by nlinarith
      have hx1 : x 1=27/20 := by nlinarith
      ext i
      fin_cases i <;> simp [point,hx0,hx1]
    · rintro rfl
      norm_num [objective,weightedDistance,point]

def gridPoint (i j : Fin 61) : E := point (-3/2+(i : ℕ)/20) (-3/2+(j : ℕ)/20)

theorem actual_grid_search_agrees :
    gridPoint 60 57=point (3/2) (27/20) ∧
    gridPoint 60 57∈feasible (21/5) ∧
    (∀ i j,gridPoint i j∈feasible (21/5) →
      objective 2 1 (gridPoint 60 57) ≤ objective 2 1 (gridPoint i j)) := by
  have he : gridPoint 60 57=point (3/2) (27/20) := by norm_num [gridPoint]
  refine ⟨he,?_,?_⟩
  · rw [he]
    exact actual_reference_source_kkt.1
  · intro i j hij
    rw [he,actual_reference_source_kkt.2.1]
    exact (actual_reference_boxed_unique_global_optimum _ hij).1

def relaxedFeasible (rhs slack : ℝ) (x : E) : Prop :=
  rhs ≤ x 0+2*x 1+slack ∧ |x 0| ≤ 3/2 ∧ |x 1| ≤ 3/2 ∧ 0 ≤ slack

theorem actual_slack_restores_solvability_without_original_guarantee :
    relaxedFeasible 5 5 (point 0 0) ∧ point 0 0∉feasible 5 := by
  norm_num [relaxedFeasible,feasible,point]

end SafeLearning.CompleteFoundationsBoxedQP
