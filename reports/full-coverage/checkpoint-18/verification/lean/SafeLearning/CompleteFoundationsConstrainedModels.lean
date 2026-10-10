import SafeLearning.CompleteFoundationsCalculusModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsConstrainedModels
open CompleteFoundationsCalculusModels (E coordinate)
open CompleteFoundationsSpectralModels (point applyMatrix matrix_coordinate_action
  inner_coordinate_formula norm_squared_coordinates)

def weightedDistance (q₀ q₁ a b : ℝ) (x : E) : ℝ :=
  q₀/2*(x 0-a)^2+q₁/2*(x 1-b)^2

theorem actual_weighted_distance_gradient (q₀ q₁ a b : ℝ) (x : E) :
    HasGradientAt (weightedDistance q₀ q₁ a b)
      (point (q₀*(x 0-a)) (q₁*(x 1-b))) x := by
  have h₀ := ((coordinate 0).hasFDerivAt (x := x)).sub_const a
  have h₁ := ((coordinate 1).hasFDerivAt (x := x)).sub_const b
  have hf : HasFDerivAt (weightedDistance q₀ q₁ a b)
      ((q₀*(x 0-a)) • coordinate 0+(q₁*(x 1-b)) • coordinate 1) x := by
    convert ((h₀.pow 2).const_mul (q₀/2)).add ((h₁.pow 2).const_mul (q₁/2)) using 1
    · rfl
    · ext u
      simp [coordinate,PiLp.proj,PiLp.projₗ]
      ring
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf using 1
  ext u
  simp [point,coordinate,InnerProductSpace.toDual_apply_apply,PiLp.inner_apply,
    Fin.sum_univ_succ,PiLp.proj,PiLp.projₗ]
  ring

theorem actual_weighted_distance_hessian (q₀ q₁ a b : ℝ) (x : E) :
    HasFDerivAt (gradient (weightedDistance q₀ q₁ a b))
      (applyMatrix !![q₀,0;0,q₁]) x := by
  have he : gradient (weightedDistance q₀ q₁ a b)=
      (fun z : E =>  applyMatrix !![q₀,0;0,q₁] z-point (q₀*a) (q₁*b)) := by
    funext z
    rw [(actual_weighted_distance_gradient q₀ q₁ a b z).gradient,matrix_coordinate_action]
    ext i
    fin_cases i  <;>  simp [point]  <;>  ring
  rw [he]
  exact (applyMatrix !![q₀,0;0,q₁]).hasFDerivAt.sub_const _

theorem actual_weighted_distance_strict_convex (q₀ q₁ a b : ℝ)
    (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) :
    StrictConvexOn ℝ univ (weightedDistance q₀ q₁ a b) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy hxy s t hs ht hst
  have hd : x 0-y 0 ≠ 0 ∨ x 1-y 1 ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hxy
    ext i
    fin_cases i
    · exact sub_eq_zero.mp hn.1
    · exact sub_eq_zero.mp hn.2
  have hp : 0 < q₀*(x 0-y 0)^2+q₁*(x 1-y 1)^2 := by
    rcases hd with hd|hd
    · have h := mul_pos hq₀ (sq_pos_of_ne_zero hd)
      have h' := mul_nonneg hq₁.le (sq_nonneg (x 1-y 1))
      linarith
    · have h := mul_pos hq₁ (sq_pos_of_ne_zero hd)
      have h' := mul_nonneg hq₀.le (sq_nonneg (x 0-y 0))
      linarith
  have hg : s*weightedDistance q₀ q₁ a b x+t*weightedDistance q₀ q₁ a b y-
      weightedDistance q₀ q₁ a b (s • x+t • y)=
      s*t/2*(q₀*(x 0-y 0)^2+q₁*(x 1-y 1)^2) := by
    have ht' : t=1-s := by linarith
    simp only [weightedDistance,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    rw [ht']
    ring
  have hpositive := mul_pos (show 0 < s*t/2 by positivity) hp
  change weightedDistance q₀ q₁ a b (s • x+t • y) <
    s*weightedDistance q₀ q₁ a b x+t*weightedDistance q₀ q₁ a b y
  linarith

theorem actual_weighted_distance_unconstrained_minimum (q₀ q₁ a b : ℝ)
    (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (x : E) :
    0 ≤ weightedDistance q₀ q₁ a b x ∧
      (weightedDistance q₀ q₁ a b x=0 ↔ x=point a b) := by
  have h0 := mul_nonneg hq₀.le (sq_nonneg (x 0-a))
  have h1 := mul_nonneg hq₁.le (sq_nonneg (x 1-b))
  constructor
  · dsimp [weightedDistance]
    positivity
  · constructor
    · intro he
      have hw : q₀*(x 0-a)^2+q₁*(x 1-b)^2=0 := by
        dsimp [weightedDistance] at he
        nlinarith
      have hx0 : x 0=a := by
        by_contra hn
        have hp := mul_pos hq₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hn))
        linarith
      have hx1 : x 1=b := by
        by_contra hn
        have hp := mul_pos hq₁ (sq_pos_of_ne_zero (sub_ne_zero.mpr hn))
        linarith
      ext i
      fin_cases i <;> simp [point,hx0,hx1]
    · rintro rfl
      simp [weightedDistance,point]

def scalarLagrangian (bound multiplier x : ℝ) : ℝ :=
  (x-3)^2+multiplier*(x-bound)

def scalarKKT (bound x multiplier : ℝ) : Prop :=
  x ≤ bound ∧ 0 ≤ multiplier ∧ multiplier*(x-bound)=0 ∧
    deriv (scalarLagrangian bound multiplier) x=0

theorem actual_scalar_lagrangian_derivative (bound multiplier x : ℝ) :
    HasDerivAt (scalarLagrangian bound multiplier) (2*(x-3)+multiplier) x := by
  convert (((hasDerivAt_id x).sub_const 3).pow 2).add
    (((hasDerivAt_id x).sub_const bound).const_mul multiplier) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem actual_scalar_kkt_certificates : scalarKKT 1 1 4 ∧ scalarKKT 4 3 0 ∧
    (∀ multiplier,scalarKKT 4 3 multiplier ↔ multiplier=0) := by
  simp only [scalarKKT,(actual_scalar_lagrangian_derivative _ _ _).deriv]
  norm_num

theorem actual_scalar_global_optima :
    (∀ x : ℝ,x ≤ 1 → 4 ≤ (x-3)^2 ∧ ((x-3)^2=4 ↔ x=1)) ∧
    (∀ x : ℝ,0 ≤ (x-3)^2 ∧ ((x-3)^2=0 ↔ x=3)) ∧
    (3 : ℝ) > 1 ∧ (3 : ℝ) < 4 := by
  refine ⟨?_,?_,by norm_num,by norm_num⟩
  · intro x hx
    constructor
    · nlinarith [sq_nonneg (x-1)]
    · constructor  <;>  intro h  <;>  nlinarith [sq_nonneg (x-1)]
  · intro x
    constructor
    · exact sq_nonneg _
    · rw [sq_eq_zero_iff,sub_eq_zero]

theorem actual_scalar_objective_decreases_until_three :
    StrictAntiOn (fun x : ℝ =>  (x-3)^2) (Iic 3) := by
  intro x hx y hy hxy
  change x ≤ 3 at hx
  change y ≤ 3 at hy
  have hp := mul_pos (sub_pos.mpr hxy) (show 0 < 6-x-y by linarith [hx,hy])
  nlinarith

theorem actual_scalar_objective_is_convex :
    ConvexOn ℝ univ (fun x : ℝ =>  (x-3)^2) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy s t hs ht hst
  have hp := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x-y))
  have he : s*(x-3)^2+t*(y-3)^2-(s*x+t*y-3)^2=s*t*(x-y)^2 := by
    have ht' : t=1-s := by linarith
    rw [ht']
    ring
  change (s*x+t*y-3)^2 ≤ s*(x-3)^2+t*(y-3)^2
  linarith

theorem actual_scalar_constraint_is_affine (bound x y s t : ℝ) (hst : s+t=1) :
    s*x+t*y-bound=s*(x-bound)+t*(y-bound) := by
  have ht : t=1-s := by linarith
  rw [ht]
  ring

theorem actual_scalar_feasible_set_is_convex (bound : ℝ) :
    Convex ℝ {x : ℝ | x ≤ bound} := convex_Iic bound

def affineConstraint (a b c : ℝ) (x : E) : ℝ := a*x 0+b*x 1-c

theorem actual_affine_constraint_gradient (a b c : ℝ) (x : E) :
    HasGradientAt (affineConstraint a b c) (point a b) x := by
  have hf := (((coordinate 0).hasFDerivAt (x := x)).const_mul a).add
    (((coordinate 1).hasFDerivAt (x := x)).const_mul b)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf.sub_const c using 1
  · rfl
  · ext u
    simp [coordinate,point,InnerProductSpace.toDual_apply_apply,PiLp.inner_apply,
      Fin.sum_univ_succ,PiLp.proj,PiLp.projₗ]
    ring

def halfspaceFeasible : Set E := {x | x 0+x 1 ≤ 1 ∧ 0 ≤ x 0}
def halfspaceLagrangian (lambda mu : ℝ) (x : E) : ℝ :=
  weightedDistance 1 1 2 2 x+lambda*affineConstraint 1 1 1 x+mu*affineConstraint (-1) 0 0 x

theorem actual_halfspace_lagrangian_gradient (lambda mu : ℝ) (x : E) :
    HasGradientAt (halfspaceLagrangian lambda mu) (point (x 0-2+lambda-mu) (x 1-2+lambda)) x := by
  have hf := ((actual_weighted_distance_gradient 1 1 2 2 x).hasFDerivAt.add
    ((actual_affine_constraint_gradient 1 1 1 x).hasFDerivAt.const_mul lambda)).add
      ((actual_affine_constraint_gradient (-1) 0 0 x).hasFDerivAt.const_mul mu)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf using 1
  · rfl
  · ext u
    simp [point,InnerProductSpace.toDual_apply_apply,inner_coordinate_formula]
    ring

theorem actual_halfspace_feasible_set_is_convex : Convex ℝ halfspaceFeasible := by
  intro x hx y hy s t hs ht hst
  rcases hx with ⟨hx,hx0⟩
  rcases hy with ⟨hy,hy0⟩
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hx hs) (mul_le_mul_of_nonneg_left hy ht)
  have hnonnegative := add_nonneg (mul_nonneg hs hx0) (mul_nonneg ht hy0)
  change s*x 0+t*y 0+(s*x 1+t*y 1) ≤ 1 ∧ 0 ≤ s*x 0+t*y 0
  constructor
  · nlinarith [hsum]
  · exact hnonnegative

theorem actual_halfspace_norm_objective (x : E) :
    weightedDistance 1 1 2 2 x=‖x-point 2 2‖^2/2 := by
  rw [norm_squared_coordinates]
  simp [weightedDistance,point]
  ring

theorem actual_halfspace_hessian_is_identity (x : E) :
    HasFDerivAt (gradient (weightedDistance 1 1 2 2)) (ContinuousLinearMap.id ℝ E) x := by
  have he : applyMatrix (!![1,0;0,1] : Matrix (Fin 2) (Fin 2) ℝ)=ContinuousLinearMap.id ℝ E := by
    ext u i
    rw [matrix_coordinate_action]
    fin_cases i <;> simp [point]
  rw [← he]
  exact actual_weighted_distance_hessian 1 1 2 2 x

theorem actual_halfspace_global_unique_optimum (x : E) (hx : x∈halfspaceFeasible) :
    9/4 ≤ weightedDistance 1 1 2 2 x ∧
      (weightedDistance 1 1 2 2 x=9/4 ↔ x=point (1/2) (1/2)) := by
  have h := hx.1
  constructor
  · dsimp [weightedDistance]
    nlinarith [sq_nonneg (x 0-x 1),sq_nonneg (x 0+x 1-1)]
  · constructor
    · intro he
      have h0 : x 0=1/2 := by
        dsimp [weightedDistance] at he
        nlinarith [sq_nonneg (x 0-x 1),sq_nonneg (x 0+x 1-1)]
      have h1 : x 1=1/2 := by
        dsimp [weightedDistance] at he
        nlinarith [sq_nonneg (x 0-x 1),sq_nonneg (x 0+x 1-1)]
      ext i
      fin_cases i  <;>  simp [point,h0,h1]
    · rintro rfl
      norm_num [weightedDistance,point]

theorem actual_halfspace_source_kkt :
    point (1/2) (1/2)∈halfspaceFeasible ∧
    affineConstraint 1 1 1 (point (1/2) (1/2))=0 ∧
    affineConstraint (-1) 0 0 (point (1/2) (1/2)) < 0 ∧
    (0 : ℝ) ≤ 3/2 ∧ (0 : ℝ) ≤ 0 ∧
    (3/2 : ℝ)*affineConstraint 1 1 1 (point (1/2) (1/2))=0 ∧
    (0 : ℝ)*affineConstraint (-1) 0 0 (point (1/2) (1/2))=0 ∧
    gradient (halfspaceLagrangian (3/2) 0) (point (1/2) (1/2))=0 ∧
    gradient (weightedDistance 1 1 2 2) (point (1/2) (1/2))=point (-3/2) (-3/2) ∧
    point 2 2∉halfspaceFeasible := by
  rw [(actual_halfspace_lagrangian_gradient _ _ _).gradient,
    (actual_weighted_distance_gradient _ _ _ _ _).gradient]
  norm_num [halfspaceFeasible,affineConstraint,point]
  ext i
  fin_cases i  <;>  simp [point]

theorem actual_halfspace_stationarity_iff (lambda mu : ℝ) (x : E) :
    gradient (halfspaceLagrangian lambda mu) x=0 ↔
      x=point (2-lambda+mu) (2-lambda) := by
  rw [(actual_halfspace_lagrangian_gradient lambda mu x).gradient]
  constructor
  · intro h
    have h0 := congrArg (fun z : E => z 0) h
    have h1 := congrArg (fun z : E => z 1) h
    simp [point] at h0 h1
    ext i
    fin_cases i
    · change x 0=2-lambda+mu
      linarith
    · change x 1=2-lambda
      linarith
  · rintro rfl
    ext i
    fin_cases i <;> simp [point] <;> ring

theorem actual_halfspace_active_constraint_solves_candidate (lambda : ℝ) (x : E) :
    (gradient (halfspaceLagrangian lambda 0) x=0 ∧ affineConstraint 1 1 1 x=0) ↔
      lambda=3/2 ∧ x=point (1/2) (1/2) := by
  rw [actual_halfspace_stationarity_iff]
  constructor
  · rintro ⟨rfl,h⟩
    have hl : lambda=3/2 := by dsimp [affineConstraint,point] at h; linarith
    refine ⟨hl,?_⟩
    rw [hl]
    norm_num
  · rintro ⟨rfl,rfl⟩
    norm_num [affineConstraint,point]

def sourceQ : Matrix (Fin 2) (Fin 2) ℝ := !![2,0;0,4]
def sourceC : E := point (-2) 4
def sourceA : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;-1,0]
def sourceB : E := point 2 0
def qpObjective (x : E) : ℝ := inner ℝ x (applyMatrix sourceQ x)/2+inner ℝ sourceC x
def qpFeasible : Set E := {x | ∀ i, (applyMatrix sourceA x) i ≤ sourceB i}

theorem actual_source_qp_expansion (x : E) :
    weightedDistance 2 4 1 (-1) x=(x 0-1)^2+2*(x 1+1)^2 ∧
    weightedDistance 2 4 1 (-1) x=qpObjective x+3 ∧
    qpObjective x=(x 0)^2+2*(x 1)^2-2*x 0+4*x 1 := by
  rw [qpObjective,matrix_coordinate_action,inner_coordinate_formula,inner_coordinate_formula]
  dsimp [weightedDistance,sourceQ,sourceC,point]
  constructor
  · ring
  · constructor <;> ring

theorem actual_source_qp_constraints (x : E) :
    x∈qpFeasible ↔ x 0+x 1 ≤ 2 ∧ 0 ≤ x 0 := by
  change (∀ i,(applyMatrix sourceA x) i ≤ sourceB i) ↔ _
  rw [matrix_coordinate_action]
  simp [sourceA,sourceB,point,Fin.forall_fin_two]

theorem actual_source_q_is_positive_definite : sourceQ.PosDef := by
  have he : sourceQ=Matrix.diagonal (![2,4] : Fin 2 → ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sourceQ,Matrix.diagonal]
  rw [he,Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem actual_source_qp_unique_global_optimum (x : E) :
    0 ≤ weightedDistance 2 4 1 (-1) x ∧
    (weightedDistance 2 4 1 (-1) x=0 ↔ x=point 1 (-1)) ∧
    -3 ≤ qpObjective x ∧ (qpObjective x= -3 ↔ x=point 1 (-1)) ∧
    point 1 (-1)∈qpFeasible := by
  have he := actual_source_qp_expansion x
  have hpos : 0 ≤ weightedDistance 2 4 1 (-1) x := by rw [he.1];positivity
  have hzero : weightedDistance 2 4 1 (-1) x=0 ↔ x=point 1 (-1) := by
    rw [he.1]
    constructor
    · intro h
      have h0 : x 0=1 := by nlinarith [sq_nonneg (x 0-1),sq_nonneg (x 1+1)]
      have h1 : x 1= -1 := by nlinarith [sq_nonneg (x 0-1),sq_nonneg (x 1+1)]
      ext i
      fin_cases i <;> simp [point,h0,h1]
    · rintro rfl
      norm_num [point]
  refine ⟨hpos,hzero,?_,?_,?_⟩
  · linarith [he.2.1]
  · rw [← hzero,he.2.1]
    constructor <;> intro h <;> linarith
  · rw [actual_source_qp_constraints]
    norm_num [point]

end SafeLearning.CompleteFoundationsConstrainedModels
