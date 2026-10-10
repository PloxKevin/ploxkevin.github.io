import SafeLearning.CompleteFoundationsSpectralModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsDefinitenessModels

open SafeLearning.CompleteFoundationsSpectralModels

def singularP : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2,0]
def indefiniteQ : Matrix (Fin 2) (Fin 2) ℝ := !![2,3;3,2]

theorem singular_P_positive_semidefinite : singularP.PosSemidef := by
  rw [singularP,Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem singular_P_actual_form (x : E) : quadratic singularP x=2*(x 0)^2 := by
  rw [quadratic,matrix_coordinate_action,inner_coordinate_formula]
  simp [singularP,point,Matrix.diagonal]
  ring

theorem singular_P_failure_witness : point 0 1≠0 ∧ quadratic singularP (point 0 1)=0 ∧
    singularP.det=0 ∧ ¬singularP.PosDef := by
  have hx : (![0,1] : Fin 2 → ℝ)≠0 := by
    intro h
    have hh := congrFun h 1
    norm_num at hh
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    have hh := congrArg (fun x : E => x 1) h
    norm_num [point] at hh
  · norm_num [singular_P_actual_form,point]
  · norm_num [singularP,Matrix.det_fin_two,Matrix.diagonal]
  · intro h
    have hh := h.dotProduct_mulVec_pos hx
    norm_num [singularP,Matrix.mulVec_diagonal,dotProduct,Fin.sum_univ_succ] at hh

theorem indefinite_Q_both_signs : quadratic indefiniteQ (point 1 1)=10 ∧
    quadratic indefiniteQ (point 1 (-1))= -2 ∧ ¬indefiniteQ.PosSemidef ∧
    ∀ i j,0 < indefiniteQ i j := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [quadratic,matrix_coordinate_action,inner_coordinate_formula]
    norm_num [indefiniteQ,point]
  · rw [quadratic,matrix_coordinate_action,inner_coordinate_formula]
    norm_num [indefiniteQ,point]
  · intro h
    have hh := h.dotProduct_mulVec_nonneg (![1,-1] : Fin 2 → ℝ)
    norm_num [indefiniteQ,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hh
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [indefiniteQ]

def choleskyP : Matrix (Fin 2) (Fin 2) ℝ := !![4,2;2,2]
def factorL : Matrix (Fin 2) (Fin 2) ℝ := !![2,0;1,1]

theorem cholesky_actual_factor : choleskyP=factorL*factorL.transpose ∧
    factorL 0 1=0 ∧ 0<factorL 0 0 ∧ 0<factorL 1 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [choleskyP,factorL,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ]
  all_goals norm_num [factorL]

theorem cholesky_positive_definite : choleskyP.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change choleskyP.conjTranspose=choleskyP
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [choleskyP,Matrix.conjTranspose_apply]
  · intro x hx
    have hn : x 0≠0 ∨ x 1≠0 := by
      by_contra h
      push Not at h
      apply hx
      ext i
      fin_cases i <;> simp [h.1,h.2]
    simp [choleskyP,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    rcases hn with h0|h1
    · nlinarith [sq_pos_of_ne_zero h0,sq_nonneg (x 0+x 1)]
    · nlinarith [sq_pos_of_ne_zero h1,sq_nonneg (2*x 0+x 1)]

theorem forward_triangular_solve_unique (y : E) :
    applyMatrix factorL y=point 6 4 ↔ y=point 3 1 := by
  rw [matrix_coordinate_action]
  constructor
  · intro h
    have h0 := congrArg (fun u : E => u 0) h
    have h1 := congrArg (fun u : E => u 1) h
    simp [factorL,point] at h0 h1
    ext i
    fin_cases i <;> simp [point] <;> linarith
  · rintro rfl
    norm_num [factorL,point]

theorem backward_triangular_solve_unique (x : E) :
    applyMatrix factorL.transpose x=point 3 1 ↔ x=point 1 1 := by
  rw [matrix_coordinate_action]
  constructor
  · intro h
    have h0 := congrArg (fun u : E => u 0) h
    have h1 := congrArg (fun u : E => u 1) h
    simp [factorL,point,Matrix.transpose_apply] at h0 h1
    ext i
    fin_cases i <;> simp [point] <;> linarith
  · rintro rfl
    norm_num [factorL,point,Matrix.transpose_apply]

theorem cholesky_source_solution : applyMatrix choleskyP (point 1 1)=point 6 4 := by
  rw [matrix_coordinate_action]
  norm_num [choleskyP,point]

theorem cholesky_actual_log_determinant : factorL.det=2 ∧ choleskyP.det=(factorL.det)^2 ∧
    choleskyP.det=4 ∧ Real.log choleskyP.det=2*(Real.log 2+Real.log 1) ∧
    Real.log choleskyP.det=Real.log 4 := by
  have hL : factorL.det=2 := by norm_num [factorL,Matrix.det_fin_two]
  have hP : choleskyP.det=4 := by norm_num [choleskyP,Matrix.det_fin_two]
  rw [hL,hP]
  norm_num
  rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
  norm_num

def ellipsoidP : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![4,1]
def ellipsoid : Set E := {x | quadratic ellipsoidP x≤1}
def margin (x : E) : ℝ := x 0+2*x 1
def transformed (x : E) : E := point (2*x 0) (x 1)
def ellipsoidMaximizer : E := point (1/(2*Real.sqrt 17)) (4/Real.sqrt 17)

theorem ellipsoid_actual_form (x : E) : quadratic ellipsoidP x=4*(x 0)^2+(x 1)^2 := by
  rw [quadratic,matrix_coordinate_action,inner_coordinate_formula]
  simp [ellipsoidP,point,Matrix.diagonal]
  ring

theorem ellipsoid_change_of_variables (x : E) :
    quadratic ellipsoidP x=‖transformed x‖^2 ∧
    margin x=inner ℝ (point (1/2) 2) (transformed x) ∧
    (x∈ellipsoid ↔ ‖transformed x‖≤1) := by
  have heq : quadratic ellipsoidP x=‖transformed x‖^2 := by
    rw [ellipsoid_actual_form,norm_squared_coordinates]
    simp [transformed,point]
    ring
  refine ⟨heq,?_,?_⟩
  · rw [inner_coordinate_formula]
    simp [margin,transformed,point]
  · change quadratic ellipsoidP x≤1 ↔ ‖transformed x‖≤1
    rw [heq]
    constructor <;> intro h <;> nlinarith [norm_nonneg (transformed x)]

theorem ellipsoid_coefficient_norm : ‖point (1/2) 2‖=Real.sqrt 17/2 := by
  have hn := norm_squared_coordinates (point (1/2) 2)
  have hn' : ‖point (1/2) 2‖^2=17/4 := by convert hn using 1 <;> norm_num [point]
  have hr := Real.sqrt_nonneg 17
  have hs : (Real.sqrt 17)^2=17 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg (point (1/2) 2),hn']

theorem ellipsoid_margin_upper_bound (x : E) (hx : x∈ellipsoid) : margin x≤Real.sqrt 17/2 := by
  rw [(ellipsoid_change_of_variables x).2.1]
  have hc := real_inner_le_norm (point (1/2) 2) (transformed x)
  rw [ellipsoid_coefficient_norm] at hc
  have hn := (ellipsoid_change_of_variables x).2.2.mp hx
  have hp : 0≤Real.sqrt 17/2 := by positivity
  nlinarith

theorem ellipsoid_attains : ellipsoidMaximizer∈ellipsoid ∧
    quadratic ellipsoidP ellipsoidMaximizer=1 ∧ margin ellipsoidMaximizer=Real.sqrt 17/2 ∧
    ‖transformed ellipsoidMaximizer‖=1 := by
  have hr : Real.sqrt 17≠0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<17)).ne'
  have hs : (Real.sqrt 17)^2=17 := Real.sq_sqrt (by norm_num)
  have hq : quadratic ellipsoidP ellipsoidMaximizer=1 := by
    rw [ellipsoid_actual_form]
    simp [ellipsoidMaximizer,point]
    field_simp [hr]
    nlinarith [hs]
  have hm : margin ellipsoidMaximizer=Real.sqrt 17/2 := by
    simp [margin,ellipsoidMaximizer,point]
    field_simp [hr]
    nlinarith [hs]
  refine ⟨by change quadratic ellipsoidP ellipsoidMaximizer≤1;rw [hq],hq,hm,?_⟩
  have hn := (ellipsoid_change_of_variables ellipsoidMaximizer).1
  rw [hq] at hn
  nlinarith [norm_nonneg (transformed ellipsoidMaximizer)]

theorem ellipsoid_actual_maximum : IsGreatest (margin '' ellipsoid) (Real.sqrt 17/2) := by
  constructor
  · exact ⟨ellipsoidMaximizer,ellipsoid_attains.1,ellipsoid_attains.2.2.1⟩
  · rintro z ⟨x,hx,rfl⟩
    exact ellipsoid_margin_upper_bound x hx

theorem ellipsoid_semiaxes (t : ℝ) :
    (point t 0∈ellipsoid ↔ |t|≤1/2) ∧ (point 0 t∈ellipsoid ↔ |t|≤1) := by
  change (quadratic ellipsoidP (point t 0)≤1 ↔ |t|≤1/2) ∧
    (quadratic ellipsoidP (point 0 t)≤1 ↔ |t|≤1)
  rw [ellipsoid_actual_form,ellipsoid_actual_form]
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,zero_pow,
    mul_zero,add_zero,zero_add,abs_le]
  constructor <;> constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (t-1/2),sq_nonneg (t+1/2)]
  · rintro ⟨h1,h2⟩
    nlinarith [mul_nonneg (by linarith : 0≤t+1/2) (by linarith : 0≤1/2-t)]
  · intro h
    constructor <;> nlinarith [sq_nonneg (t-1),sq_nonneg (t+1)]
  · rintro ⟨h1,h2⟩
    nlinarith [mul_nonneg (by linarith : 0≤t+1) (by linarith : 0≤1-t)]

def ellipsoidInverse : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1/4,1]

theorem ellipsoid_inverse_direction : ellipsoidP⁻¹=ellipsoidInverse ∧
    applyMatrix ellipsoidP⁻¹ (point 1 2)=point (1/4) 2 ∧
    ellipsoidMaximizer=(2/Real.sqrt 17) • applyMatrix ellipsoidP⁻¹ (point 1 2) ∧
    ¬∃ t : ℝ,ellipsoidMaximizer=t • point 1 2 := by
  have hi : ellipsoidP⁻¹=ellipsoidInverse := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ellipsoidP,ellipsoidInverse,Matrix.mul_apply,Matrix.diagonal,Fin.sum_univ_succ]
  have ha : applyMatrix ellipsoidP⁻¹ (point 1 2)=point (1/4) 2 := by
    rw [hi,matrix_coordinate_action]
    norm_num [ellipsoidInverse,point,Matrix.diagonal]
  refine ⟨hi,ha,?_,?_⟩
  · rw [ha]
    ext i
    fin_cases i <;> simp [ellipsoidMaximizer,point] <;> ring
  · rintro ⟨t,ht⟩
    have h0 := congrArg (fun x : E => x 0) ht
    have h1 := congrArg (fun x : E => x 1) ht
    simp [ellipsoidMaximizer,point] at h0 h1
    have hr : Real.sqrt 17≠0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<17)).ne'
    field_simp [hr] at h0 h1
    nlinarith

end SafeLearning.CompleteFoundationsDefinitenessModels
