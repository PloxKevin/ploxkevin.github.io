import SafeLearning.CompleteFoundationsSpectralModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped BigOperators Topology Matrix

namespace SafeLearning.CompleteFoundationsCalculusModels

abbrev E := EuclideanSpace ℝ (Fin 2)
open SafeLearning.CompleteFoundationsSpectralModels (point applyMatrix matrix_coordinate_action inner_coordinate_formula norm_squared_coordinates)
def coordinate (i : Fin 2) : E →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i

def sourceQuadratic (x : E) : ℝ := (x 0)^2+x 0*x 1+2*(x 1)^2
def quadraticH : Matrix (Fin 2) (Fin 2) ℝ := !![2,1;1,4]

theorem actual_quadratic_gradient (x : E) :
    HasGradientAt sourceQuadratic (applyMatrix quadraticH x) x := by
  have h0 := (coordinate 0).hasFDerivAt (x := x)
  have h1 := (coordinate 1).hasFDerivAt (x := x)
  have hf : HasFDerivAt sourceQuadratic
      ((2*x 0+x 1) • coordinate 0+(x 0+4*x 1) • coordinate 1) x := by
    convert ((h0.pow 2).add (h0.mul h1)).add ((h1.pow 2).const_mul 2) using 1
    · rfl
    · ext u
      simp [coordinate,PiLp.proj,PiLp.projₗ]
      ring
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf using 1
  ext u
  rw [matrix_coordinate_action]
  simp [quadraticH,point,coordinate,InnerProductSpace.toDual_apply_apply,PiLp.inner_apply,Fin.sum_univ_succ,PiLp.proj,PiLp.projₗ]
  ring

theorem actual_quadratic_gradient_function : gradient sourceQuadratic=applyMatrix quadraticH := by
  funext x
  exact (actual_quadratic_gradient x).gradient

theorem actual_quadratic_hessian (x : E) :
    HasFDerivAt (gradient sourceQuadratic) (applyMatrix quadraticH) x := by
  rw [actual_quadratic_gradient_function]
  exact (applyMatrix quadraticH).hasFDerivAt

theorem actual_quadratic_hessian_symmetric : quadraticHᵀ=quadraticH := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadraticH,Matrix.transpose_apply]

theorem actual_quadratic_gradient_coordinates (x : E) :
    gradient sourceQuadratic x=point (2*x 0+x 1) (x 0+4*x 1) := by
  rw [actual_quadratic_gradient_function,matrix_coordinate_action]
  simp [quadraticH]

theorem actual_directional_derivative :
    gradient sourceQuadratic (point 1 (-1))=point 1 (-3) ∧
    fderiv ℝ sourceQuadratic (point 1 (-1)) (point 0 1)= -3 := by
  constructor
  · rw [actual_quadratic_gradient_coordinates]
    norm_num [point]
  · rw [(actual_quadratic_gradient _).fderiv_apply,matrix_coordinate_action,inner_coordinate_formula]
    norm_num [quadraticH,point]

theorem actual_vertical_displacement (t : ℝ) :
    sourceQuadratic (point 1 (-1+t))-sourceQuadratic (point 1 (-1))= -3*t+2*t^2 := by
  simp [sourceQuadratic,point]
  ring

theorem actual_vertical_bigO :
    (fun t : ℝ => sourceQuadratic (point 1 (-1+t))-sourceQuadratic (point 1 (-1))+3*t)
      =O[𝓝 0] (fun t : ℝ => t^2) := by
  have he : (fun t : ℝ => sourceQuadratic (point 1 (-1+t))-sourceQuadratic (point 1 (-1))+3*t)=
      (fun t : ℝ => 2*t^2) := by
    funext t
    rw [actual_vertical_displacement]
    ring
  rw [he]
  exact Asymptotics.isBigO_const_mul_self 2 (fun t : ℝ => t^2) _

def margin (x : E) : ℝ := 1-(x 0)^2-(x 1)^2
def curve (t : ℝ) : E := point t (t^2)

theorem actual_margin_gradient (x : E) : HasGradientAt margin (point (-2*x 0) (-2*x 1)) x := by
  have h0 := (coordinate 0).hasFDerivAt (x := x)
  have h1 := (coordinate 1).hasFDerivAt (x := x)
  have hf : HasFDerivAt margin ((-2*x 0) • coordinate 0+(-2*x 1) • coordinate 1) x := by
    convert ((h0.pow 2).const_sub 1).sub (h1.pow 2) using 1
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

theorem actual_curve_velocity (t : ℝ) : HasDerivAt curve (point 1 (2*t)) t := by
  convert ((hasDerivAt_id t).smul_const (point 1 0)).add
    (((hasDerivAt_id t).pow 2).smul_const (point 0 1)) using 1
  · funext z
    ext i
    fin_cases i <;> simp [curve,point]
  · ext i
    fin_cases i <;> simp [point]

theorem actual_substituted_curve (t : ℝ) : margin (curve t)=1-t^2-t^4 := by
  simp [margin,curve,point]
  ring

theorem actual_substitution_derivative (t : ℝ) :
    HasDerivAt (fun z => margin (curve z)) (-2*t-4*t^3) t := by
  have he : (fun z => margin (curve z))=(fun z : ℝ => 1-z^2-z^4) :=
    funext actual_substituted_curve
  rw [he]
  convert (((hasDerivAt_id t).pow 2).const_sub 1).sub ((hasDerivAt_id t).pow 4) using 1
  · ext z;simp [id_eq]
  · simp [id_eq]

theorem actual_chain_rule_derivative (t : ℝ) :
    HasDerivAt (fun z => margin (curve z))
      (inner ℝ (gradient margin (curve t)) (point 1 (2*t))) t ∧
    inner ℝ (gradient margin (curve t)) (point 1 (2*t))= -2*t-4*t^3 := by
  have hgradient := actual_margin_gradient (curve t)
  have h := hgradient.hasFDerivAt.comp_hasDerivAt t (actual_curve_velocity t)
  constructor
  · convert h using 1 <;> simp [Function.comp_def,InnerProductSpace.toDual_apply_apply,hgradient.gradient]
  · rw [hgradient.gradient,inner_coordinate_formula]
    simp [curve,point]
    ring

theorem actual_curve_source_values :
    margin (curve 1)= -1 ∧ deriv (fun t => margin (curve t)) 1= -6 ∧
    margin (curve 1)<0 ∧ deriv (fun t => margin (curve t)) 1<0 := by
  rw [(actual_substitution_derivative 1).deriv,actual_substituted_curve]
  norm_num

section GeneralLeastSquares
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

def leastSquares (A : V →L[ℝ] W) (b : W) (x : V) : ℝ := ‖A x-b‖^2

theorem actual_least_squares_gradient (A : V →L[ℝ] W) (b : W) (x : V) :
    HasGradientAt (leastSquares A b) ((2 : ℝ) • A.adjoint (A x-b)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (A.hasFDerivAt.sub_const b).norm_sq using 1
  · rfl
  · ext u
    simp [InnerProductSpace.toDual_apply_apply,real_inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left,innerSL_apply_apply]

theorem actual_least_squares_hessian (A : V →L[ℝ] W) (b : W) (x : V) :
    HasFDerivAt (gradient (leastSquares A b)) ((2 : ℝ) • A.adjoint.comp A) x := by
  have he : gradient (leastSquares A b)=(fun x => (2 : ℝ) • A.adjoint (A x-b)) := by
    funext z
    exact (actual_least_squares_gradient A b z).gradient
  rw [he]
  exact (A.adjoint.hasFDerivAt.comp x (A.hasFDerivAt.sub_const b)).const_smul 2
end GeneralLeastSquares

def leastA : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,2]
def leastB : E := point 1 1
def leastObjective (x : E) : ℝ := leastSquares (applyMatrix leastA) leastB x

theorem actual_least_square_expansion (x : E) :
    leastObjective x=(x 0-1)^2+(2*x 1-1)^2 := by
  rw [leastObjective,leastSquares,norm_squared_coordinates,matrix_coordinate_action]
  simp [leastA,leastB,point]

theorem actual_least_square_gradient (x : E) :
    HasGradientAt leastObjective (point (2*(x 0-1)) (4*(2*x 1-1))) x := by
  have h0 := (coordinate 0).hasFDerivAt (x := x)
  have h1 := (coordinate 1).hasFDerivAt (x := x)
  have hf : HasFDerivAt leastObjective
      ((2*(x 0-1)) • coordinate 0+(4*(2*x 1-1)) • coordinate 1) x := by
    have he : leastObjective=(fun x : E => (x 0-1)^2+(2*x 1-1)^2) := funext actual_least_square_expansion
    rw [he]
    convert ((h0.sub_const 1).pow 2).add (((h1.const_mul 2).sub_const 1).pow 2) using 1
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

theorem actual_least_square_residual_gradient (x : E) :
    gradient leastObjective x=(2 : ℝ) • applyMatrix leastAᵀ (applyMatrix leastA x-leastB) := by
  rw [(actual_least_square_gradient x).gradient,matrix_coordinate_action,matrix_coordinate_action]
  ext i
  fin_cases i <;> simp [point,leastA,leastB,Matrix.transpose_apply] <;> ring

def leastH : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2,8]

theorem actual_least_square_hessian (x : E) :
    leastH=(2 : ℝ) • (leastAᵀ*leastA) ∧ leastH.PosDef ∧
    HasFDerivAt (gradient leastObjective) (applyMatrix leastH) x := by
  have hh : leastH=(2 : ℝ) • (leastAᵀ*leastA) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [leastH,leastA,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]
  have hp : leastH.PosDef := by
    rw [leastH,Matrix.posDef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  have hg : gradient leastObjective=(fun x => applyMatrix leastH x-point 2 4) := by
    funext z
    rw [(actual_least_square_gradient z).gradient,matrix_coordinate_action]
    ext i
    fin_cases i <;> simp [leastH,point] <;> ring
  refine ⟨hh,hp,?_⟩
  rw [hg]
  exact (applyMatrix leastH).hasFDerivAt.sub_const (point 2 4)

theorem actual_least_square_unique_minimum (x : E) :
    0≤leastObjective x ∧ (leastObjective x=0 ↔ x=point 1 (1/2)) := by
  rw [actual_least_square_expansion]
  constructor
  · positivity
  · constructor
    · intro h
      have h0 : x 0=1 := by nlinarith [sq_nonneg (x 0-1),sq_nonneg (2*x 1-1)]
      have h1 : x 1=1/2 := by nlinarith [sq_nonneg (x 0-1),sq_nonneg (2*x 1-1)]
      ext i
      fin_cases i <;> simp [point,h0,h1]
    · rintro rfl
      norm_num [point]

theorem actual_least_square_matrix_invertible : IsUnit leastA := by
  rw [Matrix.isUnit_iff_isUnit_det]
  norm_num [leastA,Matrix.det_diagonal,Fin.prod_univ_succ,isUnit_iff_ne_zero]

theorem actual_least_square_source_values :
    applyMatrix leastA 0-leastB=point (-1) (-1) ∧
    gradient leastObjective 0=point (-2) (-4) ∧
    applyMatrix leastA (point 1 (1/2))=leastB := by
  constructor
  · rw [map_zero]
    ext i
    fin_cases i <;> norm_num [point,leastB]
  constructor
  · rw [(actual_least_square_gradient 0).gradient]
    norm_num [point]
  · rw [matrix_coordinate_action]
    norm_num [leastA,leastB,point]

end SafeLearning.CompleteFoundationsCalculusModels
