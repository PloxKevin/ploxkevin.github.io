import SafeLearning.CompleteFoundationsCalculusModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace SafeLearning.CompleteFoundationsSolutionSensitivity

section Generic
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem actual_differentiated_linear_system
    (A : ℝ → V →L[ℝ] W) (x : ℝ → V) (b : ℝ → W) (t : ℝ)
    (Ad : V →L[ℝ] W) (xd : V) (bd : W)
    (hA : HasDerivAt A Ad t) (hx : HasDerivAt x xd t) (hb : HasDerivAt b bd t)
    (heq : ∀ᶠ s in 𝓝 t, A s (x s)=b s) :
    Ad (x t)+A t xd=bd := by
  have h := hA.clm_apply hx
  have heq' : b =ᶠ[𝓝 t] (fun s => A s (x s)) := heq.mono (fun _ h => h.symm)
  have h' : HasDerivAt b (Ad (x t)+A t xd) t := h.congr_of_eventuallyEq heq'
  exact h'.unique hb

theorem actual_sensitivity_is_linear_solve
    (A : ℝ → V →L[ℝ] W) (x : ℝ → V) (b : ℝ → W) (t : ℝ)
    (Ad : V →L[ℝ] W) (xd : V) (bd : W)
    (hA : HasDerivAt A Ad t) (hx : HasDerivAt x xd t) (hb : HasDerivAt b bd t)
    (heq : ∀ᶠ s in 𝓝 t, A s (x s)=b s) :
    A t xd=bd-Ad (x t) := by
  have h := actual_differentiated_linear_system A x b t Ad xd bd hA hx hb heq
  exact eq_sub_of_add_eq' h

theorem actual_invertible_sensitivity_solution
    (A : ℝ → V →L[ℝ] W) (x : ℝ → V) (b : ℝ → W) (t : ℝ)
    (Ad : V →L[ℝ] W) (xd : V) (bd : W)
    (hA : HasDerivAt A Ad t) (hx : HasDerivAt x xd t) (hb : HasDerivAt b bd t)
    (heq : ∀ᶠ s in 𝓝 t, A s (x s)=b s)
    (equiv : V ≃L[ℝ] W) (hequiv : equiv.toContinuousLinearMap=A t) :
    xd=equiv.symm (bd-Ad (x t)) := by
  have h := actual_sensitivity_is_linear_solve A x b t Ad xd bd hA hx hb heq
  rw [← hequiv] at h
  exact equiv.injective (by simpa using h)

end Generic

abbrev E := EuclideanSpace ℝ (Fin 2)
open SafeLearning.CompleteFoundationsSpectralModels (point applyMatrix matrix_coordinate_action norm_squared_coordinates)

def sourceMatrix (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1+theta,2]
def sourceOperator (theta : ℝ) : E →L[ℝ] E := applyMatrix (sourceMatrix theta)
def matrixDerivative : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,0]
def operatorDerivative : E →L[ℝ] E := applyMatrix matrixDerivative
def rightSide : E := point 2 4
def explicitSolution (theta : ℝ) : E := point (2/(1+theta)) 2
def firstOrderPrediction (theta : ℝ) : E := point (2-2*theta) 2

theorem actual_operator_coordinates (theta : ℝ) (x : E) :
    sourceOperator theta x=point ((1+theta)*x 0) (2*x 1) := by
  rw [sourceOperator,matrix_coordinate_action]
  simp [sourceMatrix]

theorem actual_matrix_derivative (theta : ℝ) :
    HasDerivAt sourceOperator operatorDerivative theta := by
  have he : sourceOperator=(fun s : ℝ => sourceOperator 0+s • operatorDerivative) := by
    funext s
    ext x i
    fin_cases i <;>
      simp [sourceOperator,sourceMatrix,operatorDerivative,matrixDerivative,matrix_coordinate_action,point]
    ring
  rw [he]
  simpa using ((hasDerivAt_id theta).smul_const operatorDerivative).const_add (sourceOperator 0)

theorem actual_source_solution_iff (theta : ℝ) (ht : -1<theta) (x : E) :
    sourceOperator theta x=rightSide ↔ x=explicitSolution theta := by
  have hn : 1+theta≠0 := by linarith
  rw [actual_operator_coordinates]
  constructor
  · intro h
    have h0 := congrArg (fun v : E => v 0) h
    have h1 := congrArg (fun v : E => v 1) h
    simp [point,rightSide] at h0 h1
    ext i
    fin_cases i
    · simp [explicitSolution,point]
      exact (eq_div_iff hn).mpr (by nlinarith)
    · simp [explicitSolution,point]
      linarith
  · intro h
    subst x
    ext i
    fin_cases i <;> norm_num [explicitSolution,rightSide,point] <;> field_simp

theorem actual_explicit_solution_derivative (theta : ℝ) (ht : -1<theta) :
    HasDerivAt explicitSolution (point (-2/(1+theta)^2) 0) theta := by
  have hn : 1+theta≠0 := by linarith
  have hscalar : HasDerivAt (fun s : ℝ => 2/(1+s)) (-2/(1+theta)^2) theta := by
    convert (hasDerivAt_const theta (2 : ℝ)).div ((hasDerivAt_id theta).const_add 1) hn using 1
    · rfl
    · simp
  convert (hscalar.smul_const (point 1 0)).add (hasDerivAt_const theta (point 0 2)) using 1
  · funext s
    ext i
    fin_cases i <;> simp [explicitSolution,point]
  · ext i
    fin_cases i <;> simp [point]

theorem actual_equation_forces_source_sensitivity
    (x : ℝ → E) (xd : E) (hx : HasDerivAt x xd 0)
    (heq : ∀ theta : ℝ, -1<theta → sourceOperator theta (x theta)=rightSide) :
    x 0=point 2 2 ∧ xd=point (-2) 0 := by
  have hx0 := (actual_source_solution_iff 0 (by norm_num) (x 0)).mp (heq 0 (by norm_num))
  have hxzero : x 0=point 2 2 := by simpa [explicitSolution] using hx0
  have hevent : ∀ᶠ s : ℝ in 𝓝 0, sourceOperator s (x s)=rightSide := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (-1 : ℝ)<0)] with s hs
    exact heq s hs
  have h := actual_differentiated_linear_system sourceOperator x (fun _ => rightSide) 0
    operatorDerivative xd 0 (actual_matrix_derivative 0) hx (hasDerivAt_const 0 rightSide) hevent
  rw [hxzero] at h
  have h0 := congrArg (fun v : E => v 0) h
  have h1 := congrArg (fun v : E => v 1) h
  simp [operatorDerivative,matrixDerivative,matrix_coordinate_action,actual_operator_coordinates,point] at h0 h1
  refine ⟨hxzero,?_⟩
  ext i
  fin_cases i <;> simp [point] <;> linarith

theorem actual_source_zero_data : sourceMatrix 0=Matrix.diagonal ![(1 : ℝ),2] ∧
    explicitSolution 0=point 2 2 ∧
    deriv explicitSolution 0=point (-2) 0 ∧
    sourceOperator 0 (point (-2) 0)= -operatorDerivative (explicitSolution 0) := by
  rw [(actual_explicit_solution_derivative 0 (by norm_num)).deriv]
  constructor
  · norm_num [sourceMatrix]
  constructor
  · norm_num [explicitSolution]
  constructor
  · norm_num
  · ext i
    fin_cases i <;>
      norm_num [actual_operator_coordinates,operatorDerivative,matrixDerivative,explicitSolution,matrix_coordinate_action,point]

theorem actual_prediction_is_tangent (theta : ℝ) :
    firstOrderPrediction theta=explicitSolution 0+theta • deriv explicitSolution 0 := by
  rw [actual_source_zero_data.2.2.1]
  ext i
  fin_cases i <;> simp [firstOrderPrediction,explicitSolution,point] <;> ring

theorem actual_exact_prediction_difference (theta : ℝ) (ht : -1<theta) :
    explicitSolution theta-firstOrderPrediction theta=point (2*theta^2/(1+theta)) 0 := by
  have hn : 1+theta≠0 := by linarith
  ext i
  fin_cases i <;> simp [explicitSolution,firstOrderPrediction,point]
  field_simp
  ring

theorem actual_horizontal_norm (r : ℝ) : ‖point r 0‖=|r| := by
  have h := norm_squared_coordinates (point r 0)
  simp [point] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp (by simpa [point,sq_abs] using h)

theorem actual_prediction_error (theta : ℝ) (ht : -1<theta) :
    ‖explicitSolution theta-firstOrderPrediction theta‖=2*theta^2/(1+theta) := by
  rw [actual_exact_prediction_difference theta ht,actual_horizontal_norm,abs_of_nonneg]
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith)

theorem actual_prediction_error_bigO :
    (fun theta : ℝ => explicitSolution theta-firstOrderPrediction theta)
      =O[𝓝 0] (fun theta : ℝ => theta^2) := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1/2 : ℝ)<0) (by norm_num : (0 : ℝ)<1/2)] with theta ht
  rw [actual_prediction_error theta (by linarith [ht.1]),Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (div_le_iff₀ (by linarith [ht.1] : 0<1+theta)).mpr
  have h := mul_nonneg (sq_nonneg theta) (show 0≤2+4*theta by linarith [ht.1])
  nlinarith

theorem actual_source_prediction_values :
    firstOrderPrediction (1/100)=point (99/50) 2 ∧
    explicitSolution (1/100)=point (200/101) 2 ∧
    ‖explicitSolution (1/100)-firstOrderPrediction (1/100)‖=1/5050 ∧
    |explicitSolution (1/100) 0-(1980198020/1000000000 : ℝ)|<1/2000000000 ∧
    |‖explicitSolution (1/100)-firstOrderPrediction (1/100)‖-(198020/1000000000 : ℝ)|<1/2000000000 := by
  rw [actual_prediction_error (1/100) (by norm_num)]
  norm_num [firstOrderPrediction,explicitSolution,point]

end SafeLearning.CompleteFoundationsSolutionSensitivity
