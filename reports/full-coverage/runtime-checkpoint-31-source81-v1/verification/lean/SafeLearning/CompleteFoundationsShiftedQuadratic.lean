import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsShiftedQuadratic

abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
def objective (x : E) : ℝ := (x 0)^2+4*(x 1)^2-2*x 0-8*x 1
def sourceH : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2,8]
def hessian : E →L[ℝ] E := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) sourceH
def sourceC : E := point 2 8
def sourceGradient (x : E) : E := point (2*x 0-2) (8*x 1-8)
def coordinate (i : Fin 2) : E →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i

theorem objective_frechet_derivative (x : E) :
    HasFDerivAt objective ((2*x 0-2) • coordinate 0+(8*x 1-8) • coordinate 1) x := by
  have h0 := (coordinate 0).hasFDerivAt (x := x)
  have h1 := (coordinate 1).hasFDerivAt (x := x)
  convert (((h0.pow 2).add ((h1.pow 2).const_mul 4)).sub (h0.const_mul 2)).sub
    (h1.const_mul 8) using 1
  · rfl
  · ext u
    simp [coordinate,PiLp.proj,PiLp.projₗ]
    ring

theorem objective_actual_gradient (x : E) : HasGradientAt objective (sourceGradient x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert objective_frechet_derivative x using 1
  ext u
  simp [sourceGradient,point,coordinate,InnerProductSpace.toDual_apply_apply,
    PiLp.inner_apply,Fin.sum_univ_succ,PiLp.proj,PiLp.projₗ]
  ring

theorem gradient_identification (x : E) : gradient objective x=sourceGradient x :=
  (objective_actual_gradient x).gradient

theorem hessian_coordinates (x : E) : hessian x=point (2*x 0) (8*x 1) := by
  ext i
  change (sourceH *ᵥ (x : Fin 2 → ℝ)) i=(![2*x 0,8*x 1] : Fin 2 → ℝ) i
  fin_cases i <;> simp [sourceH,Matrix.mulVec_diagonal]

theorem gradient_is_Hx_minus_c (x : E) : sourceGradient x=hessian x-sourceC := by
  rw [hessian_coordinates]
  ext i
  fin_cases i <;> simp [sourceGradient,sourceC,point]

theorem gradient_actual_hessian (x : E) : HasFDerivAt (gradient objective) hessian x := by
  have heq : gradient objective=(fun x => hessian x-sourceC) := by
    ext z
    rw [gradient_identification,gradient_is_Hx_minus_c]
  rw [heq]
  simpa using hessian.hasFDerivAt.sub_const sourceC

theorem objective_is_stated_matrix_quadratic (x : E) :
    objective x=(1/2 : ℝ)*inner ℝ x (hessian x)-inner ℝ sourceC x := by
  rw [hessian_coordinates]
  simp [objective,sourceC,point,PiLp.inner_apply,Fin.sum_univ_succ]
  ring

theorem hessian_positive_definite : sourceH.PosDef := by
  rw [sourceH,Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem completed_square_identity (x : E) :
    objective x=(x 0-1)^2+4*(x 1-1)^2-5 := by unfold objective;ring

theorem unique_global_minimum (x : E) :
    objective (point 1 1)≤objective x ∧ (objective x=objective (point 1 1) ↔ x=point 1 1) := by
  have hmin : objective (point 1 1)= -5 := by norm_num [objective,point]
  rw [hmin,completed_square_identity]
  constructor
  · nlinarith [sq_nonneg (x 0-1),sq_nonneg (x 1-1)]
  · constructor
    · intro h
      have h0 : x 0=1 := by nlinarith [sq_nonneg (x 0-1),sq_nonneg (x 1-1)]
      have h1 : x 1=1 := by nlinarith [sq_nonneg (x 0-1),sq_nonneg (x 1-1)]
      ext i
      fin_cases i <;> simp [point,h0,h1]
    · rintro rfl
      norm_num [point]

theorem stationary_equation_iff (x : E) : hessian x=sourceC ↔ x=point 1 1 := by
  rw [hessian_coordinates]
  constructor
  · intro h
    have h0 := congrArg (fun u : E => u 0) h
    have h1 := congrArg (fun u : E => u 1) h
    simp [point,sourceC] at h0 h1
    ext i
    fin_cases i <;> simp [point] <;> linarith
  · rintro rfl
    norm_num [point,sourceC]

theorem quadratic_taylor_model_exact (x d : E) :
    objective (x+d)=objective x+inner ℝ (sourceGradient x) d+
      (1/2 : ℝ)*inner ℝ d (hessian d) := by
  rw [hessian_coordinates]
  simp [objective,sourceGradient,point,PiLp.inner_apply,Fin.sum_univ_succ]
  ring

def newtonCorrection (x : E) : E := point (1-x 0) (1-x 1)
def newtonStep (x : E) : E := x+newtonCorrection x
def gradientStep (eta : ℝ) (x : E) : E := x-eta • gradient objective x

theorem newton_equation_unique (x d : E) : hessian d= -gradient objective x ↔ d=newtonCorrection x := by
  rw [gradient_identification,hessian_coordinates]
  constructor
  · intro h
    have h0 := congrArg (fun u : E => u 0) h
    have h1 := congrArg (fun u : E => u 1) h
    simp [point,sourceGradient] at h0 h1
    ext i
    fin_cases i <;> simp [newtonCorrection,point] <;> linarith
  · rintro rfl
    ext i
    fin_cases i <;> simp [newtonCorrection,sourceGradient,point] <;> ring

theorem full_newton_step_solves (x : E) : newtonStep x=point 1 1 := by
  ext i
  fin_cases i <;> simp [newtonStep,newtonCorrection,point]

theorem source_numerical_steps :
    gradient objective (point 3 0)=point 4 (-8) ∧
    newtonCorrection (point 3 0)=point (-2) 1 ∧
    newtonStep (point 3 0)=point 1 1 ∧
    gradientStep (1/8) (point 3 0)=point (5/2) 1 := by
  rw [gradient_identification]
  refine ⟨?_,?_,full_newton_step_solves _,?_⟩
  · ext i
    fin_cases i <;> norm_num [sourceGradient,point]
  · ext i
    fin_cases i <;> norm_num [newtonCorrection,point]
  · rw [gradientStep,gradient_identification]
    ext i
    fin_cases i <;> norm_num [sourceGradient,point]

theorem gradient_step_remaining_error :
    (gradientStep (1/8) (point 3 0)-point 1 1) 0=3/2 ∧
    objective (gradientStep (1/8) (point 3 0))-objective (point 1 1)=9/4 := by
  rw [source_numerical_steps.2.2.2]
  norm_num [objective,point]

theorem actual_eigenvalues (lambda : ℝ) :
    (∃ x : E,x≠0 ∧ hessian x=lambda • x) ↔ lambda=2 ∨ lambda=8 := by
  constructor
  · rintro ⟨x,hx,h⟩
    by_contra hn
    push_neg at hn
    have h0 := congrArg (fun u : E => u 0) h
    have h1 := congrArg (fun u : E => u 1) h
    rw [hessian_coordinates] at h0 h1
    simp [point] at h0 h1
    have hz0 : x 0=0 := h0.resolve_left (fun hh => hn.1 hh.symm)
    have hz1 : x 1=0 := h1.resolve_left (fun hh => hn.2 hh.symm)
    apply hx
    ext i
    fin_cases i <;> simp [hz0,hz1]
  · rintro (rfl|rfl)
    · refine ⟨point 1 0,?_,?_⟩
      · intro h
        have hh := congrArg (fun x : E => x 0) h
        norm_num [point] at hh
      · rw [hessian_coordinates]
        ext i
        fin_cases i <;> norm_num [point]
    · refine ⟨point 0 1,?_,?_⟩
      · intro h
        have hh := congrArg (fun x : E => x 1) h
        norm_num [point] at hh
      · rw [hessian_coordinates]
        ext i
        fin_cases i <;> norm_num [point]

def inverseH : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1/2,1/8]

theorem actual_matrix_inverse : sourceH⁻¹=inverseH := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceH,inverseH,Matrix.mul_apply,Matrix.diagonal,Fin.sum_univ_succ]

theorem matrix_condition_number : ‖sourceH‖=8 ∧ ‖sourceH⁻¹‖=1/2 ∧ ‖sourceH‖*‖sourceH⁻¹‖=4 := by
  have hH : ‖sourceH‖=8 := by
    rw [sourceH,Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤8)).mpr
      intro i
      fin_cases i <;> norm_num
    · simpa using norm_le_pi_norm (![2,8] : Fin 2 → ℝ) (1 : Fin 2)
  have hI : ‖sourceH⁻¹‖=1/2 := by
    rw [actual_matrix_inverse,inverseH,Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤1/2)).mpr
      intro i
      fin_cases i <;> norm_num
    · simpa using norm_le_pi_norm (![1/2,1/8] : Fin 2 → ℝ) (0 : Fin 2)
  exact ⟨hH,hI,by rw [hH,hI];norm_num⟩

end SafeLearning.CompleteFoundationsShiftedQuadratic
