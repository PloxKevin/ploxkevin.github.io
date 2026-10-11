import SafeLearning.CompleteFoundationsCalculusModels
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Matrix Topology

namespace SafeLearning.CompleteFoundationsLiteralGradientHessian28
open CompleteFoundationsSpectralModels (E point applyMatrix matrix_coordinate_action inner_coordinate_formula norm_squared_coordinates)
open CompleteFoundationsCalculusModels (coordinate)

def literalObjective (x : E) : ℝ := (x 0)^2+3*x 0*x 1
def literalHessian : Matrix (Fin 2) (Fin 2) ℝ := !![2,3;3,0]

theorem actual_literal_polynomial_is_twice_continuously_differentiable :
    ContDiff ℝ 2 literalObjective := by unfold literalObjective;fun_prop

theorem actual_literal_gradient (x : E) :
    HasGradientAt literalObjective (point (2*x 0+3*x 1) (3*x 0)) x := by
  have h0 := (coordinate 0).hasFDerivAt (x := x)
  have h1 := (coordinate 1).hasFDerivAt (x := x)
  have hf : HasFDerivAt literalObjective
      ((2*x 0+3*x 1) • coordinate 0+(3*x 0) • coordinate 1) x := by
    convert (h0.pow 2).add ((h0.mul h1).const_mul 3) using 1
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

theorem actual_literal_hessian_is_the_derivative_of_the_true_gradient (x : E) :
    HasFDerivAt (gradient literalObjective) (applyMatrix literalHessian) x := by
  have he : gradient literalObjective=applyMatrix literalHessian := by
    funext z
    rw [(actual_literal_gradient z).gradient,matrix_coordinate_action]
    simp [literalHessian]
  rw [he]
  exact (applyMatrix literalHessian).hasFDerivAt

theorem actual_literal_gradient_at_the_printed_point :
    gradient literalObjective (point 1 2)=point 8 3 := by
  rw [(actual_literal_gradient _).gradient]
  norm_num [point]

theorem actual_arbitrary_directional_line_derivative_at_the_printed_point (v : E) :
    HasDerivAt (fun t : ℝ => literalObjective (point 1 2+t • v))
      (inner ℝ (point 8 3) v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => point 1 2+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (point 1 2)
  have hgrad := actual_literal_gradient (point 1 2)
  have h := hgrad.hasFDerivAt.comp_hasDerivAt 0 hline
  simpa [Function.comp_def,point,InnerProductSpace.toDual_apply_apply] using h

theorem actual_printed_unit_direction_and_slope :
    ‖point (1/Real.sqrt 2) (1/Real.sqrt 2)‖=1 ∧
      inner ℝ (point 8 3) (point (1/Real.sqrt 2) (1/Real.sqrt 2))=11/Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have hn : Real.sqrt (2 : ℝ)≠0 := by positivity
  have hn2 := norm_squared_coordinates (point (1/Real.sqrt 2) (1/Real.sqrt 2))
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one] at hn2
  have hratio : (1/Real.sqrt (2 : ℝ))^2=1/2 := by rw [div_pow,one_pow,hs]
  constructor
  · rw [hratio] at hn2
    nlinarith [norm_nonneg (point (1/Real.sqrt 2) (1/Real.sqrt 2))]
  · rw [inner_coordinate_formula]
    simp [point]
    ring

theorem actual_printed_gradient_norm_and_steepest_unit_direction :
    ‖point 8 3‖=Real.sqrt 73 ∧
      ‖point (8/Real.sqrt 73) (3/Real.sqrt 73)‖=1 ∧
      inner ℝ (point 8 3) (point (8/Real.sqrt 73) (3/Real.sqrt 73))=Real.sqrt 73 ∧
      ∀ v : E,‖v‖=1 → inner ℝ (point 8 3) v≤Real.sqrt 73 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤73)
  have hp : 0<Real.sqrt (73 : ℝ) := by positivity
  have hnorm : ‖point 8 3‖=Real.sqrt 73 := by
    have hn := norm_squared_coordinates (point 8 3)
    norm_num [point] at hn
    nlinarith [norm_nonneg (point 8 3)]
  have hunit : ‖point (8/Real.sqrt 73) (3/Real.sqrt 73)‖=1 := by
    have hn := norm_squared_coordinates (point (8/Real.sqrt 73) (3/Real.sqrt 73))
    simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one] at hn
    have hr : (8/Real.sqrt (73 : ℝ))^2+(3/Real.sqrt 73)^2=1 := by
      field_simp
      nlinarith
    rw [hr] at hn
    nlinarith [norm_nonneg (point (8/Real.sqrt 73) (3/Real.sqrt 73))]
  have hattain : inner ℝ (point 8 3) (point (8/Real.sqrt 73) (3/Real.sqrt 73))=Real.sqrt 73 := by
    rw [inner_coordinate_formula]
    simp [point]
    field_simp
    nlinarith
  refine ⟨hnorm,hunit,hattain,?_⟩
  intro v hv
  simpa [hnorm,hv] using real_inner_le_norm (point 8 3) v

theorem actual_printed_slope_and_steepest_norm_decimal_roundings :
    (7775/1000 : ℝ)<11/Real.sqrt 2 ∧ 11/Real.sqrt 2<(7785/1000 : ℝ) ∧
      (8535/1000 : ℝ)<Real.sqrt 73 ∧ Real.sqrt 73<(8545/1000 : ℝ) := by
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have hs73 := Real.sq_sqrt (by norm_num : (0 : ℝ)≤73)
  have hp2 : 0<Real.sqrt (2 : ℝ) := by positivity
  have hp73 := Real.sqrt_nonneg (73 : ℝ)
  refine ⟨?_,?_,by nlinarith,by nlinarith⟩
  · rw [lt_div_iff₀ hp2]
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  · rw [div_lt_iff₀ hp2]
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem actual_literal_hessian_is_symmetric_with_nonnegative_diagonal :
    literalHessianᵀ=literalHessian ∧ (∀ i,literalHessian i i≥0) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [literalHessian,Matrix.transpose_apply]
  · intro i
    fin_cases i <;> norm_num [literalHessian]

theorem actual_literal_hessian_curves_up_and_down_in_genuine_directions :
    inner ℝ (point 1 1) (applyMatrix literalHessian (point 1 1))=8 ∧
      inner ℝ (point 1 (-1)) (applyMatrix literalHessian (point 1 (-1)))= -4 := by
  rw [matrix_coordinate_action,matrix_coordinate_action,inner_coordinate_formula,inner_coordinate_formula]
  norm_num [literalHessian,point]

theorem actual_literal_hessian_has_both_printed_eigenpairs :
    applyMatrix literalHessian (point (1+Real.sqrt 10) 3)=
      (1+Real.sqrt 10) • point (1+Real.sqrt 10) 3 ∧
    applyMatrix literalHessian (point (1-Real.sqrt 10) 3)=
      (1-Real.sqrt 10) • point (1-Real.sqrt 10) 3 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤10)
  constructor <;> rw [matrix_coordinate_action] <;> ext i <;> fin_cases i <;>
    simp [literalHessian,point] <;> nlinarith

theorem actual_literal_hessian_has_only_the_printed_two_eigenvalues (lambda : ℝ) :
    (∃x : E,x≠0 ∧ applyMatrix literalHessian x=lambda • x) ↔
      lambda=1+Real.sqrt 10 ∨ lambda=1-Real.sqrt 10 := by
  constructor
  · rintro ⟨x,hx,he⟩
    have h0 := congrArg (fun z : E => z 0) he
    have h1 := congrArg (fun z : E => z 1) he
    rw [matrix_coordinate_action] at h0 h1
    simp [literalHessian,point] at h0 h1
    have hx0 : x 0≠0 := by
      intro hz
      have hx1 : x 1=0 := by rw [hz] at h0;nlinarith
      apply hx
      ext i
      fin_cases i <;> simp [hz,hx1]
    have hproduct : (lambda^2-2*lambda-9)*x 0=0 := by nlinarith
    have hchar : lambda^2-2*lambda-9=0 := (mul_eq_zero.mp hproduct).resolve_right hx0
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤10)
    have hfactor : (lambda-(1+Real.sqrt 10))*(lambda-(1-Real.sqrt 10))=0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h|h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl|rfl)
    · refine ⟨point (1+Real.sqrt 10) 3,?_,actual_literal_hessian_has_both_printed_eigenpairs.1⟩
      intro h
      have hc := congrArg (fun z : E => z 1) h
      norm_num [point] at hc
    · refine ⟨point (1-Real.sqrt 10) 3,?_,actual_literal_hessian_has_both_printed_eigenpairs.2⟩
      intro h
      have hc := congrArg (fun z : E => z 1) h
      norm_num [point] at hc

theorem actual_literal_hessian_eigenvalue_signs_and_decimal_roundings :
    0<1+Real.sqrt (10 : ℝ) ∧ 1-Real.sqrt (10 : ℝ)<0 ∧
      (4155/1000 : ℝ)<1+Real.sqrt 10 ∧ 1+Real.sqrt 10<(4165/1000 : ℝ) ∧
      (-2165/1000 : ℝ)<1-Real.sqrt 10 ∧ 1-Real.sqrt 10<(-2155/1000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤10)
  have hp := Real.sqrt_nonneg (10 : ℝ)
  refine ⟨by linarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

section GenericC2Hessian
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev State := EuclideanSpace ℝ I
def jacobianGradientHessian (f : State → ℝ) (x : State) : Matrix I I ℝ :=
  fun i j => (fderiv ℝ (gradient f) x (EuclideanSpace.basisFun I ℝ j)) i
def secondPartialHessian (f : State → ℝ) (x : State) : Matrix I I ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.basisFun I ℝ j) (EuclideanSpace.basisFun I ℝ i)

theorem actual_c2_gradient_jacobian_entries_are_the_second_coordinate_partials
    (f : State → ℝ) (x : State) (hf : ContDiffAt ℝ 2 f x) :
    jacobianGradientHessian f x=secondPartialHessian f x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (by norm_num)).differentiableAt (by norm_num)
  have hg : HasFDerivAt (gradient f)
      (((InnerProductSpace.toDual ℝ State).symm.toContinuousLinearMap).comp
        (fderiv ℝ (fderiv ℝ f) x)) x := by
    simpa [gradient,Function.comp_def] using
      ((InnerProductSpace.toDual ℝ State).symm.toContinuousLinearMap).hasFDerivAt.comp x hd.hasFDerivAt
  ext i j
  unfold jacobianGradientHessian secondPartialHessian
  rw [hg.fderiv]
  change ((InnerProductSpace.toDual ℝ State).symm
    (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.basisFun I ℝ j))) i = _
  rw [← EuclideanSpace.inner_basisFun_real]
  change (InnerProductSpace.toDual ℝ State
    ((InnerProductSpace.toDual ℝ State).symm
      (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.basisFun I ℝ j))))
      (EuclideanSpace.basisFun I ℝ i) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem actual_c2_hessian_matrix_is_symmetric_from_commuting_mixed_partials
    (f : State → ℝ) (x : State) (hf : ContDiffAt ℝ 2 f x) :
    (jacobianGradientHessian f x)ᵀ=jacobianGradientHessian f x := by
  rw [actual_c2_gradient_jacobian_entries_are_the_second_coordinate_partials f x hf]
  ext i j
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq
    (EuclideanSpace.basisFun I ℝ i) (EuclideanSpace.basisFun I ℝ j)
end GenericC2Hessian

end SafeLearning.CompleteFoundationsLiteralGradientHessian28
