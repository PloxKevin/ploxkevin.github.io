import SafeLearning.CompleteFoundationsMatrixNormModels
import SafeLearning.CompleteFoundationsSpectralModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsSVDModels

abbrev E := EuclideanSpace ℝ (Fin 2)
open SafeLearning.CompleteFoundationsSpectralModels (point applyMatrix norm_squared_coordinates matrix_coordinate_action)
open SafeLearning.CompleteFoundationsMatrixNormModels (diagonal_two_spectral_norm)

def sourceA : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2,-1]
def signU : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,-1]
def stretchSigma : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2,1]
def rightV : Matrix (Fin 2) (Fin 2) ℝ := 1

theorem actual_svd_product : sourceA=signU*stretchSigma*rightVᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceA,signU,stretchSigma,rightV,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]

theorem actual_svd_orthogonal : signUᵀ*signU=1 ∧ rightVᵀ*rightV=1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [signU,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]
  · simp [rightV]

theorem actual_gram_matrix : sourceAᵀ*sourceA=Matrix.diagonal ![4,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceA,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]

theorem diagonal_all_eigenvalues (a b lambda : ℝ) :
    (∃ x : E, x≠0 ∧ applyMatrix (Matrix.diagonal ![a,b]) x=lambda • x) ↔
      lambda=a ∨ lambda=b := by
  constructor
  · rintro ⟨x,hx,h⟩
    have h0 := congrArg (fun u : E => u 0) h
    have h1 := congrArg (fun u : E => u 1) h
    simp [matrix_coordinate_action,Matrix.diagonal,point] at h0 h1
    by_cases hx0 : x 0=0
    · have hx1 : x 1≠0 := by
        intro hz
        apply hx
        ext i
        fin_cases i <;> simp [hx0,hz]
      right
      exact (h1.resolve_right hx1).symm
    · left
      exact (h0.resolve_right hx0).symm
  · rintro (rfl|rfl)
    · refine ⟨point 1 0,?_,?_⟩
      · intro h
        have h0 := congrArg (fun u : E => u 0) h
        norm_num [point] at h0
      · ext i
        fin_cases i <;> simp [matrix_coordinate_action,Matrix.diagonal,point]
    · refine ⟨point 0 1,?_,?_⟩
      · intro h
        have h1 := congrArg (fun u : E => u 1) h
        norm_num [point] at h1
      · ext i
        fin_cases i <;> simp [matrix_coordinate_action,Matrix.diagonal,point]

def isSingularValue (A : Matrix (Fin 2) (Fin 2) ℝ) (sigma : ℝ) : Prop :=
  0 ≤ sigma ∧ ∃ x : E, x≠0 ∧ applyMatrix (Aᵀ*A) x=(sigma^2) • x

theorem actual_singular_values (sigma : ℝ) :
    isSingularValue sourceA sigma ↔ sigma=2 ∨ sigma=1 := by
  rw [isSingularValue,actual_gram_matrix,diagonal_all_eigenvalues]
  constructor
  · rintro ⟨hs,h⟩
    rcases h with h|h
    · left; nlinarith
    · right; nlinarith
  · rintro (rfl|rfl) <;> norm_num

theorem actual_signed_eigenvalues (lambda : ℝ) :
    (∃ x : E,x≠0 ∧ applyMatrix sourceA x=lambda • x) ↔ lambda=2 ∨ lambda= -1 :=
  diagonal_all_eigenvalues 2 (-1) lambda

theorem actual_spectral_norm : ‖sourceA‖=2 := by
  rw [sourceA,diagonal_two_spectral_norm]
  norm_num

section Frobenius
open scoped Matrix.Norms.Frobenius
theorem actual_frobenius_norm : ‖sourceA‖=Real.sqrt 5 := by
  have h : ‖sourceA‖=Real.sqrt (∑ i,∑ j,sourceA i j^2) := by
    simpa [Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow,one_div] using Matrix.frobenius_norm_def sourceA
  rw [h]
  norm_num [sourceA,Fin.sum_univ_succ,Matrix.diagonal]
end Frobenius

theorem actual_inverse : sourceA⁻¹=Matrix.diagonal ![1/2,-1] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceA,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]

theorem actual_condition_number : ‖sourceA‖*‖sourceA⁻¹‖=2 ∧ (2 : ℝ)/1=2 := by
  rw [actual_spectral_norm,actual_inverse]
  rw [diagonal_two_spectral_norm]
  norm_num

theorem actual_coordinate_action (x : E) : applyMatrix sourceA x=point (2*x 0) (-x 1) := by
  ext i
  fin_cases i <;> simp [sourceA,matrix_coordinate_action,Matrix.diagonal,point]

theorem actual_unit_circle_image :
    applyMatrix sourceA '' {x : E | ‖x‖=1}={y : E | (y 0)^2/4+(y 1)^2=1} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hn := norm_squared_coordinates x
    rw [Set.mem_setOf_eq] at hx
    rw [hx] at hn
    simp only [Set.mem_setOf_eq,actual_coordinate_action,point,PiLp.toLp_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    nlinarith
  · intro hy
    refine ⟨point (y 0/2) (-y 1),?_,?_⟩
    · rw [Set.mem_setOf_eq]
      have hn := norm_squared_coordinates (point (y 0/2) (-y 1))
      change (y 0)^2/4+(y 1)^2=1 at hy
      have hh : ‖point (y 0/2) (-y 1)‖^2=1 := by
        rw [hn]
        change (y 0/2)^2+(-y 1)^2=1
        convert hy using 1 <;> ring
      nlinarith [norm_nonneg (point (y 0/2) (-y 1))]
    · rw [actual_coordinate_action]
      ext i
      fin_cases i <;> simp [point] <;> ring

theorem actual_axis_stretches :
    applyMatrix sourceA (point 1 0)=point 2 0 ∧
    applyMatrix sourceA (point 0 1)=point 0 (-1) ∧
    ‖applyMatrix sourceA (point 1 0)‖=2 ∧
    ‖applyMatrix sourceA (point 0 1)‖=1 := by
  simp only [actual_coordinate_action,point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num [EuclideanSpace.norm_eq,Fin.sum_univ_succ]

end SafeLearning.CompleteFoundationsSVDModels
