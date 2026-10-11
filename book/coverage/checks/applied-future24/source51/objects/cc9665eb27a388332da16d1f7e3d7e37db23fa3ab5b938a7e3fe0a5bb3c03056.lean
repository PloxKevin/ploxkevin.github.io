import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedCoordinateTransfer

def A : Matrix (Fin 2) (Fin 2) ℝ := !![-1,0;0,-2]
def B : Fin 2→ℝ := ![1,1]
def C : Matrix (Fin 1) (Fin 2) ℝ := fun _ => ![1,1]
def T : Matrix (Fin 2) (Fin 2) ℝ := !![2,0;0,1]
def TInverse : Matrix (Fin 2) (Fin 2) ℝ := !![1/2,0;0,1]
def Az : Matrix (Fin 2) (Fin 2) ℝ := T*A*T⁻¹
def Bz : Fin 2→ℝ := T *ᵥ B
def Cz : Matrix (Fin 1) (Fin 2) ℝ := C*T⁻¹

theorem actual_transform_inverse_and_invertibility :
    T*TInverse=1 ∧ TInverse*T=1 ∧ T⁻¹=TInverse ∧ IsUnit T := by
  have h : T*TInverse=1 := by
    ext i j;fin_cases i <;> fin_cases j <;>
      norm_num [T,TInverse,Matrix.mul_apply,Fin.sum_univ_two]
  have hi : TInverse*T=1 := by
    ext i j;fin_cases i <;> fin_cases j <;>
      norm_num [T,TInverse,Matrix.mul_apply,Fin.sum_univ_two]
  have hu : IsUnit T := by
    rw [Matrix.isUnit_iff_isUnit_det]
    norm_num [T,Matrix.det_fin_two]
  exact ⟨h,hi,Matrix.inv_eq_right_inv h,hu⟩

theorem actual_transformed_matrices :
    Az=A ∧ Bz=![2,1] ∧ Cz=(fun _ : Fin 1=>![(1/2:ℝ),1]) := by
  have hi := actual_transform_inverse_and_invertibility.2.2.1
  constructor
  · unfold Az;rw [hi]
    ext i j;fin_cases i <;> fin_cases j <;>
      norm_num [A,T,TInverse,Matrix.mul_apply,Fin.sum_univ_two]
  constructor
  · ext i;fin_cases i <;> norm_num [Bz,T,B,dotProduct,Fin.sum_univ_two]
  · unfold Cz;rw [hi]
    ext i j;fin_cases i <;> fin_cases j <;>
      norm_num [C,TInverse,Matrix.mul_apply,Fin.sum_univ_two]

def complexA : Matrix (Fin 2) (Fin 2) ℂ := A.map Complex.ofReal
def resolventMatrix (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := s • 1-complexA
def resolventCandidate (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1/(s+1),0;0,1/(s+2)]

theorem actual_resolvent_inverse (s : ℂ) (h1 : s+1≠0) (h2 : s+2≠0) :
    (resolventMatrix s)⁻¹=resolventCandidate s := by
  apply Matrix.inv_eq_right_inv
  ext i j;fin_cases i <;> fin_cases j <;>
    simp [resolventMatrix,resolventCandidate,complexA,A,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp

def originalTransfer (s : ℂ) : ℂ :=
  dotProduct (fun i=>Complex.ofReal (C 0 i))
    ((resolventMatrix s)⁻¹ *ᵥ (fun i=>Complex.ofReal (B i)))
def transformedTransfer (s : ℂ) : ℂ :=
  dotProduct (fun i=>Complex.ofReal (Cz 0 i))
    ((s • 1-Az.map Complex.ofReal)⁻¹ *ᵥ (fun i=>Complex.ofReal (Bz i)))

theorem actual_original_transfer_is_the_source_rational_map (s : ℂ)
    (h1 : s+1≠0) (h2 : s+2≠0) :
    originalTransfer s=1/(s+1)+1/(s+2) := by
  unfold originalTransfer
  rw [actual_resolvent_inverse s h1 h2]
  simp [C,B,resolventCandidate,dotProduct,Fin.sum_univ_two]

theorem actual_transformed_transfer_is_the_same_rational_map (s : ℂ)
    (h1 : s+1≠0) (h2 : s+2≠0) :
    transformedTransfer s=1/(s+1)+1/(s+2) ∧
      transformedTransfer s=originalTransfer s := by
  have h : transformedTransfer s=1/(s+1)+1/(s+2) := by
    unfold transformedTransfer
    rw [actual_transformed_matrices.1,actual_transformed_matrices.2.1,
      actual_transformed_matrices.2.2]
    change dotProduct (fun i=>Complex.ofReal (![(1/2:ℝ),1] i))
      ((resolventMatrix s)⁻¹ *ᵥ (fun i=>Complex.ofReal (![2,1] i)))= _
    rw [actual_resolvent_inverse s h1 h2]
    simp [resolventCandidate,dotProduct,Fin.sum_univ_two]
    ring
  exact ⟨h,h.trans (actual_original_transfer_is_the_source_rational_map s h1 h2).symm⟩

theorem actual_coordinate_change_and_physical_output (x : Fin 2→ℝ) :
    TInverse *ᵥ (T *ᵥ x)=x ∧
      C *ᵥ x=Cz *ᵥ (T *ᵥ x) := by
  constructor
  · rw [Matrix.mulVec_mulVec,actual_transform_inverse_and_invertibility.2.1]
    simp
  · rw [actual_transformed_matrices.2.2]
    ext i;fin_cases i
    simp [Matrix.mulVec,C,T,dotProduct,Fin.sum_univ_two]

theorem actual_arbitrary_input_transformed_differential_equations
    (x0 x1 u : ℝ→ℝ) (t : ℝ)
    (h0 : HasDerivAt x0 (-x0 t+u t) t)
    (h1 : HasDerivAt x1 (-2*x1 t+u t) t) :
    HasDerivAt (fun s=>2*x0 s) (-(2*x0 t)+2*u t) t ∧
      HasDerivAt x1 (-2*x1 t+u t) t ∧
      x0 t+x1 t=(1/2:ℝ)*(2*x0 t)+x1 t := by
  refine ⟨?_,h1,by ring⟩
  convert h0.const_mul 2 using 1 <;> ring

end SafeLearning.CompleteAppliedCoordinateTransfer
