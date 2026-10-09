import SafeLearning.CompleteFoundationsSpectralModels
import SafeLearning.CompleteFoundationsMatrixNormModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsStructuredModels

abbrev E := EuclideanSpace ℝ (Fin 2)
open SafeLearning.CompleteFoundationsSpectralModels (point applyMatrix matrix_coordinate_action norm_squared_coordinates inner_coordinate_formula general_real_skew_quadratic_zero)
open SafeLearning.CompleteFoundationsMatrixNormModels (diagonal_two_spectral_norm)

def reflection : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,-1]
def projection : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,0]
def quarterSkew : Matrix (Fin 2) (Fin 2) ℝ := !![0,-1;1,0]
def cayley {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1-A)*(1+A)⁻¹

theorem actual_reflection_orthogonal :
    reflection.transpose=reflection ∧ reflectionᵀ*reflection=1 ∧ reflection.det= -1 := by
  refine ⟨?_,?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [reflection,Matrix.diagonal]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [reflection,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]
  · norm_num [reflection,Matrix.det_fin_two,Matrix.diagonal]

theorem actual_reflection_action (x : E) : applyMatrix reflection x=point (x 0) (-x 1) := by
  rw [matrix_coordinate_action]
  ext i
  fin_cases i <;> simp [reflection,point,Matrix.diagonal]

theorem actual_reflection_preserves_every_norm (x : E) : ‖applyMatrix reflection x‖=‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [actual_reflection_action,norm_squared_coordinates,norm_squared_coordinates]
  simp [point]

theorem actual_reflection_source_values :
    applyMatrix reflection (point 3 4)=point 3 (-4) ∧
    ‖applyMatrix reflection (point 3 4)‖=5 ∧ ‖point 3 4‖=5 := by
  have hn : ‖point 3 4‖=5 := by
    have hs := norm_squared_coordinates (point 3 4)
    change ‖point 3 4‖^2=3^2+4^2 at hs
    nlinarith [norm_nonneg (point 3 4)]
  refine ⟨?_,?_,hn⟩
  · simpa [point] using actual_reflection_action (point 3 4)
  · rw [actual_reflection_preserves_every_norm,hn]

theorem actual_projection_properties :
    projection.transpose=projection ∧ projection*projection=projection ∧
    projectionᵀ*projection=projection ∧ projection≠1 ∧ projection.det=0 ∧ ‖projection‖=1 := by
  have hsym : projection.transpose=projection := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [projection,Matrix.diagonal]
  have hid : projection*projection=projection := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [projection,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal]
  refine ⟨hsym,hid,by rw [hsym,hid],?_,?_,?_⟩
  · intro h
    have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 1 1) h
    norm_num [projection,Matrix.diagonal] at h11
  · norm_num [projection,Matrix.det_fin_two,Matrix.diagonal]
  · rw [projection,diagonal_two_spectral_norm]
    norm_num

theorem actual_projection_action (x : E) : applyMatrix projection x=point (x 0) 0 := by
  rw [matrix_coordinate_action]
  ext i
  fin_cases i <;> simp [projection,point,Matrix.diagonal]

theorem actual_projection_residual (x : E) :
    x-applyMatrix projection x=point 0 (x 1) ∧
    inner ℝ (applyMatrix projection x) (x-applyMatrix projection x)=0 ∧
    ‖x‖^2=‖applyMatrix projection x‖^2+‖x-applyMatrix projection x‖^2 := by
  have hr : x-applyMatrix projection x=point 0 (x 1) := by
    rw [actual_projection_action]
    ext i
    fin_cases i <;> simp [point]
  refine ⟨hr,?_,?_⟩
  · rw [hr,actual_projection_action,inner_coordinate_formula]
    simp [point]
  · rw [hr,actual_projection_action,norm_squared_coordinates,norm_squared_coordinates,norm_squared_coordinates]
    simp [point]

theorem actual_projection_image :
    Set.range (applyMatrix projection)={y : E | y 1=0} := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    simp [actual_projection_action,point]
  · intro hy
    change y 1=0 at hy
    refine ⟨y,?_⟩
    rw [actual_projection_action]
    ext i
    fin_cases i <;> simp [point,hy]

theorem actual_projection_is_unique_closest (x y : E) (hy : y 1=0) :
    ‖x-applyMatrix projection x‖ ≤ ‖x-y‖ ∧
    (‖x-y‖=‖x-applyMatrix projection x‖ ↔ y=applyMatrix projection x) := by
  have hr := (actual_projection_residual x).1
  have hn : ‖x-y‖^2=(x 0-y 0)^2+(x 1)^2 := by
    rw [norm_squared_coordinates]
    simp [hy]
  have hp : ‖x-applyMatrix projection x‖^2=(x 1)^2 := by
    rw [hr,norm_squared_coordinates]
    simp [point]
  constructor
  · nlinarith [sq_nonneg (x 0-y 0),norm_nonneg (x-y),norm_nonneg (x-applyMatrix projection x)]
  · constructor
    · intro h
      have hc : y 0=x 0 := by rw [h,hp] at hn;nlinarith [hn]
      rw [actual_projection_action]
      ext i
      fin_cases i <;> simp [point,hy,hc]
    · intro h
      rw [h]

theorem actual_projection_source_values :
    applyMatrix projection (point 3 4)=point 3 0 ∧
    point 3 4-applyMatrix projection (point 3 4)=point 0 4 ∧
    ‖applyMatrix projection (point 3 4)‖=3 ∧
    ‖point 3 4-applyMatrix projection (point 3 4)‖=4 ∧
    ‖point 3 4‖=5 := by
  have hr := (actual_projection_residual (point 3 4)).1
  have hr' : point 3 4-applyMatrix projection (point 3 4)=point 0 4 := by
    simpa [point] using hr
  rw [hr',actual_projection_action]
  norm_num [point,EuclideanSpace.norm_eq,Fin.sum_univ_succ]

theorem actual_skew_one_add_is_invertible {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.transpose= -A) : IsUnit (1+A) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  have hz : (1+A) *ᵥ (x-y)=0 := by rw [Matrix.mulVec_sub,h,sub_self]
  have hh := congrArg (fun w : n → ℝ => (x-y) ⬝ᵥ w) hz
  rw [Matrix.add_mulVec,Matrix.one_mulVec,dotProduct_add,
    general_real_skew_quadratic_zero A hA (x-y),dotProduct_zero,add_zero] at hh
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hh)

theorem actual_cayley_no_negative_one_eigenvector {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.transpose= -A) (v : n → ℝ)
    (hv : cayley A *ᵥ v= -v) : v=0 := by
  have hu := actual_skew_one_add_is_invertible A hA
  have hd := (Matrix.isUnit_iff_isUnit_det (1+A)).mp hu
  let w : n → ℝ := (1+A)⁻¹ *ᵥ v
  have hw : (1+A) *ᵥ w=v := by
    change (1+A) *ᵥ ((1+A)⁻¹ *ᵥ v)=v
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hd,Matrix.one_mulVec]
  have he : (1-A) *ᵥ w= -((1+A) *ᵥ w) := by
    rw [hw]
    change (1-A) *ᵥ ((1+A)⁻¹ *ᵥ v)= -v
    simpa only [cayley,Matrix.mulVec_mulVec] using hv
  rw [Matrix.sub_mulVec,Matrix.add_mulVec,Matrix.one_mulVec] at he
  have hw0 : w=0 := by
    ext i
    have hi := congrFun he i
    simp at hi ⊢
    linarith
  rw [← hw,hw0,Matrix.mulVec_zero]

theorem actual_cayley_is_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.transpose= -A) : (cayley A)ᵀ*cayley A=1 := by
  have hp := (Matrix.isUnit_iff_isUnit_det (1+A)).mp (actual_skew_one_add_is_invertible A hA)
  have hm : IsUnit (1-A).det := by
    have hneg : (-A).transpose= -(-A) := by simp [hA]
    simpa [sub_eq_add_neg] using
      (Matrix.isUnit_iff_isUnit_det (1+(-A))).mp (actual_skew_one_add_is_invertible (-A) hneg)
  have hc : (1+A)*(1-A)=(1-A)*(1+A) := by noncomm_ring
  have ht : (1+A)ᵀ=1-A := by simp [Matrix.transpose_add,hA,sub_eq_add_neg]
  have hs : (1-A)ᵀ=1+A := by simp [Matrix.transpose_sub,hA]
  rw [cayley,Matrix.transpose_mul,Matrix.transpose_nonsing_inv,ht,hs]
  calc
    (1-A)⁻¹*(1+A)*((1-A)*(1+A)⁻¹)=
        (1-A)⁻¹*((1+A)*(1-A))*(1+A)⁻¹ := by simp [Matrix.mul_assoc]
    _=(1-A)⁻¹*((1-A)*(1+A))*(1+A)⁻¹ := by rw [hc]
    _=1 := by rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hm,Matrix.one_mul,Matrix.mul_nonsing_inv _ hp]

theorem actual_quarter_inverse :
    (1+quarterSkew)⁻¹=(1/2 : ℝ) • !![1,1;-1,1] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [quarterSkew,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]

theorem actual_quarter_cayley : cayley quarterSkew=!![0,1;-1,0] ∧
    (cayley quarterSkew)ᵀ*cayley quarterSkew=1 ∧ (cayley quarterSkew).det=1 := by
  have hq : cayley quarterSkew=!![0,1;-1,0] := by
    rw [cayley,actual_quarter_inverse]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [quarterSkew,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]
  refine ⟨hq,?_,?_⟩
  · rw [hq]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_succ]
  · rw [hq]
    norm_num [Matrix.det_fin_two]

theorem actual_clockwise_quarter_action (x : E) : applyMatrix (cayley quarterSkew) x=point (x 1) (-x 0) := by
  rw [actual_quarter_cayley.1,matrix_coordinate_action]
  ext i
  fin_cases i <;> simp [point]

theorem actual_negative_identity_is_orthogonal {n : Type*} [Fintype n] [DecidableEq n] :
    (-1 : Matrix n n ℝ)ᵀ*(-1)=1 := by simp

theorem actual_negative_identity_is_excluded {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.transpose= -A) : cayley A≠ -1 := by
  classical
  intro h
  let i : n := Classical.arbitrary n
  let v : n → ℝ := Pi.single i 1
  have hz : v=0 := actual_cayley_no_negative_one_eigenvector A hA v (by
    rw [h]
    change (- (1 : Matrix n n ℝ)) *ᵥ v= -v
    rw [Matrix.neg_mulVec,Matrix.one_mulVec])
  have hi := congrFun hz i
  simp [v] at hi

end SafeLearning.CompleteFoundationsStructuredModels
