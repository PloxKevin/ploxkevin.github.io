import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Matrix MeasureTheory
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsEllipseGeometry
abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
def sourceP : Matrix (Fin 2) (Fin 2) ℝ := !![5,-4;-4,5]
def sourceR : Matrix (Fin 2) (Fin 2) ℝ := !![2/3,1/3;1/3,2/3]
def sourceInverse : Matrix (Fin 2) (Fin 2) ℝ := !![5/9,4/9;4/9,5/9]
def inverseR : Matrix (Fin 2) (Fin 2) ℝ := !![2,-1;-1,2]
def actualMap (A : Matrix (Fin 2) (Fin 2) ℝ) : E →L[ℝ] E := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A
def energy (x : E) : ℝ := (x : Fin 2 → ℝ) ⬝ᵥ (sourceP *ᵥ (x : Fin 2 → ℝ))
def actualEllipse : Set E := {x | energy x ≤ 1}
def qMinus : E := point (1/Real.sqrt 2) (-1/Real.sqrt 2)
def qPlus : E := point (1/Real.sqrt 2) (1/Real.sqrt 2)

theorem actual_coordinates (A : Matrix (Fin 2) (Fin 2) ℝ) (x : E) :
    actualMap A x = point (A 0 0*x 0+A 0 1*x 1) (A 1 0*x 0+A 1 1*x 1) := by
  ext i
  change (A *ᵥ (x : Fin 2 → ℝ)) i=(![A 0 0*x 0+A 0 1*x 1,A 1 0*x 0+A 1 1*x 1] : Fin 2 → ℝ) i
  fin_cases i <;> simp [mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_energy_coordinates (x : E) : energy x = 5*(x 0)^2-8*x 0*x 1+5*(x 1)^2 := by
  simp [energy,sourceP,mulVec,dotProduct,Fin.sum_univ_succ]; ring

theorem actual_norm_squared (x : E) : ‖x‖^2=(x 0)^2+(x 1)^2 := by
  rw [←real_inner_self_eq_norm_sq]
  change (∑ i : Fin 2,x i*x i)=(x 0)^2+(x 1)^2
  simp [Fin.sum_univ_succ]; ring

theorem actual_source_matrix_products : sourceP.det=9 ∧ sourceR.det=1/3 ∧
    sourceR*sourceR=sourceInverse ∧ sourceP*sourceInverse=1 ∧
    sourceR*inverseR=1 ∧ inverseR*sourceR=1 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · norm_num [sourceP,Matrix.det_fin_two]
  · norm_num [sourceR,Matrix.det_fin_two]
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [sourceP,sourceR,sourceInverse,inverseR,mul_apply,Fin.sum_univ_succ]

theorem actual_source_inverse_and_positive_square_root : sourceP⁻¹=sourceInverse ∧ sourceR.PosDef := by
  constructor
  · exact Matrix.inv_eq_right_inv actual_source_matrix_products.2.2.2.1
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j; fin_cases i <;> fin_cases j <;> norm_num [sourceR,Matrix.conjTranspose_apply]
    · intro x hx
      have hne : x 0≠0 ∨ x 1≠0 := by
        by_contra h; push Not at h; apply hx; ext i; fin_cases i <;> simp [h.1,h.2]
      have hnorm : 0<(x 0)^2+(x 1)^2 := by
        rcases hne with h|h <;> nlinarith [sq_pos_of_ne_zero h,sq_nonneg (x 0),sq_nonneg (x 1)]
      simp [sourceR,mulVec,dotProduct,Fin.sum_univ_succ]
      nlinarith [sq_nonneg (x 0+x 1)]

theorem actual_source_positive_definite : sourceP.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [sourceP,Matrix.conjTranspose_apply]
  · intro x hx
    have hne : x 0≠0 ∨ x 1≠0 := by
      by_contra h; push Not at h; apply hx; ext i; fin_cases i <;> simp [h.1,h.2]
    have hnorm : 0<(x 0)^2+(x 1)^2 := by
      rcases hne with h|h <;> nlinarith [sq_pos_of_ne_zero h,sq_nonneg (x 0),sq_nonneg (x 1)]
    simp [sourceP,mulVec,dotProduct,Fin.sum_univ_succ]
    nlinarith [sq_nonneg (x 0-x 1)]

theorem actual_shape_energy_identity (x : E) : energy (actualMap sourceR x)=‖x‖^2 ∧
    energy x=‖actualMap inverseR x‖^2 := by
  rw [actual_coordinates,actual_energy_coordinates,actual_norm_squared,actual_energy_coordinates,
    actual_coordinates,actual_norm_squared]
  simp [sourceR,inverseR,point]; constructor <;> ring

theorem actual_shape_image_of_unit_ball : actualEllipse = actualMap sourceR '' Metric.closedBall (0 : E) 1 := by
  ext x
  constructor
  · intro hx
    refine ⟨actualMap inverseR x,?_,?_⟩
    · simp only [Metric.mem_closedBall,dist_zero_right]
      have h := (actual_shape_energy_identity x).2
      change energy x≤1 at hx
      nlinarith [norm_nonneg (actualMap inverseR x)]
    · rw [actual_coordinates,actual_coordinates]
      ext i; fin_cases i <;> simp [sourceR,inverseR,point] <;> ring
  · rintro ⟨u,hu,rfl⟩
    change energy (actualMap sourceR u)≤1
    rw [(actual_shape_energy_identity u).1]
    simp only [Metric.mem_closedBall,dist_zero_right] at hu
    nlinarith [norm_nonneg u]

theorem actual_source_eigenvectors : actualMap sourceP qMinus=9 • qMinus ∧
    actualMap sourceP qPlus=qPlus := by
  rw [actual_coordinates,actual_coordinates]
  constructor <;> ext i <;> fin_cases i <;> simp [sourceP,qMinus,qPlus,point] <;> ring

theorem actual_unit_axes_and_orthogonality : ‖qMinus‖=1 ∧ ‖qPlus‖=1 ∧ inner ℝ qMinus qPlus=0 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (1/Real.sqrt 2 : ℝ)^2=1/2 := by rw [div_pow,one_pow,hs]
  have h1 : ‖qMinus‖^2=1 := by
    rw [actual_norm_squared]
    change (1/Real.sqrt 2)^2+(-1/Real.sqrt 2)^2=1
    rw [neg_div,neg_sq,hi]; norm_num
  have h2 : ‖qPlus‖^2=1 := by
    rw [actual_norm_squared]
    change (1/Real.sqrt 2)^2+(1/Real.sqrt 2)^2=1
    rw [hi]; norm_num
  refine ⟨?_,?_,?_⟩
  · nlinarith [norm_nonneg qMinus]
  · nlinarith [norm_nonneg qPlus]
  · simp [qMinus,qPlus,point,PiLp.inner_apply,Fin.sum_univ_succ]; ring

theorem actual_energy_along_axes (t : ℝ) : energy (t • qMinus)=9*t^2 ∧ energy (t • qPlus)=t^2 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hr : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [actual_energy_coordinates,actual_energy_coordinates]
  simp [qMinus,qPlus,point]; constructor <;> field_simp <;> nlinarith [hs]

theorem actual_axis_semilengths (t : ℝ) :
    (t • qMinus∈actualEllipse ↔ |t|≤1/3) ∧ (t • qPlus∈actualEllipse ↔ |t|≤1) := by
  change (energy (t • qMinus)≤1 ↔ |t|≤1/3) ∧ (energy (t • qPlus)≤1 ↔ |t|≤1)
  rw [(actual_energy_along_axes t).1,(actual_energy_along_axes t).2]
  constructor <;> constructor
  · intro h; rw [abs_le]; constructor <;> nlinarith
  · intro h; have hh := abs_le.mp h; nlinarith
  · intro h; rw [abs_le]; constructor <;> nlinarith
  · intro h; have hh := abs_le.mp h; nlinarith

theorem actual_norm_energy_gap (x : E) : energy x-‖x‖^2=4*(x 0-x 1)^2 := by
  rw [actual_energy_coordinates,actual_norm_squared]; ring

theorem actual_every_ellipse_point_has_distance_at_most_one (x : E) (hx : x∈actualEllipse) : ‖x‖≤1 := by
  have hg := actual_norm_energy_gap x
  change energy x≤1 at hx
  nlinarith [sq_nonneg (x 0-x 1),norm_nonneg x]

theorem actual_farthest_points_are_exactly_two_axes (x : E) :
    x∈actualEllipse ∧ ‖x‖=1 ↔ x=qPlus ∨ x= -qPlus := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (1/Real.sqrt 2 : ℝ)^2=1/2 := by rw [div_pow,one_pow,hs]
  constructor
  · rintro ⟨hx,hn⟩
    have hg := actual_norm_energy_gap x
    change energy x≤1 at hx
    have he : x 0=x 1 := by rw [hn] at hg; nlinarith [sq_nonneg (x 0-x 1)]
    have hn2 := actual_norm_squared x
    rw [hn,he] at hn2
    have hh : x 0=1/Real.sqrt 2 ∨ x 0= -(1/Real.sqrt 2) := by
      apply eq_or_eq_neg_of_sq_eq_sq
      rw [←he] at hn2
      nlinarith
    rcases hh with h|h
    · left; ext i; fin_cases i
      · change x 0=1/Real.sqrt 2; exact h
      · change x 1=1/Real.sqrt 2; exact he.symm.trans h
    · right; ext i; fin_cases i
      · change x 0= -(1/Real.sqrt 2); exact h
      · change x 1= -(1/Real.sqrt 2); exact he.symm.trans h
  · rintro (rfl|rfl)
    · refine ⟨?_,actual_unit_axes_and_orthogonality.2.1⟩
      have h := (actual_energy_along_axes 1).2
      simpa [actualEllipse] using h.le
    · refine ⟨?_,by simpa using actual_unit_axes_and_orthogonality.2.1⟩
      have h := (actual_energy_along_axes (-1)).2
      simpa [actualEllipse] using h.le

theorem actual_slice_half_width (t : ℝ) : point t 0∈actualEllipse ↔ |t|≤1/Real.sqrt 5 := by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hp : 0<1/Real.sqrt 5 := by positivity
  change energy (point t 0)≤1 ↔ _
  rw [actual_energy_coordinates]
  simp only [point,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,sub_zero]
  have hi : (1/Real.sqrt 5 : ℝ)^2=1/5 := by rw [div_pow,one_pow,hs]
  constructor
  · intro h
    apply abs_le_of_sq_le_sq (by nlinarith) hp.le
  · intro h
    have hh := sq_le_sq.mpr (show |t|≤|1/Real.sqrt 5| by simpa only [abs_of_nonneg hp.le] using h)
    nlinarith

theorem actual_shadow_projection_half_width (t : ℝ) :
    (∃ y : ℝ,point t y∈actualEllipse) ↔ |t|≤Real.sqrt (5/9) := by
  have hs : (Real.sqrt (5/9 : ℝ))^2=5/9 := Real.sq_sqrt (by norm_num)
  have hp : 0≤Real.sqrt (5/9 : ℝ) := Real.sqrt_nonneg _
  constructor
  · rintro ⟨y,hy⟩
    change energy (point t y)≤1 at hy
    rw [actual_energy_coordinates] at hy
    simp [point] at hy
    have hb : t^2≤5/9 := by nlinarith [sq_nonneg (y-(4/5)*t)]
    rw [abs_le]; constructor <;> nlinarith
  · intro ht
    have hh := abs_le.mp ht
    refine ⟨(4/5)*t,?_⟩
    change energy (point t ((4/5)*t))≤1
    rw [actual_energy_coordinates]
    simp [point]
    nlinarith

theorem actual_source_point_inside : energy (point (1/2) (1/2))=1/2 ∧ point (1/2) (1/2)∈actualEllipse := by
  have he : energy (point (1/2) (1/2))=1/2 := by norm_num [actual_energy_coordinates,point]
  exact ⟨he,by change energy _≤1;rw [he];norm_num⟩

theorem actual_shape_spectral_decomposition : sourceR=
    (1/3 : ℝ) • Matrix.vecMulVec (qMinus : Fin 2 → ℝ) (qMinus : Fin 2 → ℝ)+
    Matrix.vecMulVec (qPlus : Fin 2 → ℝ) (qPlus : Fin 2 → ℝ) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sourceR,qMinus,qPlus,point,Matrix.vecMulVec] <;> field_simp <;> nlinarith [hs]

theorem actual_ellipse_area : volume actualEllipse=ENNReal.ofReal (Real.pi/3) := by
  rw [actual_shape_image_of_unit_ball]
  have hd : LinearMap.det (actualMap sourceR : E →ₗ[ℝ] E)=1/3 := by
    change LinearMap.det (sourceR.toLpLin 2 2)=1/3
    rw [LinearMap.det_toLpLin,actual_source_matrix_products.2.1]
  rw [Measure.addHaar_image_continuousLinearMap,hd,EuclideanSpace.volume_closedBall_fin_two]
  norm_num
  rw [←ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring


theorem actual_all_characteristic_roots_and_smallest (lambda : ℝ) :
    (sourceP.charpoly.eval lambda=0 ↔ lambda=1 ∨ lambda=9) ∧
    IsLeast {root : ℝ | sourceP.charpoly.eval root=0} 1 := by
  have he (r : ℝ) : sourceP.charpoly.eval r=r^2-10*r+9 := by
    rw [Matrix.charpoly_fin_two]
    norm_num [sourceP,Matrix.det_fin_two,Matrix.trace,Fin.sum_univ_succ]
  have roots (r : ℝ) : sourceP.charpoly.eval r=0 ↔ r=1 ∨ r=9 := by
    rw [he]
    constructor
    · intro h
      have hz : (r-1)*(r-9)=0 := by nlinarith
      rcases mul_eq_zero.mp hz with h|h
      · left; linarith
      · right; linarith
    · rintro (rfl|rfl) <;> norm_num
  refine ⟨roots lambda,⟨(roots 1).mpr (Or.inl rfl),?_⟩⟩
  intro r hr
  rcases (roots r).mp hr with rfl|rfl <;> norm_num

theorem actual_source_area_formula_and_axis_distance :
    Real.pi/Real.sqrt sourceP.det=Real.pi/3 ∧
    (1/Real.sqrt 1 : ℝ)=1 := by
  rw [actual_source_matrix_products.1]
  norm_num

theorem actual_source_area_shadow_and_slice_roundings :
    |Real.pi/3-1047/1000|<1/2000 ∧
    |Real.sqrt (5/9 : ℝ)-745/1000|<1/2000 ∧
    |1/Real.sqrt 5-447/1000|<1/2000 ∧
    (1/Real.sqrt 5 : ℝ)<Real.sqrt (5/9) := by
  have hp := Real.pi_gt_d4
  have hq := Real.pi_lt_d4
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤5/9)
  have hsn := Real.sqrt_nonneg (5/9 : ℝ)
  have hi : (1/Real.sqrt 5 : ℝ)^2=1/5 := by
    rw [div_pow,one_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤5)]
  have hin : 0<(1/Real.sqrt 5 : ℝ) := by positivity
  refine ⟨?_,?_,?_,?_⟩
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> nlinarith
  · rw [abs_lt]; constructor <;> nlinarith
  · nlinarith

end SafeLearning.CompleteFoundationsEllipseGeometry
