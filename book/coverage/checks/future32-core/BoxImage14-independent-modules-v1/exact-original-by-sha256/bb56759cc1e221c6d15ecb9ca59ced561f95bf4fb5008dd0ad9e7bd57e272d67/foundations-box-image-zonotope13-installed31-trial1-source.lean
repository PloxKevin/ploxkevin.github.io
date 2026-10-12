import SafeLearning.CompleteModulesAffineIBP28
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Set MeasureTheory
open scoped BigOperators RealInnerProductSpace Pointwise
namespace SafeLearning.CompleteFoundationsBoxImageZonotope32
open CompleteModulesAffineIBP28
variable {m n : Type*} [Fintype n]

def uniformInputBox (epsilon : ℝ) : Set (n → ℝ) :=
  box (fun _ => -epsilon) (fun _ => epsilon)

def columnSegment (epsilon : ℝ) (w : m → ℝ) : Set (m → ℝ) :=
  {v | ∃ a : ℝ, -epsilon ≤ a ∧ a ≤ epsilon ∧ v=a • w}

def columnSegmentSum (epsilon : ℝ) (W : Matrix m n ℝ) : Set (m → ℝ) :=
  {y | ∃ v : n → (m → ℝ), (∀ j,v j∈columnSegment epsilon (fun i => W i j)) ∧ y=∑ j,v j}

def coordinateHalfWidths (epsilon : ℝ) (W : Matrix m n ℝ) : m → ℝ :=
  fun i => epsilon*(∑ j,|W i j|)

theorem actual_nonnegative_sup_norm_ball_is_the_uniform_input_box
    (epsilon : ℝ) (he : 0 ≤ epsilon) :
    {x : n → ℝ | ‖x‖ ≤ epsilon}=uniformInputBox epsilon := by
  ext x
  rw [Set.mem_setOf_eq,pi_norm_le_iff_of_nonneg he]
  simp only [uniformInputBox,box,Set.mem_setOf_eq,Real.norm_eq_abs,abs_le]

theorem actual_matrix_action_is_the_sum_of_its_scaled_column_vectors
    (W : Matrix m n ℝ) (x : n → ℝ) :
    W *ᵥ x=∑ j,x j • (fun i => W i j) := by
  ext i
  simp [Matrix.mulVec,dotProduct,Finset.sum_apply,mul_comm]

theorem actual_uniform_box_image_is_exactly_the_sum_of_all_column_segments
    (epsilon : ℝ) (W : Matrix m n ℝ) :
    W.mulVec '' uniformInputBox epsilon=columnSegmentSum epsilon W := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨fun j => x j • (fun i => W i j),?_,?_⟩
    · intro j
      exact ⟨x j,(hx j).1,(hx j).2,rfl⟩
    · exact actual_matrix_action_is_the_sum_of_its_scaled_column_vectors W x
  · rintro ⟨v,hv,hy⟩
    choose a ha using hv
    refine ⟨a,?_,?_⟩
    · intro j
      exact ⟨(ha j).1,(ha j).2.1⟩
    · rw [actual_matrix_action_is_the_sum_of_its_scaled_column_vectors,hy]
      apply Finset.sum_congr rfl
      intro j hj
      exact (ha j).2.2.symm

theorem actual_column_segment_sum_is_the_finite_Minkowski_sum
    (epsilon : ℝ) (W : Matrix m n ℝ) :
    columnSegmentSum epsilon W=∑ j,columnSegment epsilon (fun i => W i j) := by
  ext y
  simp only [columnSegmentSum,Set.mem_setOf_eq,Set.mem_fintype_sum]
  constructor
  · rintro ⟨v,hv,he⟩
    exact ⟨v,hv,he.symm⟩
  · rintro ⟨v,hv,he⟩
    exact ⟨v,hv,he.symm⟩

theorem actual_nonnegative_column_segment_is_epsilon_times_the_unit_segment
    (epsilon : ℝ) (he : 0 ≤ epsilon) (w : m → ℝ) :
    columnSegment epsilon w=(fun v : m → ℝ => epsilon • v) '' columnSegment 1 w := by
  ext y
  constructor
  · rintro ⟨a,hal,hah,rfl⟩
    by_cases hz : epsilon=0
    · have ha : a=0 := by rw [hz] at hal hah;linarith
      refine ⟨0,⟨0,by norm_num,by norm_num,by simp⟩,?_⟩
      simp [hz,ha]
    · have hp : 0 < epsilon := lt_of_le_of_ne he (Ne.symm hz)
      have hl : -1 ≤ a/epsilon := by
        apply (le_div_iff₀ hp).mpr
        simpa using hal
      have hh : a/epsilon ≤ 1 := by
        apply (div_le_iff₀ hp).mpr
        simpa using hah
      refine ⟨(a/epsilon) • w,⟨a/epsilon,hl,hh,rfl⟩,?_⟩
      rw [smul_smul]
      congr 1
      field_simp
  · rintro ⟨v,⟨a,hal,hah,rfl⟩,rfl⟩
    refine ⟨epsilon*a,?_,?_,?_⟩
    · have h:=mul_le_mul_of_nonneg_left hal he
      nlinarith
    · simpa using mul_le_mul_of_nonneg_left hah he
    · rw [smul_smul]

theorem actual_uniform_box_has_attained_exact_coordinate_half_widths
    (epsilon : ℝ) (he : 0 ≤ epsilon) (W : Matrix m n ℝ) (i : m) :
    IsGreatest {t : ℝ | ∃ x∈uniformInputBox epsilon,t=(W *ᵥ x) i}
      (coordinateHalfWidths epsilon W i) ∧
    IsLeast {t : ℝ | ∃ x∈uniformInputBox epsilon,t=(W *ᵥ x) i}
      (-coordinateHalfWidths epsilon W i) := by
  have hc : center (fun _ : n => -epsilon) (fun _ => epsilon)=0 := by
    ext j
    dsimp [center]
    ring
  have hr : radius (fun _ : n => -epsilon) (fun _ => epsilon)=(fun _ => epsilon) := by
    ext j
    dsimp [radius]
    ring
  have ho : outputRadius W (fun _ => -epsilon) (fun _ => epsilon)=coordinateHalfWidths epsilon W := by
    ext k
    simp only [outputRadius,hr,coordinateHalfWidths,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h:=actual_finite_matrix_attained_coordinate_extrema W 0
    (fun _ => -epsilon) (fun _ => epsilon) (fun _ => by linarith) i
  rw [hc,ho] at h
  simpa only [affine,uniformInputBox,Pi.add_apply,Pi.zero_apply,
    Matrix.mulVec_zero,add_zero,zero_add,zero_sub] using h

theorem actual_uniform_box_half_width_is_epsilon_times_the_row_one_norm
    (epsilon : ℝ) (W : Matrix m n ℝ) (i : m) :
    coordinateHalfWidths epsilon W i=epsilon*‖(WithLp.toLp 1 (W i) : PiLp 1 (fun _ : n => ℝ))‖ := by
  rw [PiLp.norm_eq_of_L1]
  simp only [coordinateHalfWidths,Real.norm_eq_abs]

theorem actual_tightest_axis_aligned_enclosing_box_has_exact_printed_half_widths
    (epsilon : ℝ) (he : 0 ≤ epsilon) (W : Matrix m n ℝ) (lo hi : m → ℝ) :
    W.mulVec '' uniformInputBox epsilon ⊆ box lo hi ↔
      ∀ i,lo i ≤ -coordinateHalfWidths epsilon W i ∧ coordinateHalfWidths epsilon W i ≤ hi i := by
  constructor
  · intro h i
    have hExt:=actual_uniform_box_has_attained_exact_coordinate_half_widths epsilon he W i
    rcases hExt.1.1 with ⟨x,hx,heq⟩
    rcases hExt.2.1 with ⟨z,hz,hzeq⟩
    have hu:=(h ⟨x,hx,rfl⟩ i).2
    have hl:=(h ⟨z,hz,rfl⟩ i).1
    rw [←heq] at hu
    rw [←hzeq] at hl
    exact ⟨hl,hu⟩
  · intro h y
    rintro ⟨x,hx,rfl⟩ i
    have hExt:=actual_uniform_box_has_attained_exact_coordinate_half_widths epsilon he W i
    exact ⟨(h i).1.trans (hExt.2.2 ⟨x,hx,rfl⟩),
      (hExt.1.2 ⟨x,hx,rfl⟩).trans (h i).2⟩

theorem actual_invertible_two_by_two_box_image_has_two_independent_generators
    (epsilon : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) (hW : W.det≠0) :
    LinearIndependent ℝ (fun j : Fin 2 => fun i : Fin 2 => W i j) ∧
    W.mulVec '' uniformInputBox epsilon=
      {z | ∃ a b : ℝ, (-epsilon ≤ a ∧ a ≤ epsilon) ∧ (-epsilon ≤ b ∧ b ≤ epsilon) ∧
        z=a • (fun i => W i 0)+b • (fun i => W i 1)} := by
  constructor
  · exact Matrix.linearIndependent_cols_of_det_ne_zero hW
  · ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x 0,x 1,hx 0,hx 1,?_⟩
      rw [actual_matrix_action_is_the_sum_of_its_scaled_column_vectors,Fin.sum_univ_two]
    · rintro ⟨a,b,ha,hb,rfl⟩
      refine ⟨![a,b],?_,?_⟩
      · intro j
        fin_cases j
        · exact ha
        · exact hb
      · rw [actual_matrix_action_is_the_sum_of_its_scaled_column_vectors,Fin.sum_univ_two]
        rfl

theorem actual_positive_radius_invertible_parallelogram_generators_remain_independent
    (epsilon : ℝ) (he : 0 < epsilon) (W : Matrix (Fin 2) (Fin 2) ℝ) (hW : W.det≠0) :
    LinearIndependent ℝ (fun j : Fin 2 => epsilon • (fun i : Fin 2 => W i j)) := by
  have hd : (epsilon • W).det≠0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ he.ne') hW
  exact Matrix.linearIndependent_cols_of_det_ne_zero hd

theorem actual_running_box_map_is_a_scaled_Euclidean_isometry
    (x : Fin 2 → ℝ) :
    ‖(WithLp.toLp 2 (W *ᵥ x) : EuclideanSpace ℝ (Fin 2))‖^2=
      2*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 2))‖^2 := by
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,actual_source_matrix_coordinate_action]
  simp only [Fin.sum_univ_two,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Real.norm_eq_abs,sq_abs]
  ring

theorem actual_running_full_box_image_is_the_printed_square_with_exact_areas :
    W.mulVec '' uniformInputBox 1={z : Fin 2 → ℝ | |z 0|+|z 1|≤2} ∧
      W *ᵥ (![1,1] : Fin 2 → ℝ)=![2,0] ∧
      W *ᵥ (![-1,-1] : Fin 2 → ℝ)=![-2,0] ∧
      W *ᵥ (![1,-1] : Fin 2 → ℝ)=![0,2] ∧
      W *ᵥ (![-1,1] : Fin 2 → ℝ)=![0,-2] ∧
      volume (W.mulVec '' uniformInputBox 1)=8 ∧
      volume (box (fun _ : Fin 2 => -2) (fun _ => 2))=16 := by
  have he : W.mulVec '' uniformInputBox 1=trueImage := rfl
  rw [he]
  refine ⟨actual_source_true_image_is_diamond,actual_source_four_vertex_images.1,
    actual_source_four_vertex_images.2.1,actual_source_four_vertex_images.2.2.1,
    actual_source_four_vertex_images.2.2.2,actual_source_ibp_area_is_twice_true_image_area.2.1,
    actual_source_square_volumes.2⟩

theorem actual_negative_radius_ball_cannot_be_a_nonempty_scaled_segment :
    ((fun x : Fin 1 → ℝ => x) '' {x : Fin 1 → ℝ | ‖x‖ ≤ (-1:ℝ)})=∅ ∧
      ((fun t : ℝ => (-1:ℝ)*t) '' Icc (-1:ℝ) 1).Nonempty := by
  constructor
  · ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have h:=norm_nonneg x
      change False
      nlinarith
    · intro h
      exact False.elim h
  · exact ⟨0,⟨0,⟨by norm_num,by norm_num⟩,by norm_num⟩⟩

end SafeLearning.CompleteFoundationsBoxImageZonotope32
