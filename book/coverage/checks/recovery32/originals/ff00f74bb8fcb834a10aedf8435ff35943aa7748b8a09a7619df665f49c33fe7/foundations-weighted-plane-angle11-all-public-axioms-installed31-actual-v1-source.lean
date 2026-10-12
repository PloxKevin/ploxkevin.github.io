import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Set InnerProductGeometry
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsWeightedPlaneAngle32

abbrev Plane := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : Plane := WithLp.toLp 2 ![a,b]
def sourceX : Plane := point 1 2
def sourceY : Plane := point 3 (-1)
def sourceMetric : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1,4]
def sourceWeightedPoint (x : Plane) : Plane := point (x 0) (2*x 1)
def angleDegrees (x y : Plane) : ℝ := angle x y*180/Real.pi

theorem actual_plane_inner_product_coordinates (x y : Plane) :
    inner ℝ x y=x 0*y 0+x 1*y 1 := by
  simp [PiLp.inner_apply,Fin.sum_univ_succ]
  ring

theorem actual_plane_norm_coordinates (x : Plane) :
    ‖x‖=Real.sqrt ((x 0)^2+(x 1)^2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs]

theorem actual_printed_Euclidean_vectors_inner_product_and_lengths :
    inner ℝ sourceX sourceY=1 ∧ ‖sourceX‖=Real.sqrt 5 ∧ ‖sourceY‖=Real.sqrt 10 := by
  rw [actual_plane_inner_product_coordinates,actual_plane_norm_coordinates,actual_plane_norm_coordinates]
  norm_num [sourceX,sourceY,point]

theorem actual_alignment_identity_for_every_plane_pair (x y : Plane) :
    inner ℝ x y=‖x‖*‖y‖*Real.cos (angle x y) := by
  simpa [mul_comm,mul_left_comm,mul_assoc] using (cos_angle_mul_norm_mul_norm x y).symm

theorem actual_printed_Euclidean_angle_is_the_genuine_arccosine :
    angle sourceX sourceY=Real.arccos (1/Real.sqrt 50) := by
  unfold angle
  rw [actual_printed_Euclidean_vectors_inner_product_and_lengths.1,
    actual_printed_Euclidean_vectors_inner_product_and_lengths.2.1,
    actual_printed_Euclidean_vectors_inner_product_and_lengths.2.2]
  rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤5)]
  norm_num

private theorem exact_cosine_rational_enclosure :
    (7071/50000:ℝ)<1/Real.sqrt 50 ∧ 1/Real.sqrt 50<(14143/100000:ℝ) := by
  have hs : (Real.sqrt (50:ℝ))^2=50 := Real.sq_sqrt (by norm_num)
  have hp := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<50)
  have hl : (7071/1000:ℝ)<Real.sqrt 50 := by nlinarith [Real.sqrt_nonneg (50:ℝ)]
  have hu : Real.sqrt 50<(70711/10000:ℝ) := by nlinarith [Real.sqrt_nonneg (50:ℝ)]
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith
  · apply (div_lt_iff₀ hp).mpr
    nlinarith

private theorem exact_small_angle_sine_brackets :
    Real.sin (709/5000)<(7071/50000:ℝ) ∧
      (14143/100000:ℝ)<Real.sin (71/500) := by
  have hl:=Real.sin_bound (by norm_num : |(709/5000:ℝ)|≤1)
  have hu:=Real.sin_bound (by norm_num : |(71/500:ℝ)|≤1)
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<709/5000),
    abs_of_pos (by norm_num : (0:ℝ)<71/500)] at hl hu
  have hll:=(abs_le.mp hl).2
  have huu:=(abs_le.mp hu).1
  constructor <;> norm_num at * <;> linarith

private theorem genuine_arcsine_rational_enclosure :
    (709/5000:ℝ)<Real.arcsin (1/Real.sqrt 50) ∧
      Real.arcsin (1/Real.sqrt 50)<(71/500:ℝ) := by
  have he:=exact_cosine_rational_enclosure
  have hs:=exact_small_angle_sine_brackets
  have hpi:=Real.pi_gt_three
  constructor
  · have h:=Real.arcsin_lt_arcsin (Real.neg_one_le_sin (709/5000))
      (hs.1.trans he.1) (show 1/Real.sqrt 50≤(1:ℝ) by linarith [he.2])
    rw [Real.arcsin_sin (by linarith) (by linarith)] at h
    exact h
  · have h:=Real.arcsin_lt_arcsin (show (-1:ℝ)≤1/Real.sqrt 50 by linarith [he.1])
      (he.2.trans hs.2) (Real.sin_le_one (71/500))
    rw [Real.arcsin_sin (by linarith) (by linarith)] at h
    exact h

theorem actual_printed_Euclidean_angle_has_the_rigorous_one_decimal_degree_rounding :
    |angleDegrees sourceX sourceY-(819/10:ℝ)|<(1/20:ℝ) := by
  have hb:=genuine_arcsine_rational_enclosure
  have hpiL:=Real.pi_gt_d4
  have hpiU:=Real.pi_lt_d4
  have hpi:=Real.pi_pos
  unfold angleDegrees
  rw [actual_printed_Euclidean_angle_is_the_genuine_arccosine,Real.arccos]
  apply abs_lt.mpr
  constructor
  · have hl : (1637/20:ℝ)<(Real.pi/2-Real.arcsin (1/Real.sqrt 50))*180/Real.pi := by
      apply (lt_div_iff₀ hpi).mpr
      nlinarith [hb.2]
    linarith
  · have hu : (Real.pi/2-Real.arcsin (1/Real.sqrt 50))*180/Real.pi<(1639/20:ℝ) := by
      apply (div_lt_iff₀ hpi).mpr
      nlinarith [hb.1]
    linarith

theorem actual_diagonal_weighted_pairing_is_Euclidean_after_the_coordinate_scaling
    (x y : Plane) :
    (x : Fin 2 → ℝ) ⬝ᵥ (sourceMetric *ᵥ (y : Fin 2 → ℝ))=
      inner ℝ (sourceWeightedPoint x) (sourceWeightedPoint y) := by
  rw [actual_plane_inner_product_coordinates]
  simp [sourceMetric,sourceWeightedPoint,point,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_source_metric_is_positive_definite : sourceMetric.PosDef := by
  rw [sourceMetric,Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem actual_weighted_printed_vectors_inner_product_lengths_and_angle :
    inner ℝ (sourceWeightedPoint sourceX) (sourceWeightedPoint sourceY)= -5 ∧
      ‖sourceWeightedPoint sourceX‖=Real.sqrt 17 ∧
      ‖sourceWeightedPoint sourceY‖=Real.sqrt 13 ∧
      angle (sourceWeightedPoint sourceX) (sourceWeightedPoint sourceY)=
        Real.arccos ((-5)/Real.sqrt 221) := by
  have hi : inner ℝ (sourceWeightedPoint sourceX) (sourceWeightedPoint sourceY)= -5 := by
    rw [actual_plane_inner_product_coordinates]
    norm_num [sourceWeightedPoint,sourceX,sourceY,point]
  have hx : ‖sourceWeightedPoint sourceX‖=Real.sqrt 17 := by
    rw [actual_plane_norm_coordinates]
    norm_num [sourceWeightedPoint,sourceX,point]
  have hy : ‖sourceWeightedPoint sourceY‖=Real.sqrt 13 := by
    rw [actual_plane_norm_coordinates]
    norm_num [sourceWeightedPoint,sourceY,point]
  refine ⟨hi,hx,hy,?_⟩
  unfold angle
  rw [hi,hx,hy,←Real.sqrt_mul (by norm_num : (0:ℝ)≤17)]
  norm_num

theorem actual_weighted_angle_is_strictly_obtuse :
    Real.pi/2<angle (sourceWeightedPoint sourceX) (sourceWeightedPoint sourceY) ∧
      angle (sourceWeightedPoint sourceX) (sourceWeightedPoint sourceY)<Real.pi := by
  rw [actual_weighted_printed_vectors_inner_product_lengths_and_angle.2.2.2]
  have hs : (Real.sqrt (221:ℝ))^2=221 := Real.sq_sqrt (by norm_num)
  have hp:=Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<221)
  have hl : (5:ℝ)<Real.sqrt 221 := by nlinarith [Real.sqrt_nonneg (221:ℝ)]
  constructor
  · apply Real.pi_div_two_lt_arccos.mpr
    exact div_neg_of_neg_of_pos (by norm_num) hp
  · apply Real.arccos_lt_pi.mpr
    apply (lt_div_iff₀ hp).mpr
    linarith

theorem actual_weighting_changes_perpendicularity_and_length :
    inner ℝ sourceX (point (-2) 1)=0 ∧
      inner ℝ (sourceWeightedPoint sourceX) (sourceWeightedPoint (point (-2) 1))=6 ∧
      ‖sourceX‖<‖sourceWeightedPoint sourceX‖ := by
  refine ⟨?_,?_,?_⟩
  · rw [actual_plane_inner_product_coordinates]
    norm_num [sourceX,point]
  · rw [actual_plane_inner_product_coordinates]
    norm_num [sourceWeightedPoint,sourceX,point]
  · rw [actual_printed_Euclidean_vectors_inner_product_and_lengths.2.1,
      actual_weighted_printed_vectors_inner_product_lengths_and_angle.2.1]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

end SafeLearning.CompleteFoundationsWeightedPlaneAngle32

#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_plane_inner_product_coordinates
#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_plane_norm_coordinates
#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_printed_Euclidean_vectors_inner_product_and_lengths
#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_alignment_identity_for_every_plane_pair
#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_printed_Euclidean_angle_is_the_genuine_arccosine
#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_printed_Euclidean_angle_has_the_rigorous_one_decimal_degree_rounding
#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_diagonal_weighted_pairing_is_Euclidean_after_the_coordinate_scaling
#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_source_metric_is_positive_definite
#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_weighted_printed_vectors_inner_product_lengths_and_angle
#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_weighted_angle_is_strictly_obtuse
#print axioms SafeLearning.CompleteFoundationsWeightedPlaneAngle32.actual_weighting_changes_perpendicularity_and_length
