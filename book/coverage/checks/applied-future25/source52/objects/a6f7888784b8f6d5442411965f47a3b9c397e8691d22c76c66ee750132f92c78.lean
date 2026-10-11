import SafeLearning.CompleteModulesLandscapeRobustRadius
import SafeLearning.CompleteModulesLipSDPProduct

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace SafeLearning.CompleteModulesLipSDPPracticeRadius21
open CompleteModulesLandscapeRobustRadius CompleteModulesGeneralMargin CompleteModulesLipSDP

def infinityRadius : ℝ := sourceRadius / Real.sqrt 3

theorem actual_three_coordinate_euclidean_norm_is_bounded_by_infinity_norm
    (x : Fin 3 → ℝ) :
    ‖WithLp.toLp 2 x‖ ≤ Real.sqrt 3 * ‖x‖ := by
  have h0 := norm_le_pi_norm x 0
  have h1 := norm_le_pi_norm x 1
  have h2 := norm_le_pi_norm x 2
  have hs : ‖WithLp.toLp 2 x‖^2 = (x 0)^2+(x 1)^2+(x 2)^2 := by
    rw [squared_norm_of_coordinates]
    simp [Fin.sum_univ_succ]
    ring
  have q0 : (x 0)^2 ≤ ‖x‖^2 := by simpa only [Real.norm_eq_abs,sq_abs] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h0
  have q1 : (x 1)^2 ≤ ‖x‖^2 := by simpa only [Real.norm_eq_abs,sq_abs] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h1
  have q2 : (x 2)^2 ≤ ‖x‖^2 := by simpa only [Real.norm_eq_abs,sq_abs] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h2
  have he : (Real.sqrt 3*‖x‖)^2=3*‖x‖^2 := by
    rw [mul_pow,Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg x))).mp
  rw [he]
  nlinarith

theorem actual_source_infinity_radius_exact_expression_and_rounding :
    infinityRadius = (0.6:ℝ)/(2*Real.sqrt 6) ∧
    |infinityRadius-(0.122474:ℝ)| < 0.0000005 ∧
    (0.6:ℝ)-(2*Real.sqrt 6)*infinityRadius=0 := by
  have p2 : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have p3 : 0<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have p6 : 0<Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hm : Real.sqrt 2*Real.sqrt 3=Real.sqrt 6 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤2)];norm_num
  have he : infinityRadius=(0.6:ℝ)/(2*Real.sqrt 6) := by
    unfold infinityRadius sourceRadius
    rw [div_div,←hm]
    ring
  have hl : (2.4494897:ℝ)<Real.sqrt 6 := by nlinarith [Real.sq_sqrt (show (0:ℝ)≤6 by norm_num)]
  have hu : Real.sqrt 6<(2.4494898:ℝ) := by nlinarith [Real.sq_sqrt (show (0:ℝ)≤6 by norm_num)]
  refine ⟨he,?_,?_⟩
  · rw [he,abs_lt]
    have hd : 0<(2:ℝ)*Real.sqrt 6 := by positivity
    have lo : (0.1224735:ℝ)<(0.6:ℝ)/(2*Real.sqrt 6) := by rw [lt_div_iff₀ hd];nlinarith
    have up : (0.6:ℝ)/(2*Real.sqrt 6)<(0.1224745:ℝ) := by rw [div_lt_iff₀ hd];nlinarith
    constructor <;> linarith
  · rw [he];field_simp;ring

theorem actual_strict_infinity_radius_certifies_every_source_logit_map
    {O : Type*} [Fintype O] [DecidableEq O]
    (logits : EuclideanSpace ℝ (Fin 3) → O → ℝ)
    (winner : O) (first second : EuclideanSpace ℝ (Fin 3))
    (hcompetitors : (Finset.univ.erase winner).Nonempty)
    (hmargin : actualLogitMargin logits winner first (Finset.univ.erase winner) hcompetitors=(0.6:ℝ))
    (hlogits : ∀ x y,‖WithLp.toLp 2 (logits x-logits y)‖ ≤ (2:ℝ)*‖x-y‖)
    (hdelta : ‖WithLp.ofLp (first-second)‖ < infinityRadius) :
    ∀ other,other≠winner → logits second other<logits second winner := by
  apply actual_source_margin_and_logit_lipschitz_bound_certify_every_small_perturbation logits winner first second hcompetitors hmargin
  · simpa only [dist_eq_norm] using hlogits
  · rw [dist_eq_norm]
    have hb := actual_three_coordinate_euclidean_norm_is_bounded_by_infinity_norm
      (WithLp.ofLp (first-second))
    have hs : 0<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have ht := mul_lt_mul_of_pos_left hdelta hs
    have he : Real.sqrt 3*infinityRadius=sourceRadius := by
      unfold infinityRadius;field_simp
    rw [he] at ht
    exact hb.trans_lt ht

def unitDirection : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun _ => 1/Real.sqrt 3)
def projection (x : EuclideanSpace ℝ (Fin 3)) : ℝ := ⟪unitDirection,x⟫_ℝ
def actualLogits (x : EuclideanSpace ℝ (Fin 3)) : Fin 2 → ℝ := linearLogits (projection x)
def boundaryPoint : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun _ => infinityRadius)

theorem actual_direction_has_unit_euclidean_norm : ‖unitDirection‖=1 := by
  have hs : ‖unitDirection‖^2=1 := by
    rw [squared_norm_of_coordinates]
    simp [unitDirection]
  nlinarith [norm_nonneg unitDirection]

theorem actual_three_dimensional_model_has_source_vector_gain_and_margin :
    (∀ x y,‖WithLp.toLp 2 (actualLogits x-actualLogits y)‖ ≤ (2:ℝ)*‖x-y‖) ∧
    actualLogits 0 0-actualLogits 0 1=(0.6:ℝ) := by
  constructor
  · intro x y
    unfold actualLogits
    rw [actual_linear_logit_displacement_has_exact_euclidean_gain]
    have hc := abs_real_inner_le_norm unitDirection (x-y)
    rw [actual_direction_has_unit_euclidean_norm,one_mul] at hc
    have he : projection x-projection y=⟪unitDirection,x-y⟫_ℝ := by simp [projection,inner_sub_right]
    rw [he]
    linarith
  · norm_num [actualLogits,projection,linearLogits]

theorem actual_source_boundary_in_both_norms_can_have_a_tie :
    ‖WithLp.ofLp boundaryPoint‖=infinityRadius ∧
    ‖boundaryPoint‖=sourceRadius ∧
    actualLogits boundaryPoint 0=actualLogits boundaryPoint 1 := by
  have p2 : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have p3 : 0<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have pr : 0<sourceRadius := by unfold sourceRadius;positivity
  have hposInf : 0 < infinityRadius := by unfold infinityRadius;positivity
  have hp : projection boundaryPoint=sourceRadius := by
    simp [projection,unitDirection,boundaryPoint,PiLp.inner_apply,RCLike.inner_apply,Fin.sum_univ_succ,infinityRadius]
    field_simp <;> nlinarith [Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)]
  refine ⟨?_,?_,?_⟩
  · simp [boundaryPoint,Real.norm_eq_abs,abs_of_pos hposInf]
  · have hs : ‖boundaryPoint‖^2=sourceRadius^2 := by
      rw [squared_norm_of_coordinates]
      simp [boundaryPoint,infinityRadius,Fin.sum_univ_succ]
      field_simp <;> nlinarith [Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)]
    nlinarith [norm_nonneg boundaryPoint]
  · unfold actualLogits
    rw [hp]
    exact actual_boundary_tie_and_label_change_outside_the_radius.1

end SafeLearning.CompleteModulesLipSDPPracticeRadius21
