import SafeLearning.CompleteModulesGeneralMargin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeRobustRadius
open CompleteModulesGeneralMargin

def sourceRadius : ℝ := (0.6:ℝ)/(Real.sqrt 2*2)

theorem actual_source_radius_rounding_and_perturbation_tests :
    |sourceRadius-(0.212132:ℝ)|<0.0000005 ∧
    (0.2:ℝ)<sourceRadius ∧ sourceRadius<(0.22:ℝ) ∧
    (0.6:ℝ)-(Real.sqrt 2*2)*sourceRadius=0 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hp : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hl : (1.4142135:ℝ)<Real.sqrt 2 := by nlinarith
  have hu : Real.sqrt 2<(1.4142136:ℝ) := by nlinarith
  have hd : 0<Real.sqrt 2*2 := by positivity
  refine ⟨?_,?_,?_,?_⟩
  · rw [abs_lt]
    constructor
    · have h : (0.2121315:ℝ)<sourceRadius := by
        rw [sourceRadius,lt_div_iff₀ hd];nlinarith
      linarith
    · have h : sourceRadius<(0.2121325:ℝ) := by
        rw [sourceRadius,div_lt_iff₀ hd];nlinarith
      linarith
  · rw [sourceRadius,lt_div_iff₀ hd];nlinarith
  · rw [sourceRadius,div_lt_iff₀ hd];nlinarith
  · dsimp [sourceRadius]
    field_simp
    ring

/-- The theorem covers every perturbation with actual metric distance. Euclidean
input spaces have distance equal to the ordinary norm of their difference. -/
theorem actual_source_margin_and_logit_lipschitz_bound_certify_every_small_perturbation
    {O X : Type*} [Fintype O] [DecidableEq O] [PseudoMetricSpace X]
    (logits : X → O → ℝ) (winner : O) (first second : X)
    (hcompetitors : (Finset.univ.erase winner).Nonempty)
    (hmargin : actualLogitMargin logits winner first (Finset.univ.erase winner) hcompetitors=(0.6:ℝ))
    (hlogits : ∀ x y,‖WithLp.toLp 2 (logits x-logits y)‖ ≤ (2:ℝ)*dist x y)
    (hdistance : dist first second<sourceRadius) :
    ∀ other,other≠winner → logits second other<logits second winner := by
  apply actual_arbitrary_global_margin_radius_preserves_unique_prediction logits winner first second 2
    (by norm_num) hcompetitors hlogits
  simpa only [hmargin,sourceRadius] using hdistance

theorem actual_source_norm_point_two_is_certified
    {I O : Type*} [Fintype I] [Fintype O] [DecidableEq O]
    (logits : EuclideanSpace ℝ I → O → ℝ) (winner : O)
    (first second : EuclideanSpace ℝ I)
    (hcompetitors : (Finset.univ.erase winner).Nonempty)
    (hmargin : actualLogitMargin logits winner first (Finset.univ.erase winner) hcompetitors=(0.6:ℝ))
    (hlogits : ∀ x y,‖WithLp.toLp 2 (logits x-logits y)‖ ≤ (2:ℝ)*‖x-y‖)
    (hdistance : ‖first-second‖ ≤ (0.2:ℝ)) :
    ∀ other,other≠winner → logits second other<logits second winner := by
  apply actual_source_margin_and_logit_lipschitz_bound_certify_every_small_perturbation logits winner first second hcompetitors hmargin
  · simpa only [dist_eq_norm] using hlogits
  · rw [dist_eq_norm]
    exact hdistance.trans_lt actual_source_radius_rounding_and_perturbation_tests.2.1

def linearLogits (x : ℝ) : Fin 2 → ℝ := ![3/10-Real.sqrt 2*x,-3/10+Real.sqrt 2*x]
def constantLogits (_x : ℝ) : Fin 2 → ℝ := ![3/10,-3/10]

theorem actual_linear_logit_displacement_has_exact_euclidean_gain (x y : ℝ) :
    ‖WithLp.toLp 2 (linearLogits x-linearLogits y)‖=2*|x-y| := by
  let direction : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-Real.sqrt 2,Real.sqrt 2]
  have hs : ‖direction‖^2=4 := by
    rw [←real_inner_self_eq_norm_sq]
    change (∑ i : Fin 2,direction i*direction i)=4
    simp [direction,Fin.sum_univ_succ]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hn : ‖direction‖=2 := by nlinarith [norm_nonneg direction]
  have he : WithLp.toLp 2 (linearLogits x-linearLogits y)=(x-y) • direction := by
    ext i
    fin_cases i <;> simp [linearLogits,direction] <;> ring
  rw [he,norm_smul,hn,Real.norm_eq_abs]
  ring

theorem actual_linear_model_has_the_printed_vector_gain_and_margin :
    (∀ x y,‖WithLp.toLp 2 (linearLogits x-linearLogits y)‖ ≤ (2:ℝ)*dist x y) ∧
    linearLogits 0 0-linearLogits 0 1=(0.6:ℝ) := by
  constructor
  · intro x y;rw [actual_linear_logit_displacement_has_exact_euclidean_gain,Real.dist_eq]
  · norm_num [linearLogits]

theorem actual_boundary_tie_and_label_change_outside_the_radius :
    linearLogits sourceRadius 0=linearLogits sourceRadius 1 ∧
    linearLogits (0.22:ℝ) 0<linearLogits (0.22:ℝ) 1 := by
  have h := actual_source_radius_rounding_and_perturbation_tests.2.2.2
  constructor
  · simp [linearLogits]
    linarith
  · have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg (2:ℝ)
    have hl : (1.4:ℝ)<Real.sqrt 2 := by nlinarith
    simp [linearLogits]
    nlinarith

theorem actual_constant_model_with_same_gain_bound_and_margin_has_no_label_change :
    (∀ x y,‖WithLp.toLp 2 (constantLogits x-constantLogits y)‖ ≤ (2:ℝ)*dist x y) ∧
    constantLogits 0 0-constantLogits 0 1=(0.6:ℝ) ∧
    (∀ x,constantLogits x 1<constantLogits x 0) := by
  refine ⟨?_,by norm_num [constantLogits],?_⟩
  · intro x y
    have hz : constantLogits x-constantLogits y=0 := by simp [constantLogits]
    rw [hz]
    simp only [WithLp.toLp_zero,norm_zero]
    positivity
  · intro x;norm_num [constantLogits]

end SafeLearning.CompleteModulesLandscapeRobustRadius
