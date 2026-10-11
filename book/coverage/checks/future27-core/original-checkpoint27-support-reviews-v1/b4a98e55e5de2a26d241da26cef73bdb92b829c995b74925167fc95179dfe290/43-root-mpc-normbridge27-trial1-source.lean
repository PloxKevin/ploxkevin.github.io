import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace SafeLearning.CompleteCoreMPCNormBridge27

variable {I J : Type*} [Fintype I] [Fintype J]
attribute [local instance] Matrix.linftyOpNormedAddCommGroup

theorem actual_coordinate_infinity_norm_is_at_most_the_state_euclidean_norm
    (x : EuclideanSpace ℝ I) : ‖(fun i => x i)‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
  intro i
  exact PiLp.norm_apply_le x i

theorem actual_matrix_infinity_row_sum_bound_controls_euclidean_state_error
    (H : Matrix J I ℝ) (x : EuclideanSpace ℝ I) (j : J) :
    |(H *ᵥ (fun i => x i)) j| ≤ ‖H‖ * ‖x‖ := by
  calc
    |(H *ᵥ (fun i => x i)) j| ≤ ‖H *ᵥ (fun i => x i)‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (H *ᵥ (fun i => x i)) j
    _ ≤ ‖H‖ * ‖(fun i => x i)‖ := Matrix.linfty_opNorm_mulVec H _
    _ ≤ ‖H‖ * ‖x‖ := mul_le_mul_of_nonneg_left
      (actual_coordinate_infinity_norm_is_at_most_the_state_euclidean_norm x) (norm_nonneg H)

theorem actual_euclidean_feedback_deviation_implies_the_required_input_infinity_bound
    (u v : EuclideanSpace ℝ I) (k error : ℝ) (hbound : ‖u - v‖ ≤ k * error) :
    ‖(fun i => u i - v i)‖ ≤ k * error := by
  exact (actual_coordinate_infinity_norm_is_at_most_the_state_euclidean_norm (u-v)).trans hbound

theorem actual_polytopic_tightening_covers_a_euclidean_state_perturbation
    (H : Matrix J I ℝ) (z x : EuclideanSpace ℝ I) (radius margin : ℝ)
    (hnominal : ∀ j, (H *ᵥ (fun i => z i)) j ≤ 1-margin)
    (hdistance : ‖x-z‖ ≤ radius) (hmargin : ‖H‖ * radius ≤ margin) :
    ∀ j, (H *ᵥ (fun i => x i)) j ≤ 1 := by
  intro j
  have hb := actual_matrix_infinity_row_sum_bound_controls_euclidean_state_error H (x-z) j
  have hr : (H *ᵥ (fun i => x i-z i)) j ≤ margin := by
    calc
      (H *ᵥ (fun i => x i-z i)) j ≤ |(H *ᵥ (fun i => x i-z i)) j| := le_abs_self _
      _ ≤ ‖H‖ * ‖x-z‖ := hb
      _ ≤ ‖H‖ * radius := mul_le_mul_of_nonneg_left hdistance (norm_nonneg H)
      _ ≤ margin := hmargin
  have hlinear : (H *ᵥ (fun i => x i-z i)) j =
      (H *ᵥ (fun i => x i)) j - (H *ᵥ (fun i => z i)) j := by
    exact congrFun (Matrix.mulVec_sub H (fun i => x i) (fun i => z i)) j
  rw [hlinear] at hr
  linarith [hnominal j]

theorem actual_infinity_bounded_input_error_implies_the_euclidean_successor_radius
    {K : Type*} [Fintype K]
    (f : EuclideanSpace ℝ I → (K → ℝ) → EuclideanSpace ℝ I)
    (X : Set (EuclideanSpace ℝ I)) (U : Set (K → ℝ)) (lambda eta : ℝ)
    (hlambda : 0 ≤ lambda)
    (hLipschitz : ∀ x ∈ X, ∀ u ∈ U, ∀ d : K → ℝ, u+d ∈ U →
      ‖f x (u+d)-f x u‖ ≤ lambda * ‖d‖)
    (x : EuclideanSpace ℝ I) (u d : K → ℝ)
    (hx : x ∈ X) (hu : u ∈ U) (hud : u+d ∈ U) (hd : ‖d‖ ≤ eta) :
    ‖f x (u+d)-f x u‖ ≤ lambda * eta := by
  exact (hLipschitz x hx u hu d hud).trans (mul_le_mul_of_nonneg_left hd hlambda)

end SafeLearning.CompleteCoreMPCNormBridge27
