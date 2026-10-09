import SafeLearning.CompleteModulesLipSDPProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteModulesLipSDPWalkthrough

open CompleteModulesLipSDP CompleteModulesLipSDPNetwork CompleteModulesLipSDPProduct

theorem actual_spectral_norm_le_of_quadratic_bound {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] (weight : Matrix K I ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hbound : ∀ input : I → ℝ,
      (∑ k, ((weight *ᵥ input) k)^2) ≤ rho*(∑ i, (input i)^2)) :
    ‖weight‖ ≤ Real.sqrt rho := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg rho)
  intro input
  change ‖WithLp.toLp 2 (weight *ᵥ input)‖ ≤ Real.sqrt rho*‖input‖
  have h := hbound input
  rw [← squared_norm_of_coordinates,← squared_norm_of_coordinates] at h
  change ‖WithLp.toLp 2 (weight *ᵥ input)‖^2 ≤ rho*‖input‖^2 at h
  have hs : (Real.sqrt rho*‖input‖)^2=rho*‖input‖^2 := by
    rw [mul_pow,Real.sq_sqrt hrho]
  nlinarith [Real.sq_sqrt hrho,Real.sqrt_nonneg rho,
    norm_nonneg input,norm_nonneg (WithLp.toLp 2 (weight *ᵥ input)),
    mul_nonneg (Real.sqrt_nonneg rho) (norm_nonneg input)]

def walkthroughFirst : Matrix (Fin 2) (Fin 2) ℝ := !![1,2;1,-2]
def walkthroughLast : Matrix (Fin 1) (Fin 2) ℝ := fun _ => ![1,1]

theorem walkthrough_first_coordinate_energy (input : Fin 2 → ℝ) :
    (∑ k, ((walkthroughFirst *ᵥ input) k)^2)=2*(input 0)^2+8*(input 1)^2 := by
  simp [walkthroughFirst,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem walkthrough_last_coordinate_energy (input : Fin 2 → ℝ) :
    (∑ k, ((walkthroughLast *ᵥ input) k)^2)=(input 0+input 1)^2 := by
  simp [walkthroughLast,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem walkthrough_first_actual_spectral_norm_squared : ‖walkthroughFirst‖^2=8 := by
  have hu : ‖walkthroughFirst‖ ≤ Real.sqrt 8 := by
    apply actual_spectral_norm_le_of_quadratic_bound _ _ (by norm_num)
    intro input
    rw [walkthrough_first_coordinate_energy]
    simp only [Fin.sum_univ_two]
    nlinarith [sq_nonneg (input 0)]
  have hl := actual_spectral_matrix_gain walkthroughFirst (![0,1] : Fin 2 → ℝ)
  have hi : ‖WithLp.toLp 2 (![0,1] : Fin 2 → ℝ)‖^2=1 := by
    rw [squared_norm_of_coordinates]
    norm_num [Fin.sum_univ_two]
  have ho : ‖WithLp.toLp 2 (walkthroughFirst *ᵥ (![0,1] : Fin 2 → ℝ))‖^2=8 := by
    rw [squared_norm_of_coordinates,walkthrough_first_coordinate_energy]
    norm_num
  nlinarith [norm_nonneg walkthroughFirst,Real.sq_sqrt (show (0:ℝ) ≤ 8 by norm_num),
    Real.sqrt_nonneg 8,norm_nonneg (WithLp.toLp 2 (![0,1] : Fin 2 → ℝ)),
    norm_nonneg (WithLp.toLp 2 (walkthroughFirst *ᵥ (![0,1] : Fin 2 → ℝ)))]

theorem walkthrough_last_actual_spectral_norm_squared : ‖walkthroughLast‖^2=2 := by
  have hu : ‖walkthroughLast‖ ≤ Real.sqrt 2 := by
    apply actual_spectral_norm_le_of_quadratic_bound _ _ (by norm_num)
    intro input
    rw [walkthrough_last_coordinate_energy]
    simp only [Fin.sum_univ_two]
    nlinarith [sq_nonneg (input 0-input 1)]
  have hl := actual_spectral_matrix_gain walkthroughLast (![1,1] : Fin 2 → ℝ)
  have hi : ‖WithLp.toLp 2 (![1,1] : Fin 2 → ℝ)‖^2=2 := by
    rw [squared_norm_of_coordinates]
    norm_num [Fin.sum_univ_two]
  have ho : ‖WithLp.toLp 2 (walkthroughLast *ᵥ (![1,1] : Fin 2 → ℝ))‖^2=4 := by
    rw [squared_norm_of_coordinates,walkthrough_last_coordinate_energy]
    norm_num
  have hp : 0 ≤ ‖walkthroughLast‖*‖WithLp.toLp 2 (![1,1] : Fin 2 → ℝ)‖ := by positivity
  have hsq : ‖WithLp.toLp 2 (walkthroughLast *ᵥ (![1,1] : Fin 2 → ℝ))‖^2 ≤
      ‖walkthroughLast‖^2*‖WithLp.toLp 2 (![1,1] : Fin 2 → ℝ)‖^2 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (walkthroughLast *ᵥ (![1,1] : Fin 2 → ℝ)))]
  nlinarith [norm_nonneg walkthroughLast,Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
    Real.sqrt_nonneg 2]

theorem walkthrough_product_feasible_point :
    (-(blockCertificate walkthroughFirst walkthroughLast 0 1 16 (fun _ => 2))).PosSemidef := by
  have h := product_bound_is_actual_lipsdp_feasible walkthroughFirst walkthroughLast
  simpa only [walkthrough_first_actual_spectral_norm_squared,
    walkthrough_last_actual_spectral_norm_squared,show (2:ℝ)*8=16 by norm_num] using h

theorem walkthrough_product_gain_is_four : ‖walkthroughLast‖*‖walkthroughFirst‖=4 := by
  have hfirst := walkthrough_first_actual_spectral_norm_squared
  have hlast := walkthrough_last_actual_spectral_norm_squared
  have hprod : 0 ≤ ‖walkthroughLast‖*‖walkthroughFirst‖ := by positivity
  have hs : (‖walkthroughLast‖*‖walkthroughFirst‖)^2=16 := by
    rw [mul_pow,hfirst,hlast]
    norm_num
  nlinarith

theorem walkthrough_optimal_layer_gain_le_four :
    Real.sqrt (optimalLayerRho walkthroughFirst walkthroughLast) ≤ 4 := by
  have h := actual_layer_optimization_never_exceeds_product walkthroughFirst walkthroughLast
  rwa [walkthrough_product_gain_is_four] at h

end SafeLearning.CompleteModulesLipSDPWalkthrough
