import SafeLearning.CompleteBarrierVectorChainRule
import SafeLearning.CompleteBarrierNonlinearDomainComparison
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
namespace SafeLearning.CompleteModulesLandscapeControlAffineDomain
variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

theorem actual_control_affine_existing_trajectory_is_safe_for_a_proper_alpha_interval
    (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E) (u : E → U) (x : ℝ → E)
    (alpha : ℝ → ℝ) (J : Set ℝ) (D : Set E) (a b : ℝ)
    (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D) (hab : a≤b)
    (hm : MonotoneOn alpha J) (ha0 : alpha 0=0) (hJ0 : (0:ℝ)∈J)
    (hx : AbsolutelyContinuousOnInterval x a b) (hxD : MapsTo x (uIcc a b) D)
    (hhJ : MapsTo h D J)
    (hode : ∀ᵐt ∂volume, t∈Icc a b → HasDerivAt x (f (x t)+g (x t) (u (x t))) t)
    (hcbf : ∀z∈D, -alpha (h z)≤fderiv ℝ h z (f z)+fderiv ℝ h z (g z (u z)))
    (h0 : 0≤h (x a)) : ∀t∈Icc a b, 0≤h (x t) := by
  apply CompleteBarrierNonlinearDomainComparison.genuine_nonlinear_invariance
    (h ∘ x) (fun t => fderiv ℝ h (x t) (f (x t)+g (x t) (u (x t))))
    alpha J a b hab hm ha0
    (CompleteBarrierVectorChainRule.genuine_c1_ac_composition h x D a b hD hh hx hxD) hJ0
  · intro t ht
    exact hhJ (hxD (by simpa [uIcc_of_le hab] using ht))
  · exact CompleteBarrierVectorChainRule.genuine_ae_vector_chain_rule h x
      (fun t => f (x t)+g (x t) (u (x t))) D a b hD hh hab hxD hode
  · exact Eventually.of_forall fun t ht => by
      rw [map_add]
      exact hcbf (x t) (hxD (by simpa [uIcc_of_le hab] using ht))
  · exact h0

theorem actual_bounded_model_residual_has_the_true_Lie_derivative_error_bound
    (h : E → ℝ) (z d : E) (epsilon : ℝ) (hd : ‖d‖≤epsilon) :
    |fderiv ℝ h z d|≤‖fderiv ℝ h z‖*epsilon := by
  calc
    |fderiv ℝ h z d|=‖fderiv ℝ h z d‖ := (Real.norm_eq_abs _).symm
    _≤‖fderiv ℝ h z‖*‖d‖ := ContinuousLinearMap.le_opNorm _ _
    _≤‖fderiv ℝ h z‖*epsilon := mul_le_mul_of_nonneg_left hd (norm_nonneg _)

theorem actual_nominal_uncertainty_margin_implies_the_true_perturbed_barrier_inequality
    (h : E → ℝ) (z nominal residual : E) (alpha : ℝ → ℝ) (epsilon : ℝ)
    (hd : ‖residual‖≤epsilon)
    (hnom : -alpha (h z)+‖fderiv ℝ h z‖*epsilon≤fderiv ℝ h z nominal) :
    -alpha (h z)≤fderiv ℝ h z (nominal+residual) := by
  have he := actual_bounded_model_residual_has_the_true_Lie_derivative_error_bound h z residual epsilon hd
  have hlo := neg_le_of_abs_le he
  rw [map_add]
  linarith

theorem actual_robust_margin_protects_every_existing_perturbed_control_affine_trajectory
    (h : E → ℝ) (f residual : E → E) (g : E → U →L[ℝ] E) (u : E → U) (x : ℝ → E)
    (alpha epsilon : ℝ → ℝ) (J : Set ℝ) (D : Set E) (a b : ℝ)
    (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D) (hab : a≤b)
    (hm : MonotoneOn alpha J) (ha0 : alpha 0=0) (hJ0 : (0:ℝ)∈J)
    (hx : AbsolutelyContinuousOnInterval x a b) (hxD : MapsTo x (uIcc a b) D)
    (hhJ : MapsTo h D J)
    (hode : ∀ᵐt ∂volume, t∈Icc a b →
      HasDerivAt x ((f (x t)+residual (x t))+g (x t) (u (x t))) t)
    (herror : ∀z∈D, ‖residual z‖≤epsilon (h z))
    (hmargin : ∀z∈D, -alpha (h z)+‖fderiv ℝ h z‖*epsilon (h z)≤
      fderiv ℝ h z (f z)+fderiv ℝ h z (g z (u z)))
    (h0 : 0≤h (x a)) : ∀t∈Icc a b, 0≤h (x t) := by
  apply actual_control_affine_existing_trajectory_is_safe_for_a_proper_alpha_interval
    h (fun z => f z+residual z) g u x alpha J D a b hD hh hab hm ha0 hJ0 hx hxD hhJ hode
  · intro z hz
    have he := actual_nominal_uncertainty_margin_implies_the_true_perturbed_barrier_inequality
      h z (f z+g z (u z)) (residual z) alpha (epsilon (h z)) (herror z hz)
    have hn : -alpha (h z)+‖fderiv ℝ h z‖*epsilon (h z)≤fderiv ℝ h z (f z+g z (u z)) := by
      rw [map_add];exact hmargin z hz
    have hb := he hn
    simp only [map_add] at hb ⊢
    linarith
  · exact h0
end SafeLearning.CompleteModulesLandscapeControlAffineDomain
