import SafeLearning.CompleteBarrierVectorChainRule
import SafeLearning.CompleteBarrierNonlinearDomainComparison
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
namespace SafeLearning.CompleteModulesLandscapeFilteredController

def projected (beta state requested : ℝ) : ℝ := max requested (-beta*state)

theorem actual_scalar_CBF_QP_has_the_unique_projected_solution
    (beta state requested : ℝ) :
    -beta*state≤projected beta state requested ∧
      (∀u : ℝ, -beta*state≤u →
        (projected beta state requested-requested)^2≤(u-requested)^2) ∧
      ∀u : ℝ, -beta*state≤u →
        (u-requested)^2=(projected beta state requested-requested)^2 →
        u=projected beta state requested := by
  refine ⟨le_max_right _ _,?_,?_⟩
  · intro u hu
    by_cases hr : -beta*state≤requested
    · rw [projected,max_eq_left hr]
      simpa using sq_nonneg (u-requested)
    · have hb : requested < -beta*state := lt_of_not_ge hr
      rw [projected,max_eq_right hb.le]
      have hp : 0≤u-(-beta*state) := sub_nonneg.mpr hu
      nlinarith [sq_nonneg (u-(-beta*state))]
  · intro u hu he
    by_cases hr : -beta*state≤requested
    · rw [projected,max_eq_left hr] at he ⊢
      have hz : (u-requested)^2=0 := by simpa using he
      have hs := sq_eq_zero_iff.mp hz
      linarith
    · have hb : requested < -beta*state := lt_of_not_ge hr
      rw [projected,max_eq_right hb.le] at he ⊢
      nlinarith [sq_nonneg (u-(-beta*state))]

theorem actual_scalar_QP_is_one_Lipschitz_in_the_requested_command
    (beta state : ℝ) : LipschitzWith 1 (projected beta state) := by
  exact LipschitzWith.id.max_const (-beta*state)

theorem actual_time_varying_requested_policy_is_safe_when_continuously_projected
    (requested : ℝ → ℝ → ℝ) (x : ℝ → ℝ) (beta horizon : ℝ)
    (hT : 0≤horizon) (hx : AbsolutelyContinuousOnInterval x 0 horizon)
    (hode : ∀ᵐt ∂volume, t∈Icc 0 horizon →
      HasDerivAt x (projected beta (x t) (requested t (x t))) t)
    (h0 : 0≤x 0) : ∀t∈Icc 0 horizon,
      x 0*Real.exp (-beta*t)≤x t ∧ 0≤x t := by
  have hb : ∀ᵐt ∂volume, t∈Icc 0 horizon →
      -beta*x t≤projected beta (x t) (requested t (x t)) :=
    Eventually.of_forall fun t _ => le_max_right _ _
  intro t ht
  have he := CompleteBarrierAbsolutelyContinuous.genuine_ae_integrating_factor x
    (fun t => projected beta (x t) (requested t (x t))) beta horizon hT hx hode hb t ht
  exact ⟨he,(mul_nonneg h0 (Real.exp_pos _).le).trans he⟩

theorem actual_initial_only_filter_and_held_command_do_not_protect_later_times :
    projected 1 1 (-2)=-1 ∧
      (∀t : ℝ, HasDerivAt (fun s : ℝ => 1-s) (-1) t) ∧
      (∀t : ℝ, 0<t → projected 1 1 (-2)+(1-t)<0) ∧
      (∀t : ℝ, 1<t → (1-t:ℝ)<0) := by
  refine ⟨by norm_num [projected],?_,?_,?_⟩
  · intro t
    convert! (hasDerivAt_neg' t).const_add (1:ℝ) using 1 <;> rfl
  · intro t ht; norm_num [projected]; linarith
  · intro t ht; linarith

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

theorem actual_time_dependent_filtered_control_affine_trajectory_is_safe
    (h : E → ℝ) (f : E → E) (g : E → U →L[ℝ] E) (filtered : ℝ → E → U) (x : ℝ → E)
    (alpha : ℝ → ℝ) (J : Set ℝ) (D : Set E) (a b : ℝ)
    (hD : IsOpen D) (hh : ContDiffOn ℝ 1 h D) (hab : a≤b)
    (hm : MonotoneOn alpha J) (ha0 : alpha 0=0) (hJ0 : (0:ℝ)∈J)
    (hx : AbsolutelyContinuousOnInterval x a b) (hxD : MapsTo x (uIcc a b) D)
    (hhJ : MapsTo h D J)
    (hode : ∀ᵐt ∂volume, t∈Icc a b → HasDerivAt x (f (x t)+g (x t) (filtered t (x t))) t)
    (hcbf : ∀ᵐt ∂volume, t∈Icc a b → ∀z∈D,
      -alpha (h z)≤fderiv ℝ h z (f z)+fderiv ℝ h z (g z (filtered t z)))
    (h0 : 0≤h (x a)) : ∀t∈Icc a b, 0≤h (x t) := by
  apply CompleteBarrierNonlinearDomainComparison.genuine_nonlinear_invariance
    (h ∘ x) (fun t => fderiv ℝ h (x t) (f (x t)+g (x t) (filtered t (x t))))
    alpha J a b hab hm ha0
    (CompleteBarrierVectorChainRule.genuine_c1_ac_composition h x D a b hD hh hx hxD) hJ0
  · intro t ht
    exact hhJ (hxD (by simpa [uIcc_of_le hab] using ht))
  · exact CompleteBarrierVectorChainRule.genuine_ae_vector_chain_rule h x
      (fun t => f (x t)+g (x t) (filtered t (x t))) D a b hD hh hab hxD hode
  · filter_upwards [hcbf] with t hb ht
    rw [map_add]
    exact hb ht (x t) (hxD (by simpa [uIcc_of_le hab] using ht))
  · exact h0
end SafeLearning.CompleteModulesLandscapeFilteredController
