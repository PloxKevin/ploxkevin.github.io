import SafeLearning.CompleteBarrierAbsolutelyContinuous

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SafeLearning.CompleteAppliedActuatorBarrier

def strongestInwardTrajectory (initial t : ℝ) : ℝ :=
  1/2+(initial-1/2)*Real.exp (2*t)

theorem actual_most_negative_admissible_input_still_points_outward
    (x u : ℝ) (hx : 1/2 < x) (hu : |u| ≤ 1) : 0 < 2*x+u := by
  have hl := (abs_le.mp hu).1
  linarith

theorem actual_comparison_trajectory_initial_and_ODE (initial t : ℝ) :
    strongestInwardTrajectory initial 0=initial ∧
    HasDerivAt (strongestInwardTrajectory initial)
      (2*strongestInwardTrajectory initial t-1) t := by
  constructor
  · simp [strongestInwardTrajectory]
  · unfold strongestInwardTrajectory
    convert ((((hasDerivAt_id t).const_mul 2).exp).const_mul (initial-1/2)).const_add (1/2)
      using 1 <;> (try ext s) <;> simp only [id_eq] <;> ring

theorem actual_every_admissible_almost_everywhere_control_obeys_the_comparison
    (x u : ℝ → ℝ) (horizon : ℝ) (hT : 0 ≤ horizon)
    (hAC : AbsolutelyContinuousOnInterval x 0 horizon)
    (hODE : ∀ᵐ t ∂volume,t ∈ Icc 0 horizon → HasDerivAt x (2*x t+u t) t)
    (hu : ∀ᵐ t ∂volume,t ∈ Icc 0 horizon → |u t|≤1) :
    ∀ t ∈ Icc 0 horizon,strongestInwardTrajectory (x 0) t ≤ x t := by
  have hc : AbsolutelyContinuousOnInterval (fun t => x t-1/2) 0 horizon :=
    hAC.sub (ContDiffOn.absolutelyContinuousOnInterval (by fun_prop))
  have hd : ∀ᵐ t ∂volume,t ∈ Icc 0 horizon →
      HasDerivAt (fun s => x s-1/2) (2*x t+u t) t := by
    filter_upwards [hODE] with t ht hs
    exact (ht hs).sub_const (1/2)
  have hl : ∀ᵐ t ∂volume,t ∈ Icc 0 horizon →
      -(-2)*(x t-1/2) ≤ 2*x t+u t := by
    filter_upwards [hu] with t ht hs
    have habs := (abs_le.mp (ht hs)).1
    linarith
  intro t ht
  have h := CompleteBarrierAbsolutelyContinuous.genuine_ae_integrating_factor
    (fun t => x t-1/2) (fun t => 2*x t+u t) (-2) horizon hT hc hd hl t ht
  dsimp [strongestInwardTrajectory]
  norm_num at h
  linarith

theorem actual_no_admissible_existing_trajectory_can_cross_back_below_the_boundary
    (x u : ℝ → ℝ) (horizon : ℝ) (hT : 0 ≤ horizon)
    (hAC : AbsolutelyContinuousOnInterval x 0 horizon)
    (hODE : ∀ᵐ t ∂volume,t ∈ Icc 0 horizon → HasDerivAt x (2*x t+u t) t)
    (hu : ∀ᵐ t ∂volume,t ∈ Icc 0 horizon → |u t|≤1)
    (hinitial : 1/2 < x 0) :
    ∀ t ∈ Icc 0 horizon,1/2 < x t := by
  intro t ht
  have h := actual_every_admissible_almost_everywhere_control_obeys_the_comparison
    x u horizon hT hAC hODE hu t ht
  have hp : 0 < (x 0-1/2)*Real.exp (2*t) :=
    mul_pos (by linarith) (Real.exp_pos _)
  dsimp [strongestInwardTrajectory] at h
  linarith

theorem actual_comparison_trajectory_grows_to_infinity (initial : ℝ)
    (hi : 1/2 < initial) : Tendsto (strongestInwardTrajectory initial) atTop atTop := by
  have he := Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have hm := he.const_mul_atTop (by linarith : 0 < initial-1/2)
  change Tendsto (fun t : ℝ => 1/2+(initial-1/2)*Real.exp (2*t)) atTop atTop
  simpa [add_comm,Function.comp_def] using
    hm.atTop_add (tendsto_const_nhds (x := (1/2:ℝ)))

theorem actual_every_global_admissible_trajectory_grows_away_from_zero
    (x u : ℝ → ℝ)
    (hAC : ∀ horizon : ℝ,0 ≤ horizon → AbsolutelyContinuousOnInterval x 0 horizon)
    (hODE : ∀ᵐ t ∂volume,0 ≤ t → HasDerivAt x (2*x t+u t) t)
    (hu : ∀ᵐ t ∂volume,0 ≤ t → |u t|≤1)
    (hinitial : 1/2 < x 0) : Tendsto x atTop atTop := by
  apply tendsto_atTop_mono' atTop _
    (actual_comparison_trajectory_grows_to_infinity (x 0) hinitial)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  apply actual_every_admissible_almost_everywhere_control_obeys_the_comparison
    x u t ht (hAC t ht) _ _ t ⟨ht,le_rfl⟩
  · filter_upwards [hODE] with s hs hmem
    exact hs hmem.1
  · filter_upwards [hu] with s hs hmem
    exact hs hmem.1

theorem actual_unsaturated_feedback_admissibility_is_exact (x : ℝ) :
    |-(3:ℝ)*x|≤1 ↔ |x|≤1/3 := by
  rw [abs_mul]
  norm_num
  constructor <;> intro h <;> linarith

theorem actual_unsaturated_feedback_closes_to_a_stable_local_rate (x : ℝ) :
    2*x+(-(3:ℝ)*x)=-x := by ring

end SafeLearning.CompleteAppliedActuatorBarrier
