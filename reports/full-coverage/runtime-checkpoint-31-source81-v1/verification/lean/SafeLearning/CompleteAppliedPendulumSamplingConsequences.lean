import SafeLearning.CompleteAppliedPendulumSampling

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedPendulumSamplingConsequences
open SafeLearning.CompleteAppliedPendulumSampling

theorem actual_euler_energy_is_bounded_by_the_true_state_norm (x:ℝ×ℝ) :
    energy x≤12*‖x‖^2 := by
  have hq : |x.1|≤‖x‖:=by simpa only [Real.norm_eq_abs] using norm_fst_le x
  have hv : |x.2|≤‖x‖:=by simpa only [Real.norm_eq_abs] using norm_snd_le x
  have hq2 : x.1^2≤‖x‖^2:=by nlinarith [sq_abs x.1,abs_nonneg x.1,norm_nonneg x]
  have hv2 : x.2^2≤‖x‖^2:=by nlinarith [sq_abs x.2,abs_nonneg x.2,norm_nonneg x]
  dsimp [energy]
  nlinarith [sq_nonneg (x.1-x.2)]

theorem actual_every_nonzero_hanging_euler_trajectory_has_growing_norm (x:ℝ×ℝ) (hx:x≠0) :
    Tendsto (fun n:ℕ=>‖trajectory x n‖) atTop atTop := by
  have he:=actual_every_nonzero_hanging_euler_trajectory_energy_grows_without_bound x hx
  apply tendsto_atTop.mpr
  intro bound
  by_cases hb : bound≤0
  · exact Eventually.of_forall (fun n=>hb.trans (norm_nonneg _))
  · have hbpos:0<bound:=lt_of_not_ge hb
    filter_upwards [he.eventually (eventually_ge_atTop (12*bound^2+1))] with n hn
    have h:=actual_euler_energy_is_bounded_by_the_true_state_norm (trajectory x n)
    by_contra hh
    have hlt:‖trajectory x n‖<bound:=lt_of_not_ge hh
    nlinarith [norm_nonneg (trajectory x n)]

theorem actual_hanging_euler_model_is_lyapunov_unstable :
    ∀delta:ℝ,0<delta → ∃initial:ℝ×ℝ,
      ‖initial‖<delta ∧ ∃n:ℕ,(1:ℝ)≤‖trajectory initial n‖ := by
  intro delta hd
  let initial:ℝ×ℝ:=(delta/2,0)
  have hi:initial≠0:=by
    intro h
    have hfst:=congrArg Prod.fst h
    change delta/2=0 at hfst
    linarith
  have ht:=actual_every_nonzero_hanging_euler_trajectory_has_growing_norm initial hi
  obtain ⟨n,hn⟩:=(ht.eventually (eventually_ge_atTop (1:ℝ))).exists
  refine ⟨initial,?_,n,hn⟩
  change max |delta/2| |(0:ℝ)| <delta
  rw [abs_zero,abs_of_pos (show (0:ℝ)<delta/2 by linarith),
    max_eq_left (show (0:ℝ)≤delta/2 by linarith)]
  linarith

end SafeLearning.CompleteAppliedPendulumSamplingConsequences
