import SafeLearning.CompleteAppliedACImproperFTC
import SafeLearning.CompleteAppliedScalarLQRConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedScalarLQRAC
open CompleteAppliedACImproperFTC CompleteAppliedScalarLQR CompleteAppliedScalarLQRConsequences

theorem actual_riccati_completed_square_and_quadratic_value_derivative (P state : ℝ) :
    ((P-1)^2=2 ↔ 2*P-P^2+1=0) ∧
      HasDerivAt (fun point : ℝ=>P*point^2) (2*P*state) state := by
  constructor
  · constructor <;> intro h <;> nlinarith
  · convert ((hasDerivAt_id state).pow 2).const_mul P using 1 <;>
      (try funext point) <;> simp [Pi.pow_apply,id_eq] <;> ring

theorem actual_all_finite_cost_ac_trajectories_have_the_value_identity_and_zero_storage_limit
    (state input : ℝ→ℝ)
    (hlocal : ∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval state 0 horizon)
    (hode : ∀ᵐtime ∂volume,time∈Ici (0:ℝ)→HasDerivAt state (state time+input time) time)
    (hstate : MemLp state 2 (volume.restrict (Ioi (0:ℝ))))
    (hinput : MemLp input 2 (volume.restrict (Ioi (0:ℝ)))) :
    Tendsto (fun time=>sourceP*state time^2) atTop (𝓝 0) ∧
      (∫time in Ioi (0:ℝ),state time^2+input time^2)=
        sourceP*state 0^2+(∫time in Ioi (0:ℝ),(input time+sourceP*state time)^2) := by
  let derivative := fun time=>2*sourceP*state time*(state time+input time)
  have hstorage : ∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval
      (fun time=>sourceP*state time^2) 0 horizon := by
    intro horizon ht
    simpa only [pow_two,Pi.mul_apply] using
      AbsolutelyContinuousOnInterval.const_mul sourceP ((hlocal horizon ht).mul (hlocal horizon ht))
  have hd : ∀ᵐtime ∂volume,time∈Ici (0:ℝ)→HasDerivAt (fun time=>sourceP*state time^2)
      (derivative time) time := by
    filter_upwards [hode] with time ht hs
    convert ((ht hs).pow 2).const_mul sourceP using 1 <;> dsimp [derivative] <;> ring
  have hm : Integrable (fun time=>state time*(state time+input time))
      (volume.restrict (Ioi (0:ℝ))) :=
    memLp_one_iff_integrable.mp (hstate.mul (hstate.add hinput) : MemLp _ 1 _)
  have hdi : IntegrableOn derivative (Ioi (0:ℝ)) := by
    have he : derivative=(fun time=>(2*sourceP)*(state time*(state time+input time))) := by
      funext time;dsimp [derivative];ring
    rw [he];exact hm.const_mul (2*sourceP)
  have hsi : IntegrableOn (fun time=>sourceP*state time^2) (Ioi (0:ℝ)) :=
    hstate.integrable_sq.const_mul sourceP
  have hi := actual_locally_absolutely_continuous_integrable_function_and_ae_derivative_have_zero_limit
    (fun time=>sourceP*state time^2) derivative hstorage hd hdi hsi
  refine ⟨hi.1,?_⟩
  have hcost := hstate.integrable_sq.add hinput.integrable_sq
  have he : (fun time=>state time^2+input time^2+derivative time)=
      (fun time=>(input time+sourceP*state time)^2) := by
    funext time;exact (actual_hjb_completion_and_unique_minimum (state time) (input time)).1
  have hsum := congrArg (fun f : ℝ→ℝ=>∫time in Ioi (0:ℝ),f time) he
  have hadd := integral_add hcost hdi
  change (∫time in Ioi (0:ℝ),state time^2+input time^2+derivative time)=
    (∫time in Ioi (0:ℝ),state time^2+input time^2)+(∫time in Ioi (0:ℝ),derivative time) at hadd
  rw [hadd,hi.2] at hsum
  linarith

def actualFiniteCostACPairs (initial : ℝ) : Set ((ℝ→ℝ)×(ℝ→ℝ)) :=
  {pair | pair.1 0=initial ∧
    (∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval pair.1 0 horizon) ∧
    (∀ᵐtime ∂volume,time∈Ici (0:ℝ)→HasDerivAt pair.1 (pair.1 time+pair.2 time) time) ∧
    MemLp pair.1 2 (volume.restrict (Ioi (0:ℝ))) ∧
    MemLp pair.2 2 (volume.restrict (Ioi (0:ℝ)))}

theorem actual_source_value_is_the_attained_global_minimum_of_all_finite_cost_ac_pairs
    (initial : ℝ) :
    IsLeast (actualSourceCost '' actualFiniteCostACPairs initial) (sourceP*initial^2) := by
  have ht := actual_optimal_feedback_trajectory_has_the_true_ode_and_exponential_decay initial
  have hs := actual_optimal_feedback_trajectory_has_square_integrable_state_and_input initial
  constructor
  · refine ⟨(sourceTrajectory initial,sourceInput initial),⟨ht.1,?_,?_,hs⟩,?_⟩
    · intro horizon hh
      apply ContDiffOn.absolutelyContinuousOnInterval
      unfold sourceTrajectory
      fun_prop
    · filter_upwards [] with time htime
      exact ht.2.1 time
    · exact actual_feedback_attains_the_true_infinite_horizon_cost initial
  · rintro cost ⟨pair,⟨hzero,hlocal,hode,hstate,hinput⟩,rfl⟩
    have hi := (actual_all_finite_cost_ac_trajectories_have_the_value_identity_and_zero_storage_limit
      pair.1 pair.2 hlocal hode hstate hinput).2
    have hnonnegative : 0≤∫time in Ioi (0:ℝ),(pair.2 time+sourceP*pair.1 time)^2 :=
      integral_nonneg (fun _=>sq_nonneg _)
    change sourceP*initial^2≤∫time in Ioi (0:ℝ),pair.1 time^2+pair.2 time^2
    rw [hi,hzero]
    linarith

end SafeLearning.CompleteAppliedScalarLQRAC
