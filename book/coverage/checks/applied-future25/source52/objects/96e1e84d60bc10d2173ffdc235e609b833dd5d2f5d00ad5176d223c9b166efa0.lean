import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedScalarLQR

def sourceP : ℝ := 1+Real.sqrt 2
def sourceTrajectory (initial time : ℝ) : ℝ := initial*Real.exp (-Real.sqrt 2*time)
def sourceInput (initial time : ℝ) : ℝ := -sourceP*sourceTrajectory initial time

theorem actual_source_riccati_roots_positive_choice_and_rounding :
    (∀P : ℝ,2*P-P^2+1=0 ↔ P=1+Real.sqrt 2 ∨ P=1-Real.sqrt 2) ∧
      (0<sourceP) ∧ (1-Real.sqrt 2<0) ∧
      (24142135/10000000 : ℝ)<sourceP ∧ sourceP<(24142145/10000000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp := Real.sqrt_nonneg (2:ℝ)
  refine ⟨?_,by unfold sourceP;positivity,?_,?_,?_⟩
  · intro P
    constructor
    · intro h
      have hf : (P-(1+Real.sqrt 2))*(P-(1-Real.sqrt 2))=0 := by nlinarith
      rcases mul_eq_zero.mp hf with h|h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (sub_eq_zero.mp h)
    · rintro (rfl|rfl) <;> nlinarith
  · nlinarith
  · unfold sourceP;nlinarith
  · unfold sourceP;nlinarith

theorem actual_hjb_completion_and_unique_minimum (state input : ℝ) :
    state^2+input^2+2*sourceP*state*(state+input)=(input+sourceP*state)^2 ∧
      (0 ≤ state^2+input^2+2*sourceP*state*(state+input)) ∧
      (state^2+input^2+2*sourceP*state*(state+input)=0 ↔ input= -sourceP*state) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have he : state^2+input^2+2*sourceP*state*(state+input)=(input+sourceP*state)^2 := by
    dsimp [sourceP];nlinarith
  rw [he]
  exact ⟨rfl,sq_nonneg _,by rw [sq_eq_zero_iff];constructor <;> intro h <;> linarith⟩

theorem actual_all_finite_cost_classical_trajectories_have_the_value_identity
    (state input : ℝ→ℝ)
    (hode : ∀time∈Ici (0:ℝ),HasDerivAt state (state time+input time) time)
    (hstate : MemLp state 2 (volume.restrict (Ioi (0:ℝ))))
    (hinput : MemLp input 2 (volume.restrict (Ioi (0:ℝ)))) :
    (∫time in Ioi (0:ℝ),state time^2+input time^2)=
      sourceP*state 0^2+(∫time in Ioi (0:ℝ),(input time+sourceP*state time)^2) := by
  let derivative := fun time => 2*sourceP*state time*(state time+input time)
  have hd : ∀time∈Ici (0:ℝ),HasDerivAt (fun time=>sourceP*state time^2)
      (derivative time) time := by
    intro time ht
    convert ((hode time ht).pow 2).const_mul sourceP using 1 <;> dsimp [derivative] <;> ring
  have hm : Integrable (fun time=>state time*(state time+input time))
      (volume.restrict (Ioi (0:ℝ))) := by
    exact memLp_one_iff_integrable.mp (hstate.mul (hstate.add hinput) : MemLp _ 1 _)
  have hdi : IntegrableOn derivative (Ioi (0:ℝ)) := by
    change Integrable derivative _
    have he : derivative=(fun time=>(2*sourceP)*(state time*(state time+input time))) := by
      funext time;dsimp [derivative];ring
    rw [he];exact hm.const_mul (2*sourceP)
  have hsi : IntegrableOn (fun time=>sourceP*state time^2) (Ioi (0:ℝ)) :=
    hstate.integrable_sq.const_mul sourceP
  have hdo : ∀time∈Ioi (0:ℝ),HasDerivAt (fun time=>sourceP*state time^2)
      (derivative time) time := by
    intro time ht
    apply hd time
    change 0≤time
    exact le_of_lt ht
  have hz := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hdo hdi hsi
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd hdi hz
  have hcost := hstate.integrable_sq.add hinput.integrable_sq
  have hresidual : IntegrableOn (fun time=>(input time+sourceP*state time)^2) (Ioi (0:ℝ)) :=
    (hinput.add (hstate.const_mul sourceP)).integrable_sq
  have he : (fun time=>state time^2+input time^2+derivative time)=
      (fun time=>(input time+sourceP*state time)^2) := by
    funext time;exact (actual_hjb_completion_and_unique_minimum (state time) (input time)).1
  have hsum := congrArg (fun f : ℝ→ℝ=>∫time in Ioi (0:ℝ),f time) he
  have hadd := integral_add hcost hdi
  change (∫time in Ioi (0:ℝ),state time^2+input time^2+derivative time)=
    (∫time in Ioi (0:ℝ),state time^2+input time^2)+(∫time in Ioi (0:ℝ),derivative time) at hadd
  rw [hadd,hi] at hsum
  linarith

theorem actual_all_finite_cost_classical_controls_have_cost_at_least_the_derived_value
    (state input : ℝ→ℝ)
    (hode : ∀time∈Ici (0:ℝ),HasDerivAt state (state time+input time) time)
    (hstate : MemLp state 2 (volume.restrict (Ioi (0:ℝ))))
    (hinput : MemLp input 2 (volume.restrict (Ioi (0:ℝ)))) :
    sourceP*state 0^2≤∫time in Ioi (0:ℝ),state time^2+input time^2 := by
  rw [actual_all_finite_cost_classical_trajectories_have_the_value_identity state input hode hstate hinput]
  exact le_add_of_nonneg_right (integral_nonneg (fun _=>sq_nonneg _))

theorem actual_optimal_feedback_trajectory_has_the_true_ode_and_exponential_decay
    (initial : ℝ) :
    sourceTrajectory initial 0=initial ∧
      (∀time : ℝ,HasDerivAt (sourceTrajectory initial)
        (sourceTrajectory initial time+sourceInput initial time) time) ∧
      Tendsto (sourceTrajectory initial) atTop (𝓝 0) := by
  have hr : -Real.sqrt (2:ℝ)<0 := by exact neg_neg_of_pos (Real.sqrt_pos.mpr (by norm_num))
  refine ⟨by simp [sourceTrajectory],?_,?_⟩
  · intro time
    change HasDerivAt (fun t=>initial*Real.exp (-Real.sqrt 2*t)) _ time
    convert (((hasDerivAt_id time).const_mul (-Real.sqrt 2)).exp).const_mul initial using 1 <;>
      dsimp [sourceTrajectory,sourceInput,sourceP] <;> ring
  · have he := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hr)
    change Tendsto (fun t=>initial*Real.exp (-Real.sqrt 2*t)) atTop (𝓝 0)
    simpa only [mul_zero,Function.comp_def,id_eq] using he.const_mul initial

theorem actual_optimal_feedback_trajectory_has_square_integrable_state_and_input
    (initial : ℝ) :
    MemLp (sourceTrajectory initial) 2 (volume.restrict (Ioi (0:ℝ))) ∧
      MemLp (sourceInput initial) 2 (volume.restrict (Ioi (0:ℝ))) := by
  have hr : -(2*Real.sqrt (2:ℝ))<0 := by
    have hs := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2);nlinarith
  have hi := (integrableOn_exp_mul_Ioi hr (0:ℝ)).const_mul (initial^2)
  have he : (fun time : ℝ=>sourceTrajectory initial time^2)=
      (fun time=>initial^2*Real.exp (-(2*Real.sqrt 2)*time)) := by
    funext time
    dsimp [sourceTrajectory]
    rw [mul_pow,←Real.exp_nat_mul]
    congr 2;ring
  have hs : MemLp (sourceTrajectory initial) 2 (volume.restrict (Ioi (0:ℝ))) :=
    (memLp_two_iff_integrable_sq (by unfold sourceTrajectory;fun_prop)).mpr (he ▸ hi)
  exact ⟨hs,hs.const_mul (-sourceP)⟩

theorem actual_feedback_attains_the_true_infinite_horizon_cost (initial : ℝ) :
    (∫time in Ioi (0:ℝ),sourceTrajectory initial time^2+sourceInput initial time^2)=sourceP*initial^2 := by
  have hs := actual_optimal_feedback_trajectory_has_square_integrable_state_and_input initial
  rw [actual_all_finite_cost_classical_trajectories_have_the_value_identity
    (sourceTrajectory initial) (sourceInput initial)
    (fun time _=>(actual_optimal_feedback_trajectory_has_the_true_ode_and_exponential_decay initial).2.1 time)
    hs.1 hs.2,(actual_optimal_feedback_trajectory_has_the_true_ode_and_exponential_decay initial).1]
  simp [sourceInput]

end SafeLearning.CompleteAppliedScalarLQR
