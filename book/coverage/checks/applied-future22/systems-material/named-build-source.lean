import SafeLearning.CompleteAppliedDynamics

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace SafeLearning.CompleteAppliedSystemsMaterial22
open SafeLearning.CompleteAppliedSystems SafeLearning.CompleteAppliedDynamics

theorem actual_temperature_and_input_translations_preserve_the_literal_intervals
    (temperature input : ℝ) :
    (input ∈ Set.Icc (0:ℝ) 2 ↔ input-1 ∈ Set.Icc (-1:ℝ) 1)  ∧ 
    (temperature ∈ Set.Icc (20:ℝ) 24 ↔ temperature-22 ∈ Set.Icc (-2:ℝ) 2)  ∧ 
    (temperature=22 ↔ temperature-22=0) := by
  simp only [Set.mem_Icc]
  constructor
  · constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  constructor
  · constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  · constructor <;> intro h <;> linarith

theorem actual_source_equilibrium_shift_and_continuous_feedback_rate (error : ℝ) :
    -((22:ℝ)-18)/20+(1/5)*1=0  ∧ 
      -((error+22)-18)/20+(1/5)*(-error/2+1)=-(3/20)*error := by
  constructor
  · exact equilibrium_input
  · ring

def actualContinuousThermal (initial time : ℝ) : ℝ :=
  Real.exp (-(3/20)*time)*initial

theorem actual_continuously_updated_source_feedback_solves_its_actual_rate
    (initial time : ℝ) :
    HasDerivAt (actualContinuousThermal initial)
      (-(3/20)*actualContinuousThermal initial time) time := by
  have he := (((hasDerivAt_id time).const_mul (-(3/20:ℝ))).exp).mul_const initial
  convert he using 1 <;> (try ext t) <;>
    simp only [actualContinuousThermal,id_eq] <;>ring

theorem actual_continuous_initial_and_five_minute_multiplier (initial : ℝ) :
    actualContinuousThermal initial 0=initial  ∧ 
      actualContinuousThermal initial 5=Real.exp (-(3/4:ℝ))*initial := by
  constructor
  · simp [actualContinuousThermal]
  · norm_num [actualContinuousThermal]

theorem actual_continuous_five_minute_factor_has_the_literal_six_decimal_rounding :
    (472366552740/1000000000000:ℝ) < Real.exp (-(3/4:ℝ))  ∧ 
      Real.exp (-(3/4:ℝ)) < 472366552743/1000000000000  ∧ 
      |Real.exp (-(3/4:ℝ))-(472367/1000000:ℝ)| < 1/2000000 := by
  have h := Real.exp_bound (x := -(3/4:ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have hh := abs_le.mp h
  refine ⟨?_,?_,?_⟩
  · linarith
  · linarith
  · rw [abs_lt]
    constructor <;> linarith

theorem actual_continuous_and_held_feedback_have_distinct_five_minute_updates
    (initial : ℝ) (hinitial : initial ≠ 0) :
    |thermalQ-(336402/1000000:ℝ)| ≤ 1/2000000  ∧ 
      thermalQ < Real.exp (-(3/4:ℝ))  ∧ 
      actualContinuousThermal initial 5 ≠ heldThermal initial (-initial/2) 5 := by
  have hc := actual_continuous_five_minute_factor_has_the_literal_six_decimal_rounding
  have hq := thermal_rounded_coefficients.2.2.1
  have hstrict : thermalQ < Real.exp (-(3/4:ℝ)) := by
    have hqu := (abs_le.mp hq).2
    linarith [hc.1]
  refine ⟨hq,hstrict,?_⟩
  rw [(actual_continuous_initial_and_five_minute_multiplier initial).2,
    sampled_thermal,sampled_feedback]
  intro he
  exact hstrict.ne' ((mul_left_inj' hinitial).mp he)

theorem actual_stable_unclipped_gain_can_still_violate_the_source_heater_limit :
    |thermalA-thermalB|<1  ∧ 
      (∀ initial : ℝ,Tendsto (fun n : ℕ => (thermalA-thermalB)^n*initial)
        atTop (𝓝 0))  ∧  (1-(-2:ℝ)=3)  ∧  ¬(1-(-2:ℝ) ∈ Set.Icc (0:ℝ) 2) := by
  obtain ⟨hl,hu⟩ := thermalA_precise
  have ha : |thermalA-thermalB|<1 := by
    rw [abs_lt]
    unfold thermalB
    constructor <;> linarith
  refine ⟨ha,?_,by norm_num,by norm_num⟩
  intro initial
  have hp : Tendsto (fun n : ℕ => (thermalA-thermalB)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_iff.mpr ha
  simpa using hp.mul_const initial

theorem actual_delayed_robot_consumes_the_literal_distance_and_stops_beyond_the_wall :
    (1:ℝ)*(2/5)=2/5  ∧  (4/5:ℝ)-1*(2/5)=2/5  ∧ 
      (1:ℝ)^2/(2*1)=1/2  ∧  delayedDistance (4/5) 1 1 (2/5) (7/5)=-(1/10)  ∧ 
      ¬(∀ time : ℝ,0 ≤ time  →  0 ≤ delayedDistance (4/5) 1 1 (2/5) time) := by
  refine ⟨by norm_num,by norm_num,by norm_num,?_,?_⟩
  · norm_num [delayedDistance,stoppedDistance,brakeDistance,stoppingClearance]
  · rw [nominal_delay_endpoint (2/5) (by norm_num)]
    norm_num

theorem actual_immediate_braking_is_safe_while_the_point_four_delay_is_unsafe :
    (∀ time : ℝ,0 ≤ time  →  0 ≤ delayedDistance (4/5) 1 1 0 time)  ∧ 
      (∀ delay : ℝ,0 ≤ delay  → 
        ((∀ time : ℝ,0 ≤ time  →  0 ≤ delayedDistance (4/5) 1 1 delay time) ↔
          delay ≤ 3/10))  ∧  (3/10:ℝ)<2/5 := by
  refine ⟨(nominal_delay_endpoint 0 (by norm_num)).2 (by norm_num),?_,by norm_num⟩
  intro delay hdelay
  exact nominal_delay_endpoint delay hdelay

theorem actual_optimistic_acceleration_can_pass_its_estimated_test_but_hit_the_wall :
    stoppingClearance (2/5) 1 2=3/20  ∧  0 ≤ stoppingClearance (2/5) 1 2  ∧ 
      stoppingClearance (2/5) 1 1=-(1/10)  ∧ 
      stoppedDistance (2/5) 1 1 1=-(1/10)  ∧ 
      ¬(∀ time : ℝ,0 ≤ time  →  0 ≤ stoppedDistance (2/5) 1 1 time) := by
  refine ⟨by norm_num [stoppingClearance],by norm_num [stoppingClearance],
    by norm_num [stoppingClearance],by norm_num [stoppedDistance,brakeDistance],?_⟩
  rw [stopped_safe_iff (2/5) 1 1 (by norm_num) (by norm_num)]
  norm_num [stoppingClearance]

theorem actual_uncertain_braking_worst_corner_requires_both_delay_and_stopping_distance
    (distance speed acceleration delay : ℝ)
    (hdistance : distance ∈ Set.Icc (18/25) (39/50))
    (hspeed : speed ∈ Set.Icc (9/10) (11/10)) (hacceleration : 1 ≤ acceleration)
    (hdelay : 0 ≤ delay) :
    speed*delay+speed^2/(2*acceleration) ≤ (11/10)*delay+121/200  ∧ 
      ((11/10)*delay+121/200 ≤ 18/25  → 
        ∀ time : ℝ,0 ≤ time  →  0 ≤ delayedDistance distance speed acceleration delay time) := by
  have hspeed0 : 0 ≤ speed := by linarith [hspeed.1]
  have hs : speed^2 ≤ (11/10:ℝ)^2 := by nlinarith [hspeed.1,hspeed.2]
  have hquot : speed^2/(2*acceleration) ≤ 121/200 := by
    apply (div_le_iff₀ (by linarith : 0<2*acceleration)).2
    nlinarith
  have htravel := mul_le_mul_of_nonneg_right hspeed.2 hdelay
  refine ⟨by linarith,?_⟩
  intro hcorner
  apply (delayed_safe_iff distance speed acceleration delay hspeed0
    (by linarith) hdelay).2
  linarith [hdistance.1]

end SafeLearning.CompleteAppliedSystemsMaterial22
