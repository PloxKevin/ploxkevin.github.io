import Mathlib

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace SafeLearning.CompleteAppliedDoubleIntegratorWall27

/-- Actual absolutely continuous double-integrator solutions, with arbitrary
measurable bounded input. No stopping, comparison or safety conclusion is a field. -/
structure ControlledPath (a x v : ℝ) where
  position : ℝ → ℝ
  velocity : ℝ → ℝ
  input : ℝ → ℝ
  position_zero : position 0 = x
  velocity_zero : velocity 0 = v
  input_measurable : Measurable input
  input_bound : ∀ t : ℝ, 0 ≤ t → |input t| ≤ a
  position_ac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval position 0 T
  velocity_ac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval velocity 0 T
  derivatives_ae : ∀ᵐ t : ℝ ∂volume, 0 ≤ t →
    HasDerivAt position (velocity t) t ∧ HasDerivAt velocity (input t) t

def Viable (a L x v : ℝ) : Prop :=
  ∃ P : ControlledPath a x v, ∀ t : ℝ, 0 ≤ t → P.position t < L

def printedKernel (a L : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 < L ∧ (z.2 ≤ 0 ∨ z.1 + z.2 ^ 2 / (2 * a) < L)}

/-- The actual ODE and absolute continuity derive its integral representation. -/
theorem actual_velocity_integral (a x v t : ℝ) (P : ControlledPath a x v) (ht : 0 ≤ t) :
    (∫ s : ℝ in 0..t, P.input s) = P.velocity t - v := by
  calc
    _ = ∫ s : ℝ in 0..t, deriv P.velocity s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [P.derivatives_ae] with s hs hmem
      rw [uIoc_of_le ht] at hmem
      exact (hs hmem.1.le).2.deriv.symm
    _ = P.velocity t - P.velocity 0 := (P.velocity_ac t ht).integral_deriv_eq_sub
    _ = P.velocity t - v := by rw [P.velocity_zero]

theorem actual_position_integral (a x v t : ℝ) (P : ControlledPath a x v) (ht : 0 ≤ t) :
    (∫ s : ℝ in 0..t, P.velocity s) = P.position t - x := by
  calc
    _ = ∫ s : ℝ in 0..t, deriv P.position s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [P.derivatives_ae] with s hs hmem
      rw [uIoc_of_le ht] at hmem
      exact (hs hmem.1.le).1.deriv.symm
    _ = P.position t - P.position 0 := (P.position_ac t ht).integral_deriv_eq_sub
    _ = P.position t - x := by rw [P.position_zero]

/-- Every bounded control lies above the full-braking velocity, derived by FTC. -/
theorem every_actual_control_velocity_has_the_braking_lower_bound
    (a x v t : ℝ) (P : ControlledPath a x v) (ht : 0 ≤ t) :
    v - a * t ≤ P.velocity t := by
  have hmono : (∫ s : ℝ in 0..t, (-a : ℝ)) ≤
      ∫ s : ℝ in 0..t, deriv P.velocity s := by
    apply intervalIntegral.integral_mono_ae_restrict ht intervalIntegrable_const
      (P.velocity_ac t ht).intervalIntegrable_deriv
    filter_upwards [ae_restrict_of_ae P.derivatives_ae,
      ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [(hs hmem.1).2.deriv]
    exact (abs_le.mp (P.input_bound s hmem.1)).1
  rw [intervalIntegral.integral_const,
    (P.velocity_ac t ht).integral_deriv_eq_sub, P.velocity_zero] at hmono
  simp only [sub_zero, smul_eq_mul] at hmono
  nlinarith

theorem actual_integral_of_the_braking_velocity (a v t : ℝ) :
    (∫ s : ℝ in 0..t, v - a * s) = v * t - a * t ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun s : ℝ => a * s) volume 0 t :=
    (by fun_prop : Continuous (fun s : ℝ => a * s)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [sub_zero, smul_eq_mul, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true]
  ring

/-- The source comparison holds for arbitrary actual bounded-input paths, not
only a supplied polynomial stopping trajectory. -/
theorem every_actual_control_position_has_the_braking_lower_bound
    (a x v t : ℝ) (P : ControlledPath a x v) (ht : 0 ≤ t) :
    x + v * t - a * t ^ 2 / 2 ≤ P.position t := by
  have hi : IntervalIntegrable (fun s : ℝ => v - a * s) volume 0 t :=
    (by fun_prop : Continuous (fun s : ℝ => v - a * s)).intervalIntegrable _ _
  have hmono : (∫ s : ℝ in 0..t, v - a * s) ≤
      ∫ s : ℝ in 0..t, deriv P.position s := by
    apply intervalIntegral.integral_mono_ae_restrict ht hi
      (P.position_ac t ht).intervalIntegrable_deriv
    filter_upwards [ae_restrict_of_ae P.derivatives_ae,
      ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [(hs hmem.1).1.deriv]
    exact every_actual_control_velocity_has_the_braking_lower_bound a x v s P hmem.1
  rw [actual_integral_of_the_braking_velocity,
    (P.position_ac t ht).integral_deriv_eq_sub, P.position_zero] at hmono
  linarith

theorem actual_closed_wall_failure_by_stopping_time
    (a L x v : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hpeak : L ≤ x + v ^ 2 / (2 * a)) (P : ControlledPath a x v) :
    0 ≤ v / a ∧ L ≤ P.position (v / a) := by
  have ht : 0 ≤ v / a := div_nonneg hv.le ha.le
  refine ⟨ht, ?_⟩
  have hp := every_actual_control_position_has_the_braking_lower_bound a x v (v/a) P ht
  have he : x + v * (v/a) - a * (v/a)^2/2 = x + v^2/(2*a) := by
    field_simp
    ring
  rw [he] at hp
  exact hpeak.trans hp

theorem actual_initial_velocity_bound_gives_the_uniform_failure_horizon
    (a L x v vmax : ℝ) (ha : 0 < a) (hv : 0 < v) (hbound : |v| ≤ vmax)
    (hpeak : L ≤ x + v ^ 2 / (2 * a)) (P : ControlledPath a x v) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ vmax / a ∧ L ≤ P.position t := by
  have h := actual_closed_wall_failure_by_stopping_time a L x v ha hv hpeak P
  refine ⟨v/a, h.1, ?_, h.2⟩
  exact (div_le_div_iff_of_pos_right ha).mpr (by simpa [abs_of_pos hv] using hbound)

theorem every_actual_viable_state_has_the_printed_kernel_conditions
    (a L x v : ℝ) (ha : 0 < a) (hviable : Viable a L x v) :
    (x,v) ∈ printedKernel a L := by
  obtain ⟨P, hsafe⟩ := hviable
  have hx : x < L := by simpa [P.position_zero] using hsafe 0 (le_refl 0)
  refine ⟨hx, ?_⟩
  by_cases hv : v ≤ 0
  · exact Or.inl hv
  · right
    by_contra hn
    have hf := actual_closed_wall_failure_by_stopping_time a L x v ha (lt_of_not_ge hv)
      (le_of_not_gt hn) P
    exact (not_lt_of_ge hf.2) (hsafe (v/a) hf.1)


/-- A legal zero-input trajectory, including the AC and actual ODE obligations. -/
def zeroInputPath (a x v : ℝ) (ha : 0 ≤ a) : ControlledPath a x v where
  position := fun t => x + v * t
  velocity := fun _ => v
  input := fun _ => 0
  position_zero := by simp
  velocity_zero := rfl
  input_measurable := measurable_const
  input_bound := by intro t ht; simpa using ha
  position_ac := by
    intro T hT
    exact (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => x + v * t)).contDiffOn.absolutelyContinuousOnInterval
  velocity_ac := by
    intro T hT
    exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => v)).contDiffOn.absolutelyContinuousOnInterval
  derivatives_ae := by
    filter_upwards with t
    intro ht
    constructor
    · convert (hasDerivAt_const t x).add ((hasDerivAt_id t).const_mul v) using 1 <;>
        (try ext z) <;> simp <;> ring
    · exact hasDerivAt_const t v

def brakingTime (a v t : ℝ) : ℝ := min t (v/a)
def brakingPosition (a x v t : ℝ) : ℝ :=
  x + v * brakingTime a v t - (a/2) * (brakingTime a v t * brakingTime a v t)
def brakingVelocity (a v t : ℝ) : ℝ := v - a * brakingTime a v t
def brakingInput (a v t : ℝ) : ℝ := if t < v/a then -a else 0

private theorem brakingTime_ac (a v T : ℝ) :
    AbsolutelyContinuousOnInterval (brakingTime a v) 0 T := by
  exact (LipschitzWith.id.min_const (v/a)).lipschitzOnWith.absolutelyContinuousOnInterval

private theorem brakingTime_hasDeriv_before (a v t : ℝ) (ht : t < v/a) :
    HasDerivAt (brakingTime a v) 1 t := by
  apply (hasDerivAt_id t).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds ht] with y hy
  exact min_eq_left hy.le

private theorem brakingTime_hasDeriv_after (a v t : ℝ) (ht : v/a < t) :
    HasDerivAt (brakingTime a v) 0 t := by
  apply (hasDerivAt_const t (v/a)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with y hy
  exact min_eq_right hy.le

/-- Full braking until zero velocity, then zero input, is an actual measurable
bounded-input AC/AE-ODE path, not a supplied safety conclusion. -/
def brakingPath (a x v : ℝ) (ha : 0 < a) (hv : 0 ≤ v) : ControlledPath a x v where
  position := brakingPosition a x v
  velocity := brakingVelocity a v
  input := brakingInput a v
  position_zero := by
    simp [brakingPosition, brakingTime, min_eq_left (div_nonneg hv ha.le)]
  velocity_zero := by
    simp [brakingVelocity, brakingTime, min_eq_left (div_nonneg hv ha.le)]
  input_measurable := by
    exact Measurable.ite measurableSet_Iio measurable_const measurable_const
  input_bound := by
    intro t ht
    simp only [brakingInput]
    split_ifs <;> simp [abs_of_nonneg ha.le, ha.le]
  position_ac := by
    intro T hT
    have hz := brakingTime_ac a v T
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => x) 0 T :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => x)).contDiffOn.absolutelyContinuousOnInterval
    exact (hc.fun_add (hz.const_mul v)).fun_sub ((hz.fun_mul hz).const_mul (a/2))
  velocity_ac := by
    intro T hT
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => v) 0 T :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => v)).contDiffOn.absolutelyContinuousOnInterval
    exact hc.fun_sub ((brakingTime_ac a v T).const_mul a)
  derivatives_ae := by
    filter_upwards [volume.ae_ne (v/a)] with t hne
    intro ht
    rcases lt_or_gt_of_ne hne with hbefore | hafter
    · have hz := brakingTime_hasDeriv_before a v t hbefore
      constructor
      · have hp := ((hasDerivAt_const t x).add (hz.const_mul v)).sub
          ((hz.mul hz).const_mul (a/2))
        convert hp using 1 <;> (try ext z) <;>
          dsimp [brakingPosition, brakingVelocity] <;> ring
      · have hv' := (hasDerivAt_const t v).sub (hz.const_mul a)
        convert hv' using 1 <;> (try ext z) <;>
          simp [brakingVelocity, brakingInput, hbefore]
    · have hz := brakingTime_hasDeriv_after a v t hafter
      have hvzero : brakingVelocity a v t = 0 := by
        simp only [brakingVelocity, brakingTime, min_eq_right hafter.le]
        field_simp
        ring
      constructor
      · have hp := ((hasDerivAt_const t x).add (hz.const_mul v)).sub
          ((hz.mul hz).const_mul (a/2))
        rw [hvzero]
        convert hp using 1 <;> (try ext z) <;>
          dsimp [brakingPosition] <;> ring
      · have hv' := (hasDerivAt_const t v).sub (hz.const_mul a)
        convert hv' using 1 <;> (try ext z) <;>
          simp [brakingVelocity, brakingInput, not_lt_of_ge hafter.le]

theorem actual_braking_position_is_bounded_by_its_stopping_peak
    (a x v t : ℝ) (ha : 0 < a) :
    brakingPosition a x v t ≤ x + v^2/(2*a) := by
  have he : x + v^2/(2*a) - brakingPosition a x v t =
      (a/2) * (v/a - brakingTime a v t)^2 := by
    unfold brakingPosition
    field_simp
    ring
  have hn : 0 ≤ (a/2) * (v/a - brakingTime a v t)^2 := by positivity
  linarith

theorem actual_braking_path_is_safe_under_strict_stopping_clearance
    (a L x v : ℝ) (ha : 0 < a) (hv : 0 ≤ v)
    (hpeak : x + v^2/(2*a) < L) :
    ∀ t : ℝ, 0 ≤ t → (brakingPath a x v ha hv).position t < L := by
  intro t ht
  exact (actual_braking_position_is_bounded_by_its_stopping_peak a x v t ha).trans_lt hpeak

theorem actual_nonpositive_velocity_zero_input_path_is_safe
    (a L x v : ℝ) (ha : 0 ≤ a) (hx : x < L) (hv : v ≤ 0) :
    ∀ t : ℝ, 0 ≤ t → (zeroInputPath a x v ha).position t < L := by
  intro t ht
  change x + v*t < L
  exact (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hv ht] : x + v*t ≤ x).trans_lt hx

/-- Exact viability iff for the closed wall failure set; equality of stopping
peak and wall is correctly excluded. All admissible controllers were quantified
in the necessary direction, and legal actual controls attain the converse. -/
theorem actual_all_controller_double_integrator_viability_iff
    (a L x v : ℝ) (ha : 0 < a) :
    Viable a L x v ↔ (x,v) ∈ printedKernel a L := by
  constructor
  · exact every_actual_viable_state_has_the_printed_kernel_conditions a L x v ha
  · rintro ⟨hx, hv | hpeak⟩
    · exact ⟨zeroInputPath a x v ha.le,
        actual_nonpositive_velocity_zero_input_path_is_safe a L x v ha.le hx hv⟩
    · by_cases hv : 0 ≤ v
      · exact ⟨brakingPath a x v ha hv,
          actual_braking_path_is_safe_under_strict_stopping_clearance a L x v ha hv hpeak⟩
      · exact ⟨zeroInputPath a x v ha.le,
          actual_nonpositive_velocity_zero_input_path_is_safe a L x v ha.le hx (le_of_not_ge hv)⟩

/-- Both velocity and position are actually constant after the attained braking
stop; this also identifies its exact stopping peak. -/
theorem actual_braking_path_after_stop
    (a x v t : ℝ) (ha : 0 < a) (ht : v/a ≤ t) :
    brakingVelocity a v t = 0 ∧ brakingPosition a x v t = x + v^2/(2*a) := by
  simp only [brakingVelocity, brakingPosition, brakingTime, min_eq_right ht]
  constructor <;> field_simp <;> ring

end SafeLearning.CompleteAppliedDoubleIntegratorWall27
