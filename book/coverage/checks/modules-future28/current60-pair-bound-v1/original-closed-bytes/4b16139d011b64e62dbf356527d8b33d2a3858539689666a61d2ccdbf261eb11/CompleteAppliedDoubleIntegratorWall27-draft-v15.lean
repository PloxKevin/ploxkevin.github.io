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
          (try dsimp [brakingPosition]) <;> ring
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


/-- The displayed quadratic root is the first wall hit of the actual maximally
braking path; equality with stopping time holds exactly on the boundary. -/
theorem actual_braking_first_wall_hit_root
    (a L x v : ℝ) (ha : 0 < a) (hx : x < L) (hv : 0 < v)
    (hpeak : L ≤ x + v^2/(2*a)) :
    let r := (v - Real.sqrt (v^2 - 2*a*(L-x)))/a
    0 < r ∧ r ≤ v/a ∧ brakingPosition a x v r = L ∧
      (∀ t : ℝ, 0 ≤ t → t < r → brakingPosition a x v t < L) ∧
      (r = v/a ↔ x + v^2/(2*a) = L) := by
  let D := v^2 - 2*a*(L-x)
  let r := (v - Real.sqrt D)/a
  change 0 < r ∧ r ≤ v/a ∧ brakingPosition a x v r = L ∧ _ ∧ _
  have hD : 0 ≤ D := by
    have hh : L-x ≤ v^2/(2*a) := by linarith
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*a)).mp hh
    dsimp [D]; nlinarith
  have hDlt : D < v^2 := by
    dsimp [D]; nlinarith [mul_pos ha (sub_pos.mpr hx)]
  have hs := Real.sqrt_nonneg D
  have hslt : Real.sqrt D < v := (Real.sqrt_lt hD hv.le).mpr hDlt
  have hrpos : 0 < r := div_pos (sub_pos.mpr hslt) ha
  have hrle : r ≤ v/a := (div_le_div_iff_of_pos_right ha).mpr (by linarith)
  have har : a*r ≤ v := by
    have hh := (le_div_iff₀ ha).mp hrle
    nlinarith
  have hroot : brakingPosition a x v r = L := by
    unfold brakingPosition brakingTime
    rw [min_eq_left hrle]
    have he : 2*a*(x + v*r - (a/2)*(r*r) - L) = D - (Real.sqrt D)^2 := by
      dsimp [r,D]
      field_simp
      ring
    rw [Real.sq_sqrt hD] at he
    nlinarith
  refine ⟨hrpos, hrle, hroot, ?_, ?_⟩
  · intro t ht htr
    have htstop : t ≤ v/a := htr.le.trans hrle
    have hfactor : 0 < v - (a/2)*(r+t) := by
      nlinarith [mul_pos ha (sub_pos.mpr htr)]
    have hprod := mul_pos (sub_pos.mpr htr) hfactor
    have he : brakingPosition a x v r - brakingPosition a x v t =
        (r-t)*(v - (a/2)*(r+t)) := by
      unfold brakingPosition brakingTime
      rw [min_eq_left hrle, min_eq_left htstop]
      ring
    rw [hroot] at he
    linarith
  · have hsq := Real.sq_sqrt hD
    constructor
    · intro he
      have hzero : Real.sqrt D = 0 := by
        have hh : (v - Real.sqrt D)/a = v/a := he
        have hh' := (div_left_inj' ha.ne').mp hh
        linarith
      rw [hzero] at hsq
      have hDzero : D = 0 := by nlinarith
      dsimp [D] at hDzero
      field_simp
      nlinarith
    · intro he
      have hDzero : D = 0 := by
        have hh : v^2/(2*a) = L-x := by linarith
        have hh' := (div_eq_iff (by positivity : (2*a:ℝ) ≠ 0)).mp hh
        dsimp [D]; nlinarith
      change (v-Real.sqrt D)/a = v/a
      rw [hDzero, Real.sqrt_zero, sub_zero]

/-- On the boundary family, braking touches the closed failure wall exactly at
T, with every earlier nonnegative time strictly safe. -/
theorem actual_boundary_braking_family_first_hit
    (a L T : ℝ) (ha : 0 < a) (hT : 0 < T) :
    let x := L - (a/2)*T^2
    let v := a*T
    ¬ Viable a L x v ∧
      brakingPosition a x v T = L ∧
      (∀ t : ℝ, 0 ≤ t → t < T → brakingPosition a x v t < L) := by
  let x := L - (a/2)*T^2
  let v := a*T
  have hx : x < L := by dsimp [x]; nlinarith [sq_pos_of_pos hT]
  have hv : 0 < v := mul_pos ha hT
  have hpeak : x + v^2/(2*a) = L := by dsimp [x,v]; field_simp; ring
  have hstop : v/a = T := by dsimp [v]; field_simp
  have hr := actual_braking_first_wall_hit_root a L x v ha hx hv hpeak.ge
  dsimp only at hr
  have hroot : (v - Real.sqrt (v^2-2*a*(L-x)))/a = T := (hr.2.2.2.2.mpr hpeak).trans hstop
  refine ⟨?_, ?_, ?_⟩
  · intro hviable
    have hK := every_actual_viable_state_has_the_printed_kernel_conditions a L x v ha hviable
    rcases hK.2 with hneg | hlt
    · exact (not_le_of_gt hv) hneg
    · exact (not_lt_of_ge hpeak.ge) hlt
  · simpa only [hroot] using hr.2.2.1
  · intro t ht hlt
    exact hr.2.2.2.1 t ht (by simpa only [hroot] using hlt)

/-- There is no uniform finite failure horizon without an initial velocity
bound: actual unviable boundary trajectories can stay safe past any finite bound. -/
theorem actual_unbounded_initial_velocities_preclude_uniform_failure_horizon
    (a L Tf : ℝ) (ha : 0 < a) (hTf : 0 ≤ Tf) :
    ∃ x v : ℝ, ¬ Viable a L x v ∧
      ∃ P : ControlledPath a x v, ∀ t : ℝ, 0 ≤ t → t ≤ Tf → P.position t < L := by
  let T := Tf+1
  have hT : 0 < T := by dsimp [T]; linarith
  let x := L - (a/2)*T^2
  let v := a*T
  have hf := actual_boundary_braking_family_first_hit a L T ha hT
  refine ⟨x, v, hf.1, brakingPath a x v ha (mul_nonneg ha.le hT.le), ?_⟩
  intro t ht htTf
  exact hf.2.2 t ht (by dsimp [T]; linarith)


private theorem actual_path_ac_subinterval
    (a x v s t : ℝ) (P : ControlledPath a x v) (hs : 0 ≤ s) (hst : s ≤ t) :
    AbsolutelyContinuousOnInterval P.position s t ∧
      AbsolutelyContinuousOnInterval P.velocity s t := by
  have hsub : uIcc s t ⊆ uIcc 0 t := by
    rw [uIcc_of_le hst, uIcc_of_le (hs.trans hst)]
    intro r hr
    exact ⟨hs.trans hr.1, hr.2⟩
  exact ⟨(P.position_ac t (hs.trans hst)).mono hsub,
    (P.velocity_ac t (hs.trans hst)).mono hsub⟩

theorem actual_velocity_change_has_the_braking_lower_bound
    (a x v s t : ℝ) (P : ControlledPath a x v) (hs : 0 ≤ s) (hst : s ≤ t) :
    P.velocity s - a*(t-s) ≤ P.velocity t := by
  have hac := (actual_path_ac_subinterval a x v s t P hs hst).2
  have hmono : (∫ r : ℝ in s..t, (-a : ℝ)) ≤ ∫ r : ℝ in s..t, deriv P.velocity r := by
    apply intervalIntegral.integral_mono_ae_restrict hst intervalIntegrable_const hac.intervalIntegrable_deriv
    filter_upwards [ae_restrict_of_ae P.derivatives_ae,
      ae_restrict_mem measurableSet_Icc] with r hr hmem
    rw [(hr (hs.trans hmem.1)).2.deriv]
    exact (abs_le.mp (P.input_bound r (hs.trans hmem.1))).1
  rw [intervalIntegral.integral_const, hac.integral_deriv_eq_sub] at hmono
  simp only [smul_eq_mul] at hmono
  nlinarith

private theorem braking_velocity_integral_subinterval (a w s t : ℝ) :
    (∫ r : ℝ in s..t, w - a*(r-s)) = w*(t-s) - a*(t-s)^2/2 := by
  have hfun : (fun r : ℝ => w-a*(r-s)) = (fun r : ℝ => (w+a*s)-a*r) := by
    ext r; ring
  rw [hfun]
  have hi : IntervalIntegrable (fun r : ℝ => a*r) volume s t :=
    (by fun_prop : Continuous (fun r : ℝ => a*r)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

theorem actual_position_change_has_the_braking_lower_bound
    (a x v s t : ℝ) (P : ControlledPath a x v) (hs : 0 ≤ s) (hst : s ≤ t) :
    P.position s + P.velocity s*(t-s) - a*(t-s)^2/2 ≤ P.position t := by
  have hac := (actual_path_ac_subinterval a x v s t P hs hst).1
  have hi : IntervalIntegrable (fun r : ℝ => P.velocity s-a*(r-s)) volume s t :=
    (by fun_prop : Continuous (fun r : ℝ => P.velocity s-a*(r-s))).intervalIntegrable _ _
  have hmono : (∫ r : ℝ in s..t, P.velocity s-a*(r-s)) ≤
      ∫ r : ℝ in s..t, deriv P.position r := by
    apply intervalIntegral.integral_mono_ae_restrict hst hi hac.intervalIntegrable_deriv
    filter_upwards [ae_restrict_of_ae P.derivatives_ae,
      ae_restrict_mem measurableSet_Icc] with r hr hmem
    rw [(hr (hs.trans hmem.1)).1.deriv]
    exact actual_velocity_change_has_the_braking_lower_bound a x v s r P hs hmem.1
  rw [braking_velocity_integral_subinterval, hac.integral_deriv_eq_sub] at hmono
  linarith

/-- Every point along an actual globally safe continuation satisfies the kernel
conditions, derived by the arbitrary-control comparison at that point. -/
theorem actual_safe_continuation_has_kernel_at_every_time
    (a L x v s : ℝ) (P : ControlledPath a x v) (ha : 0 < a) (hs : 0 ≤ s)
    (hsafe : ∀ t : ℝ, 0 ≤ t → P.position t < L) :
    (P.position s, P.velocity s) ∈ printedKernel a L := by
  refine ⟨hsafe s hs, ?_⟩
  by_cases hv : P.velocity s ≤ 0
  · exact Or.inl hv
  · right
    have hvs : 0 < P.velocity s := lt_of_not_ge hv
    have ht : s ≤ s + P.velocity s/a := le_add_of_nonneg_right (div_nonneg hvs.le ha.le)
    have hp := actual_position_change_has_the_braking_lower_bound a x v s
      (s+P.velocity s/a) P hs ht
    have he : P.position s + P.velocity s*((s+P.velocity s/a)-s) -
        a*((s+P.velocity s/a)-s)^2/2 = P.position s + (P.velocity s)^2/(2*a) := by
      field_simp; ring
    rw [he] at hp
    exact hp.trans_lt (hsafe _ (hs.trans ht))

/-- Actual safe hold actions quantify over a bounded-input AC/AE-ODE
continuation. Held input is imposed only almost everywhere, as required by the
physical ODE, and is not a supplied viability or measure conclusion. -/
def heldContinuationActions (a L x v Delta : ℝ) : Set ℝ :=
  {u | |u| ≤ a ∧ ∃ P : ControlledPath a x v,
    (∀ᵐ t : ℝ ∂volume, 0 ≤ t → t ≤ Delta → P.input t = u) ∧
    (∀ t : ℝ, 0 ≤ t → P.position t < L)}

theorem actual_held_input_implies_the_polynomial_state
    (a x v Delta u t : ℝ) (P : ControlledPath a x v) (ht : 0 ≤ t) (htD : t ≤ Delta)
    (hheld : ∀ᵐ s : ℝ ∂volume, 0 ≤ s → s ≤ Delta → P.input s = u) :
    P.velocity t = v+u*t ∧ P.position t = x+v*t+(u/2)*t^2 := by
  have hv : ∀ r : ℝ, 0 ≤ r → r ≤ Delta → P.velocity r = v+u*r := by
    intro r hr hrD
    have he : (∫ s : ℝ in 0..r, P.input s) = ∫ s : ℝ in 0..r, u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hheld] with s hs hmem
      rw [uIoc_of_le hr] at hmem
      exact hs hmem.1.le (hmem.2.trans hrD)
    rw [actual_velocity_integral a x v r P hr, intervalIntegral.integral_const] at he
    simp only [sub_zero, smul_eq_mul] at he
    linarith
  refine ⟨hv t ht htD, ?_⟩
  have he : (∫ r : ℝ in 0..t, P.velocity r) = ∫ r : ℝ in 0..t, v-(-u)*r := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r hmem
    rw [uIoc_of_le ht] at hmem
    rw [hv r hmem.1.le (hmem.2.trans htD)]
    ring
  rw [actual_position_integral a x v t P ht, actual_integral_of_the_braking_velocity] at he
  nlinarith

/-- A constant bounded input gives an actual trajectory, used for attained safe
intervals in the action measure lower bound. -/
def constantInputPath (a x v u : ℝ) (hu : |u| ≤ a) : ControlledPath a x v where
  position := fun t => x+v*t+(u/2)*t^2
  velocity := fun t => v+u*t
  input := fun _ => u
  position_zero := by simp
  velocity_zero := by simp
  input_measurable := measurable_const
  input_bound := by intro t ht; exact hu
  position_ac := by
    intro T hT
    exact (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => x+v*t+(u/2)*t^2)).contDiffOn.absolutelyContinuousOnInterval
  velocity_ac := by
    intro T hT
    exact (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => v+u*t)).contDiffOn.absolutelyContinuousOnInterval
  derivatives_ae := by
    filter_upwards with t
    intro ht
    constructor
    · have hp := ((hasDerivAt_const t x).add ((hasDerivAt_id t).const_mul v)).add
        (((hasDerivAt_id t).pow 2).const_mul (u/2))
      convert hp using 1 <;> (try ext r) <;> dsimp <;> ring
    · convert (hasDerivAt_const t v).add ((hasDerivAt_id t).const_mul u) using 1 <;>
        (try ext r) <;> simp

theorem actual_nonpositive_constant_inputs_give_safe_hold_actions
    (a L x v Delta u : ℝ) (hx : x < L) (hv : v ≤ 0) (hu : u ≤ 0) (hbound : |u| ≤ a) :
    u ∈ heldContinuationActions a L x v Delta := by
  refine ⟨hbound, constantInputPath a x v u hbound, ?_, ?_⟩
  · filter_upwards with t
    intro ht htD
    rfl
  · intro t ht
    change x+v*t+(u/2)*t^2 < L
    have hvt := mul_nonpos_of_nonpos_of_nonneg hv ht
    have hut := mul_nonpos_of_nonpos_of_nonneg (show u/2 ≤ 0 by linarith) (sq_nonneg t)
    linarith

/-- The printed positive-action inequality is derived as a necessary condition
from an actual safe held trajectory and its actual future continuation. -/
theorem actual_wall_rest_positive_hold_inequality
    (a L epsilon Delta u : ℝ) (ha : 0 < a) (hD : 0 < Delta) (hu : 0 < u)
    (hmem : u ∈ heldContinuationActions a L (L-epsilon) 0 Delta) :
    u+u^2/a < 2*epsilon/Delta^2 := by
  obtain ⟨hb, P, hheld, hsafe⟩ := hmem
  have hp := actual_held_input_implies_the_polynomial_state a (L-epsilon) 0 Delta u Delta P hD.le le_rfl hheld
  have hK := actual_safe_continuation_has_kernel_at_every_time a L (L-epsilon) 0 Delta P ha hD.le hsafe
  have hv : 0 < P.velocity Delta := by rw [hp.1]; nlinarith
  have hpeak : P.position Delta+(P.velocity Delta)^2/(2*a) < L :=
    hK.2.resolve_left (not_le_of_gt hv)
  rw [hp.1,hp.2] at hpeak
  have he : L-epsilon+0*Delta+(u/2)*Delta^2 + (0+u*Delta)^2/(2*a) =
      L-epsilon+(Delta^2/2)*(u+u^2/a) := by field_simp; ring
  rw [he] at hpeak
  apply (lt_div_iff₀ (sq_pos_of_pos hD)).mpr
  nlinarith

/-- Actual safe-action outer/Lebesgue measure at rest is squeezed between a
fully attained negative-input interval and an interval whose extra width is O(epsilon). -/
theorem actual_wall_rest_safe_action_measure_bounds
    (a L epsilon Delta : ℝ) (ha : 0 < a) (he : 0 < epsilon) (hD : 0 < Delta) :
    a ≤ volume.real (heldContinuationActions a L (L-epsilon) 0 Delta) ∧
      volume.real (heldContinuationActions a L (L-epsilon) 0 Delta) ≤ a+2*epsilon/Delta^2 := by
  have hl : Icc (-a) 0 ⊆ heldContinuationActions a L (L-epsilon) 0 Delta := by
    intro u hu
    apply actual_nonpositive_constant_inputs_give_safe_hold_actions a L (L-epsilon) 0 Delta u
      (by linarith) le_rfl hu.2
    exact abs_le.mpr ⟨hu.1, hu.2.trans ha.le⟩
  have hu : heldContinuationActions a L (L-epsilon) 0 Delta ⊆ Ico (-a) (2*epsilon/Delta^2) := by
    intro u hum
    refine ⟨(abs_le.mp hum.1).1, ?_⟩
    by_cases hp : 0 < u
    · have hi := actual_wall_rest_positive_hold_inequality a L epsilon Delta u ha hD hp hum
      have hn : 0 ≤ u^2/a := div_nonneg (sq_nonneg u) ha.le
      linarith
    · have hh : 0 < 2*epsilon/Delta^2 := by positivity
      exact (le_of_not_gt hp).trans_lt hh
  have hf : volume (heldContinuationActions a L (L-epsilon) 0 Delta) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Ico (-a) (2*epsilon/Delta^2)) ≠ ⊤ by simp [Real.volume_Ico])
    exact measure_mono hu
  constructor
  · have hh := measureReal_mono hl hf
    rw [Real.volume_real_Icc_of_le (by linarith : -a ≤ (0:ℝ))] at hh
    linarith
  · have hh := measureReal_mono (μ := volume) hu (by simp [Real.volume_Ico])
    have ho : -a ≤ 2*epsilon/Delta^2 := (neg_nonpos.mpr ha.le).trans (by positivity)
    rw [Real.volume_real_Ico_of_le ho] at hh
    linarith

theorem actual_wall_rest_safe_action_measure_tends_to_a
    (a L Delta : ℝ) (ha : 0 < a) (hD : 0 < Delta) :
    Tendsto (fun epsilon : ℝ => volume.real (heldContinuationActions a L (L-epsilon) 0 Delta))
      (𝓝[>] 0) (𝓝 a) := by
  have hlin : Tendsto (fun epsilon : ℝ => a+2*epsilon/Delta^2) (𝓝[>] 0) (𝓝 a) := by
    have hi : Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    convert tendsto_const_nhds.add ((hi.const_mul 2).div_const (Delta^2)) using 1 <;> simp
  apply tendsto_const_nhds.squeeze' hlin
  · filter_upwards [self_mem_nhdsWithin] with epsilon he
    exact (actual_wall_rest_safe_action_measure_bounds a L epsilon Delta ha he hD).1
  · filter_upwards [self_mem_nhdsWithin] with epsilon he
    exact (actual_wall_rest_safe_action_measure_bounds a L epsilon Delta ha he hD).2


/-- The source stopping-point chain rule for an actual held-input polynomial. -/
theorem actual_held_stopping_point_chain_rule (a x v u t : ℝ) (ha : 0 < a) :
    HasDerivAt (fun s : ℝ => x+v*s+(u/2)*s^2 + (v+u*s)^2/(2*a))
      ((v+u*t)*(1+u/a)) t := by
  have hp := ((hasDerivAt_const t x).add ((hasDerivAt_id t).const_mul v)).add
    (((hasDerivAt_id t).pow 2).const_mul (u/2))
  have hv := (hasDerivAt_const t v).add ((hasDerivAt_id t).const_mul u)
  have hh := hp.add ((hv.pow 2).div_const (2*a))
  convert hh using 1 <;> (try ext r) <;> dsimp <;> field_simp <;> ring

/-- Derives the actual O(epsilon) input restriction from the bounded-input ODE,
held-input state, and global safety, with no measure or stopping-point premise. -/
theorem actual_braking_parabola_safe_hold_input_restriction
    (a L v epsilon Delta t : ℝ) (ha : 0 < a) (hv : 0 < v)
    (ht : 0 < t) (htD : t ≤ Delta) (htv : t ≤ v/(2*a))
    (u : ℝ) (hum : u ∈ heldContinuationActions a L (L-epsilon-v^2/(2*a)) v Delta) :
    -a ≤ u ∧ u < -a+2*a*epsilon/(v*t) := by
  obtain ⟨hb, P, hheld, hsafe⟩ := hum
  have hlu : -a ≤ u := (abs_le.mp hb).1
  have hdu : 0 ≤ u+a := by linarith
  have hvt : v/2 ≤ v+u*t := by
    have hat : t*(2*a) ≤ v := (le_div_iff₀ (by positivity : 0 < 2*a)).mp htv
    nlinarith [mul_nonneg hdu ht.le]
  have hp := actual_held_input_implies_the_polynomial_state a (L-epsilon-v^2/(2*a)) v
    Delta u t P ht.le htD hheld
  have hK := actual_safe_continuation_has_kernel_at_every_time a L (L-epsilon-v^2/(2*a)) v
    t P ha ht.le hsafe
  have hvP : 0 < P.velocity t := by rw [hp.1]; linarith
  have hpeak := hK.2.resolve_left (not_le_of_gt hvP)
  rw [hp.1,hp.2] at hpeak
  have he : (L-epsilon-v^2/(2*a)+v*t+(u/2)*t^2+(v+u*t)^2/(2*a)) - (L-epsilon) -
      v*(u+a)*t/(2*a) = ((u+a)/(2*a))*t*(v+u*t) := by
    field_simp; ring
  have hn : 0 ≤ ((u+a)/(2*a))*t*(v+u*t) := by
    exact mul_nonneg (mul_nonneg (div_nonneg hdu (by positivity)) ht.le) (by linarith)
  have hsmall : v*(u+a)*t/(2*a) < epsilon := by linarith
  have hm := (div_lt_iff₀ (by positivity : 0 < 2*a)).mp hsmall
  refine ⟨hlu, ?_⟩
  have hdelta : u+a < 2*a*epsilon/(v*t) := by
    apply (lt_div_iff₀ (mul_pos hv ht)).mpr
    nlinarith
  linarith

theorem actual_braking_parabola_safe_actions_fit_the_shrinking_interval
    (a L v epsilon Delta : ℝ) (ha : 0 < a) (hv : 0 < v) (hD : 0 < Delta) :
    heldContinuationActions a L (L-epsilon-v^2/(2*a)) v Delta ⊆
      Ico (-a) (-a+2*a*epsilon/(v*min Delta (v/(2*a)))) := by
  intro u hu
  have ht : 0 < min Delta (v/(2*a)) := lt_min hD (by positivity)
  exact actual_braking_parabola_safe_hold_input_restriction a L v epsilon Delta
    (min Delta (v/(2*a))) ha hv ht (min_le_left _ _) (min_le_right _ _) u hu

theorem actual_braking_parabola_safe_action_measure_bounds
    (a L v epsilon Delta : ℝ) (ha : 0 < a) (hv : 0 < v) (he : 0 < epsilon) (hD : 0 < Delta) :
    0 ≤ volume.real (heldContinuationActions a L (L-epsilon-v^2/(2*a)) v Delta) ∧
      volume.real (heldContinuationActions a L (L-epsilon-v^2/(2*a)) v Delta) ≤
        2*a*epsilon/(v*min Delta (v/(2*a))) := by
  refine ⟨measureReal_nonneg, ?_⟩
  have hs := actual_braking_parabola_safe_actions_fit_the_shrinking_interval a L v epsilon Delta ha hv hD
  have hh := measureReal_mono (μ := volume) hs (by simp [Real.volume_Ico])
  have ho : -a ≤ -a+2*a*epsilon/(v*min Delta (v/(2*a))) := le_add_of_nonneg_right (by positivity)
  rw [Real.volume_real_Ico_of_le ho] at hh
  linarith

theorem actual_braking_parabola_safe_action_measure_tends_to_zero
    (a L v Delta : ℝ) (ha : 0 < a) (hv : 0 < v) (hD : 0 < Delta) :
    Tendsto (fun epsilon : ℝ =>
      volume.real (heldContinuationActions a L (L-epsilon-v^2/(2*a)) v Delta))
      (𝓝[>] 0) (𝓝 0) := by
  have hlin : Tendsto (fun epsilon : ℝ => 2*a*epsilon/(v*min Delta (v/(2*a))))
      (𝓝[>] 0) (𝓝 0) := by
    have hi : Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    convert (hi.const_mul (2*a)).div_const (v*min Delta (v/(2*a))) using 1 <;> simp
  apply tendsto_const_nhds.squeeze' hlin
  · exact Eventually.of_forall (fun _ => measureReal_nonneg)
  · filter_upwards [self_mem_nhdsWithin] with epsilon he
    exact (actual_braking_parabola_safe_action_measure_bounds a L v epsilon Delta ha hv he hD).2

/-- Full braking is genuinely attained in every positive-margin hold action set;
combined with the shrinking interval this identifies the unique limiting input. -/
theorem actual_full_braking_is_a_safe_held_action
    (a L x v Delta : ℝ) (ha : 0 < a) (hpeak : x+v^2/(2*a) < L) :
    -a ∈ heldContinuationActions a L x v Delta := by
  have hb : |-a| ≤ a := by simpa [abs_of_pos ha]
  refine ⟨hb, constantInputPath a x v (-a) hb, ?_, ?_⟩
  · filter_upwards with t
    intro ht htD
    rfl
  · intro t ht
    change x+v*t+(-a/2)*t^2 < L
    have he : x+v^2/(2*a) - (x+v*t+(-a/2)*t^2) = (a/2)*(v/a-t)^2 := by
      field_simp; ring
    have hn : 0 ≤ (a/2)*(v/a-t)^2 := by positivity
    linarith


/-- The actual unviable set is exactly the printed union with the closed wall. -/
theorem actual_unviable_state_iff_printed_union
    (a L x v : ℝ) (ha : 0 < a) :
    ¬ Viable a L x v ↔ L ≤ x ∨ (0 < v ∧ L ≤ x+v^2/(2*a)) := by
  rw [actual_all_controller_double_integrator_viability_iff a L x v ha]
  simp only [printedKernel, mem_setOf_eq, not_and_or, not_or, not_lt, not_le]

def wallStoppingBarrier (a : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1+(max z.2 0)^2/(2*a)

theorem actual_kernel_is_the_strict_stopping_barrier_sublevel
    (a L : ℝ) (ha : 0 < a) :
    printedKernel a L = {z | wallStoppingBarrier a z < L} := by
  ext ⟨x,v⟩
  by_cases hv : v ≤ 0
  · simp [printedKernel,wallStoppingBarrier,max_eq_right hv,hv]
  · have hvp : 0 ≤ v := (lt_of_not_ge hv).le
    have hnon : 0 ≤ v^2/(2*a) := by positivity
    simp only [printedKernel,wallStoppingBarrier,mem_setOf_eq,max_eq_left hvp,hv,false_or]
    constructor
    · exact And.right
    · intro hp
      exact ⟨(le_add_of_nonneg_right hnon).trans_lt hp,hp⟩

theorem actual_kernel_closure_is_the_nonstrict_stopping_barrier_sublevel
    (a L : ℝ) (ha : 0 < a) :
    closure (printedKernel a L) = {z | wallStoppingBarrier a z ≤ L} := by
  have hcont : Continuous (wallStoppingBarrier a) := by unfold wallStoppingBarrier; fun_prop
  apply Subset.antisymm
  · apply closure_minimal
    · rw [actual_kernel_is_the_strict_stopping_barrier_sublevel a L ha]
      intro z hz
      exact (show wallStoppingBarrier a z < L from hz).le
    · exact isClosed_le hcont continuous_const
  · intro z hz
    apply Metric.mem_closure_iff.mpr
    intro epsilon he
    let y : ℝ×ℝ := (z.1-epsilon/2,z.2)
    refine ⟨y,?_,?_⟩
    · rw [actual_kernel_is_the_strict_stopping_barrier_sublevel a L ha]
      change wallStoppingBarrier a y < L
      change wallStoppingBarrier a z ≤ L at hz
      dsimp [wallStoppingBarrier,y] at *
      linarith
    · have hd : dist z y = epsilon/2 := by
        simp only [Prod.dist_eq,Real.dist_eq,y,sub_self,abs_zero]
        have hh : z.1-(z.1-epsilon/2) = epsilon/2 := by ring
        rw [hh,abs_of_pos (by positivity),max_eq_left (by positivity)]
      rw [hd]
      linarith

/-- The physical boundary is the positive-velocity braking parabola and the
nonpositive-velocity wall segment, as two distinct approach regimes in part(c). -/
theorem actual_kernel_frontier_is_the_printed_two_piece_boundary
    (a L : ℝ) (ha : 0 < a) :
    frontier (printedKernel a L) =
      {z | (0 < z.2 ∧ z.1+z.2^2/(2*a)=L) ∨ (z.1=L ∧ z.2≤0)} := by
  have hcont : Continuous (wallStoppingBarrier a) := by unfold wallStoppingBarrier; fun_prop
  have hopen : IsOpen (printedKernel a L) := by
    rw [actual_kernel_is_the_strict_stopping_barrier_sublevel a L ha]
    exact isOpen_lt hcont continuous_const
  rw [hopen.frontier_eq, actual_kernel_closure_is_the_nonstrict_stopping_barrier_sublevel a L ha,
    actual_kernel_is_the_strict_stopping_barrier_sublevel a L ha]
  ext ⟨x,v⟩
  simp only [Set.mem_sdiff,Set.mem_setOf_eq,not_lt]
  have heq : wallStoppingBarrier a (x,v) ≤ L ∧ L ≤ wallStoppingBarrier a (x,v) ↔
      wallStoppingBarrier a (x,v) = L := ⟨fun h => le_antisymm h.1 h.2,fun h=>⟨h.le,h.ge⟩⟩
  rw [heq]
  by_cases hv : v ≤ 0
  · simp [wallStoppingBarrier,max_eq_right hv,hv,not_lt_of_ge hv]
  · have hvp : 0 < v := lt_of_not_ge hv
    simp [wallStoppingBarrier,max_eq_left hvp.le,hv,hvp]


/-- The displayed smaller root is an actual all-controller failure deadline,
not merely the first hit of the chosen maximally braking trajectory. -/
theorem actual_every_control_fails_by_the_displayed_first_root
    (a L x v : ℝ) (ha : 0 < a) (hx : x < L) (hv : 0 < v)
    (hpeak : L ≤ x+v^2/(2*a)) (P : ControlledPath a x v) :
    let r := (v-Real.sqrt (v^2-2*a*(L-x)))/a
    L ≤ P.position r := by
  have hr := actual_braking_first_wall_hit_root a L x v ha hx hv hpeak
  dsimp only at hr ⊢
  have hp := every_actual_control_position_has_the_braking_lower_bound a x v
    ((v-Real.sqrt (v^2-2*a*(L-x)))/a) P hr.1.le
  have he := hr.2.2.1
  simp only [brakingPosition, brakingTime, min_eq_left hr.2.1] at he
  nlinarith

/-- The attained braking input is an actual stationary velocity feedback. -/
theorem actual_braking_input_is_the_stationary_feedback
    (a v t : ℝ) (ha : 0 < a) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    brakingInput a v t = if 0 < brakingVelocity a v t then -a else 0 := by
  by_cases hbefore : t < v/a
  · have hvpos : 0 < brakingVelocity a v t := by
      simp only [brakingVelocity, brakingTime, min_eq_left hbefore.le]
      have hh := (lt_div_iff₀ ha).mp hbefore
      nlinarith
    simp [brakingInput,hbefore,hvpos]
  · have hvzero : brakingVelocity a v t = 0 := by
      simp only [brakingVelocity,brakingTime,min_eq_right (le_of_not_gt hbefore)]
      field_simp;ring
    simp [brakingInput,hbefore,hvzero]

def holdBrakeTime (a v u Delta t : ℝ) : ℝ :=
  min (max (t-Delta) 0) ((v+u*Delta)/a)
def holdBrakePosition (a x v u Delta t : ℝ) : ℝ :=
  x+v*min t Delta+(u/2)*(min t Delta)^2 +
    (v+u*Delta)*holdBrakeTime a v u Delta t - (a/2)*(holdBrakeTime a v u Delta t)^2
def holdBrakeVelocity (a v u Delta t : ℝ) : ℝ :=
  v+u*min t Delta-a*holdBrakeTime a v u Delta t
def holdBrakeInput (a v u Delta t : ℝ) : ℝ :=
  if t < Delta then u else if t < Delta+(v+u*Delta)/a then -a else 0

private theorem holdBrakeTime_ac (a v u Delta T : ℝ) :
    AbsolutelyContinuousOnInterval (holdBrakeTime a v u Delta) 0 T := by
  have hs : AbsolutelyContinuousOnInterval (fun t : ℝ => t-Delta) 0 T :=
    (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => t-Delta)).contDiffOn.absolutelyContinuousOnInterval
  exact ((LipschitzWith.id.max_const 0).min_const ((v+u*Delta)/a)).comp_absolutelyContinuousOnInterval hs

private theorem holdBrakeTime_hasDeriv_before
    (a v u Delta t : ℝ) (ha : 0 < a) (hw : 0 ≤ v+u*Delta) (ht : t < Delta) :
    HasDerivAt (holdBrakeTime a v u Delta) 0 t := by
  apply (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds ht] with y hy
  simp [holdBrakeTime,max_eq_right (sub_nonpos.mpr hy.le),
    min_eq_left (div_nonneg hw ha.le)]

private theorem holdBrakeTime_hasDeriv_middle
    (a v u Delta t : ℝ) (ht : Delta < t) (hs : t < Delta+(v+u*Delta)/a) :
    HasDerivAt (holdBrakeTime a v u Delta) 1 t := by
  apply ((hasDerivAt_id t).sub_const Delta).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht,eventually_lt_nhds hs] with y hy hy'
  simp only [holdBrakeTime,max_eq_left (sub_nonneg.mpr hy.le)]
  exact min_eq_left (by linarith)

private theorem holdBrakeTime_hasDeriv_after
    (a v u Delta t : ℝ) (hw : 0 ≤ (v+u*Delta)/a)
    (ht : Delta+(v+u*Delta)/a < t) :
    HasDerivAt (holdBrakeTime a v u Delta) 0 t := by
  apply (hasDerivAt_const t ((v+u*Delta)/a)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with y hy
  have hyD : Delta ≤ y := by linarith
  simp only [holdBrakeTime,max_eq_left (sub_nonneg.mpr hyD)]
  exact min_eq_right (by linarith)

/-- A held input followed by actual full braking and zero input is a legal
measurable bounded-input AC/AE-ODE continuation when its terminal velocity is
nonnegative. No safety or endpoint viability is a field of this constructor. -/
def holdThenBrakePath (a x v u Delta : ℝ) (ha : 0 < a) (hD : 0 < Delta)
    (hu : |u| ≤ a) (hw : 0 ≤ v+u*Delta) : ControlledPath a x v where
  position := holdBrakePosition a x v u Delta
  velocity := holdBrakeVelocity a v u Delta
  input := holdBrakeInput a v u Delta
  position_zero := by
    simp [holdBrakePosition,holdBrakeTime,min_eq_left hD.le,
      max_eq_right (show -Delta ≤ 0 by linarith),min_eq_left (div_nonneg hw ha.le)]
  velocity_zero := by
    simp [holdBrakeVelocity,holdBrakeTime,min_eq_left hD.le,
      max_eq_right (show -Delta ≤ 0 by linarith),min_eq_left (div_nonneg hw ha.le)]
  input_measurable := by
    exact Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const)
  input_bound := by
    intro t ht
    simp only [holdBrakeInput]
    split_ifs
    · exact hu
    · simp [abs_of_nonneg ha.le]
    · simp [ha.le]
  position_ac := by
    intro T hT
    have hh : AbsolutelyContinuousOnInterval (fun t : ℝ => min t Delta) 0 T :=
      (LipschitzWith.id.min_const Delta).lipschitzOnWith.absolutelyContinuousOnInterval
    have hq := holdBrakeTime_ac a v u Delta T
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => x) 0 T :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => x)).contDiffOn.absolutelyContinuousOnInterval
    simpa only [holdBrakePosition,pow_two] using
      (((hc.fun_add (hh.const_mul v)).fun_add ((hh.fun_mul hh).const_mul (u/2))).fun_add
        (hq.const_mul (v+u*Delta))).fun_sub ((hq.fun_mul hq).const_mul (a/2))
  velocity_ac := by
    intro T hT
    have hh : AbsolutelyContinuousOnInterval (fun t : ℝ => min t Delta) 0 T :=
      (LipschitzWith.id.min_const Delta).lipschitzOnWith.absolutelyContinuousOnInterval
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => v) 0 T :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => v)).contDiffOn.absolutelyContinuousOnInterval
    exact (hc.fun_add (hh.const_mul u)).fun_sub ((holdBrakeTime_ac a v u Delta T).const_mul a)
  derivatives_ae := by
    filter_upwards [volume.ae_ne Delta,volume.ae_ne (Delta+(v+u*Delta)/a)] with t htD htS
    intro ht
    rcases lt_or_gt_of_ne htD with hbefore | hafter
    · have hh := brakingTime_hasDeriv_before 1 Delta t (by simpa using hbefore)
      simp only [brakingTime,div_one] at hh
      have hq := holdBrakeTime_hasDeriv_before a v u Delta t ha hw hbefore
      have hqzero : holdBrakeTime a v u Delta t = 0 := by
        simp [holdBrakeTime,max_eq_right (sub_nonpos.mpr hbefore.le),min_eq_left (div_nonneg hw ha.le)]
      constructor
      · have hp := (((hasDerivAt_const t x).add (hh.const_mul v)).add ((hh.pow 2).const_mul (u/2))).add
          (hq.const_mul (v+u*Delta)) |>.sub ((hq.pow 2).const_mul (a/2))
        convert hp using 1 <;> (try ext y) <;>
          (try dsimp [holdBrakePosition,holdBrakeVelocity,brakingTime]) <;>
          (try rw [hqzero]) <;> ring
      · have hvel := ((hasDerivAt_const t v).add (hh.const_mul u)).sub (hq.const_mul a)
        convert hvel using 1 <;> (try ext y) <;>
          simp [holdBrakeVelocity,holdBrakeInput,brakingTime,hbefore]
    · have hh := brakingTime_hasDeriv_after 1 Delta t (by simpa using hafter)
      simp only [brakingTime,div_one] at hh
      rcases lt_or_gt_of_ne htS with hmiddle | hdone
      · have hq := holdBrakeTime_hasDeriv_middle a v u Delta t hafter hmiddle
        constructor
        · have hp := (((hasDerivAt_const t x).add (hh.const_mul v)).add ((hh.pow 2).const_mul (u/2))).add
            (hq.const_mul (v+u*Delta)) |>.sub ((hq.pow 2).const_mul (a/2))
          convert hp using 1 <;> (try ext y) <;>
            (try dsimp [holdBrakePosition,holdBrakeVelocity,brakingTime]) <;>
            (try rw [min_eq_right hafter.le]) <;> ring
        · have hvel := ((hasDerivAt_const t v).add (hh.const_mul u)).sub (hq.const_mul a)
          convert hvel using 1 <;> (try ext y) <;>
            simp [holdBrakeVelocity,holdBrakeInput,brakingTime,not_lt_of_ge hafter.le,hmiddle]
      · have hq := holdBrakeTime_hasDeriv_after a v u Delta t (div_nonneg hw ha.le) hdone
        have hqval : holdBrakeTime a v u Delta t = (v+u*Delta)/a := by
          simp only [holdBrakeTime,max_eq_left (sub_nonneg.mpr hafter.le),min_eq_right (by linarith : (v+u*Delta)/a ≤ t-Delta)]
        have hvzero : holdBrakeVelocity a v u Delta t = 0 := by
          simp only [holdBrakeVelocity,min_eq_right hafter.le,hqval]
          field_simp;ring
        constructor
        · have hp := (((hasDerivAt_const t x).add (hh.const_mul v)).add ((hh.pow 2).const_mul (u/2))).add
            (hq.const_mul (v+u*Delta)) |>.sub ((hq.pow 2).const_mul (a/2))
          rw [hvzero]
          convert hp using 1 <;> (try ext y) <;> (try dsimp [holdBrakePosition,brakingTime]) <;> ring
        · have hvel := ((hasDerivAt_const t v).add (hh.const_mul u)).sub (hq.const_mul a)
          convert hvel using 1 <;> (try ext y) <;>
            simp [holdBrakeVelocity,holdBrakeInput,brakingTime,not_lt_of_ge hafter.le,not_lt_of_ge hdone.le]

theorem actual_held_then_braking_path_is_safe
    (a L x v u Delta : ℝ) (ha : 0 < a) (hD : 0 < Delta)
    (hw : 0 ≤ v+u*Delta)
    (hprefix : ∀ t : ℝ, 0 ≤ t → t ≤ Delta → x+v*t+(u/2)*t^2 < L)
    (hpeak : x+v*Delta+(u/2)*Delta^2+(v+u*Delta)^2/(2*a) < L) :
    ∀ t : ℝ, 0 ≤ t → holdBrakePosition a x v u Delta t < L := by
  intro t ht
  by_cases htD : t ≤ Delta
  · have hqzero : holdBrakeTime a v u Delta t = 0 := by
      simp [holdBrakeTime,max_eq_right (sub_nonpos.mpr htD),min_eq_left (div_nonneg hw ha.le)]
    simpa [holdBrakePosition,min_eq_left htD,hqzero] using hprefix t ht htD
  · have htD' : Delta ≤ t := (lt_of_not_ge htD).le
    have he : holdBrakePosition a x v u Delta t =
        x+v*Delta+(u/2)*Delta^2+brakingPosition a 0 (v+u*Delta) (t-Delta) := by
      simp only [holdBrakePosition,min_eq_right htD',holdBrakeTime,
        max_eq_left (sub_nonneg.mpr htD'),brakingPosition,brakingTime]
      ring
    have hb := actual_braking_position_is_bounded_by_its_stopping_peak a 0 (v+u*Delta) (t-Delta) ha
    rw [he];linarith

/-- The positive-input rest criterion is sufficient through an actual legal
held-input and braking continuation, as well as necessary. -/
theorem actual_wall_rest_positive_hold_iff
    (a L epsilon Delta u : ℝ) (ha : 0 < a) (he : 0 < epsilon)
    (hD : 0 < Delta) (hu : 0 < u) (hbound : |u| ≤ a) :
    u ∈ heldContinuationActions a L (L-epsilon) 0 Delta ↔
      u+u^2/a < 2*epsilon/Delta^2 := by
  constructor
  · exact actual_wall_rest_positive_hold_inequality a L epsilon Delta u ha hD hu
  · intro hi
    have hi' := (lt_div_iff₀ (sq_pos_of_pos hD)).mp hi
    have hpeak : L-epsilon+0*Delta+(u/2)*Delta^2+(0+u*Delta)^2/(2*a) < L := by
      have hid : (u+u^2/a)*Delta^2 = 2*((u/2)*Delta^2+(u*Delta)^2/(2*a)) := by field_simp;ring
      nlinarith
    have hpref : ∀ t : ℝ, 0 ≤ t → t ≤ Delta → L-epsilon+0*t+(u/2)*t^2 < L := by
      intro t ht htD
      have hs : t^2 ≤ Delta^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hs (hu.le : 0 ≤ u)
      have htail := div_nonneg (sq_nonneg (u*Delta)) (by positivity : 0 ≤ 2*a)
      nlinarith
    refine ⟨hbound,holdThenBrakePath a (L-epsilon) 0 u Delta ha hD hbound (by positivity),?_,?_⟩
    · filter_upwards [volume.ae_ne Delta] with t htne
      intro ht htD
      change holdBrakeInput a 0 u Delta t = u
      simp [holdBrakeInput,lt_of_le_of_ne htD htne]
    · exact actual_held_then_braking_path_is_safe a L (L-epsilon) 0 u Delta ha hD
        (by positivity) hpref hpeak


def holdZeroPosition (x v u Delta t : ℝ) : ℝ :=
  x+v*min t Delta+(u/2)*(min t Delta)^2 + (v+u*Delta)*max (t-Delta) 0
def holdZeroVelocity (v u Delta t : ℝ) : ℝ := v+u*min t Delta
def holdZeroInput (u Delta t : ℝ) : ℝ := if t < Delta then u else 0

private theorem holdZeroTail_ac (Delta T : ℝ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => max (t-Delta) 0) 0 T := by
  exact (LipschitzWith.id.max_const 0).comp_absolutelyContinuousOnInterval
    ((by fun_prop : ContDiff ℝ 1 (fun t : ℝ => t-Delta)).contDiffOn.absolutelyContinuousOnInterval)

private theorem holdZeroTail_hasDeriv_before (Delta t : ℝ) (ht : t < Delta) :
    HasDerivAt (fun s : ℝ => max (s-Delta) 0) 0 t := by
  apply (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds ht] with y hy
  exact max_eq_right (sub_nonpos.mpr hy.le)

private theorem holdZeroTail_hasDeriv_after (Delta t : ℝ) (ht : Delta < t) :
    HasDerivAt (fun s : ℝ => max (s-Delta) 0) 1 t := by
  apply ((hasDerivAt_id t).sub_const Delta).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with y hy
  exact max_eq_left (sub_nonneg.mpr hy.le)

/-- The other legal continuation: hold u and then use zero input. Safety of its
nonpositive terminal velocity is derived separately, not assumed here. -/
def holdThenZeroPath (a x v u Delta : ℝ) (ha : 0 ≤ a) (hD : 0 < Delta)
    (hu : |u| ≤ a) : ControlledPath a x v where
  position := holdZeroPosition x v u Delta
  velocity := holdZeroVelocity v u Delta
  input := holdZeroInput u Delta
  position_zero := by simp [holdZeroPosition,min_eq_left hD.le,max_eq_right (show -Delta ≤ 0 by linarith)]
  velocity_zero := by simp [holdZeroVelocity,min_eq_left hD.le]
  input_measurable := Measurable.ite measurableSet_Iio measurable_const measurable_const
  input_bound := by
    intro t ht
    simp only [holdZeroInput]
    split_ifs
    · exact hu
    · simpa using ha
  position_ac := by
    intro T hT
    have hh : AbsolutelyContinuousOnInterval (fun t : ℝ => min t Delta) 0 T :=
      (LipschitzWith.id.min_const Delta).lipschitzOnWith.absolutelyContinuousOnInterval
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => x) 0 T :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => x)).contDiffOn.absolutelyContinuousOnInterval
    simpa only [holdZeroPosition,pow_two] using
      ((hc.fun_add (hh.const_mul v)).fun_add ((hh.fun_mul hh).const_mul (u/2))).fun_add
        ((holdZeroTail_ac Delta T).const_mul (v+u*Delta))
  velocity_ac := by
    intro T hT
    have hh : AbsolutelyContinuousOnInterval (fun t : ℝ => min t Delta) 0 T :=
      (LipschitzWith.id.min_const Delta).lipschitzOnWith.absolutelyContinuousOnInterval
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => v) 0 T :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => v)).contDiffOn.absolutelyContinuousOnInterval
    exact hc.fun_add (hh.const_mul u)
  derivatives_ae := by
    filter_upwards [volume.ae_ne Delta] with t htne
    intro ht
    rcases lt_or_gt_of_ne htne with hbefore | hafter
    · have hh := brakingTime_hasDeriv_before 1 Delta t (by simpa using hbefore)
      simp only [brakingTime,div_one] at hh
      have hq := holdZeroTail_hasDeriv_before Delta t hbefore
      constructor
      · have hp := (((hasDerivAt_const t x).add (hh.const_mul v)).add ((hh.pow 2).const_mul (u/2))).add
          (hq.const_mul (v+u*Delta))
        convert hp using 1 <;> (try ext y) <;> dsimp [holdZeroPosition,holdZeroVelocity] <;> ring
      · have hv := (hasDerivAt_const t v).add (hh.const_mul u)
        convert hv using 1 <;> (try ext y) <;> simp [holdZeroVelocity,holdZeroInput,hbefore]
    · have hh := brakingTime_hasDeriv_after 1 Delta t (by simpa using hafter)
      simp only [brakingTime,div_one] at hh
      have hq := holdZeroTail_hasDeriv_after Delta t hafter
      constructor
      · have hp := (((hasDerivAt_const t x).add (hh.const_mul v)).add ((hh.pow 2).const_mul (u/2))).add
          (hq.const_mul (v+u*Delta))
        convert hp using 1 <;> (try ext y) <;> dsimp [holdZeroPosition,holdZeroVelocity] <;>
          (try rw [min_eq_right hafter.le]) <;> ring
      · have hv := (hasDerivAt_const t v).add (hh.const_mul u)
        convert hv using 1 <;> (try ext y) <;>
          simp [holdZeroVelocity,holdZeroInput,not_lt_of_ge hafter.le]

theorem actual_held_then_zero_path_is_safe
    (L x v u Delta : ℝ) (hw : v+u*Delta ≤ 0)
    (hprefix : ∀ t : ℝ, 0 ≤ t → t ≤ Delta → x+v*t+(u/2)*t^2 < L)
    (hD : 0 < Delta) :
    ∀ t : ℝ, 0 ≤ t → holdZeroPosition x v u Delta t < L := by
  intro t ht
  by_cases htD : t ≤ Delta
  · simpa [holdZeroPosition,min_eq_left htD,max_eq_right (sub_nonpos.mpr htD)] using hprefix t ht htD
  · have hD' : Delta ≤ t := (lt_of_not_ge htD).le
    have hm := mul_nonpos_of_nonpos_of_nonneg hw (sub_nonneg.mpr hD')
    have hb := hprefix Delta hD.le le_rfl
    simp only [holdZeroPosition,min_eq_right hD',max_eq_left (sub_nonneg.mpr hD')]
    linarith

/-- Exact actual safe hold-action characterization, including safety DURING the
hold as well as the successor kernel. Both sufficient branches are actual
bounded AC/AE-ODE trajectories, not an assumed concatenation principle. -/
theorem actual_safe_hold_action_iff_prefix_and_successor_kernel
    (a L x v Delta u : ℝ) (ha : 0 < a) (hD : 0 < Delta) :
    u ∈ heldContinuationActions a L x v Delta ↔
      |u| ≤ a ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ Delta → x+v*t+(u/2)*t^2 < L) ∧
      (x+v*Delta+(u/2)*Delta^2,v+u*Delta) ∈ printedKernel a L := by
  constructor
  · rintro ⟨hu,P,hheld,hsafe⟩
    refine ⟨hu,?_,?_⟩
    · intro t ht htD
      have he := actual_held_input_implies_the_polynomial_state a x v Delta u t P ht htD hheld
      simpa only [he.2] using hsafe t ht
    · have he := actual_held_input_implies_the_polynomial_state a x v Delta u Delta P hD.le le_rfl hheld
      simpa only [he.1,he.2] using actual_safe_continuation_has_kernel_at_every_time a L x v Delta P ha hD.le hsafe
  · rintro ⟨hu,hprefix,hK⟩
    by_cases hw : v+u*Delta ≤ 0
    · refine ⟨hu,holdThenZeroPath a x v u Delta ha.le hD hu,?_,?_⟩
      · filter_upwards [volume.ae_ne Delta] with t hne
        intro ht htD
        change holdZeroInput u Delta t = u
        simp [holdZeroInput,lt_of_le_of_ne htD hne]
      · exact actual_held_then_zero_path_is_safe L x v u Delta hw hprefix hD
    · have hpeak := hK.2.resolve_left hw
      refine ⟨hu,holdThenBrakePath a x v u Delta ha hD hu (le_of_not_ge hw),?_,?_⟩
      · filter_upwards [volume.ae_ne Delta] with t hne
        intro ht htD
        change holdBrakeInput a v u Delta t = u
        simp [holdBrakeInput,lt_of_le_of_ne htD hne]
      · exact actual_held_then_braking_path_is_safe a L x v u Delta ha hD (le_of_not_ge hw) hprefix hpeak

/-- The finite held-prefix safety predicate is open in u: violations are the
projection of a genuinely closed subset with compact time factor. -/
theorem actual_held_prefix_safety_set_is_open (L x v Delta : ℝ) :
    IsOpen {u : ℝ | ∀ t : ℝ, 0 ≤ t → t ≤ Delta → x+v*t+(u/2)*t^2 < L} := by
  let C : Set (ℝ × ↥(Icc (0:ℝ) Delta)) :=
    {z | L ≤ x+v*(z.2:ℝ)+(z.1/2)*(z.2:ℝ)^2}
  have hC : IsClosed C := isClosed_le continuous_const (by fun_prop)
  have hp : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
  have he : {u : ℝ | ∀ t : ℝ, 0 ≤ t → t ≤ Delta → x+v*t+(u/2)*t^2 < L} =
      (Prod.fst '' C)ᶜ := by
    ext u
    simp only [mem_setOf_eq,mem_compl_iff,mem_image,not_exists,not_and]
    constructor
    · intro h z hz hzu
      have heq : z.1=u := hzu
      have ht := z.2.property
      have hh := h (z.2:ℝ) ht.1 ht.2
      change L ≤ x+v*(z.2:ℝ)+(z.1/2)*(z.2:ℝ)^2 at hz
      rw [heq] at hz
      linarith
    · intro h t ht htD
      by_contra hn
      have hz : (u,⟨t,ht,htD⟩) ∈ C := le_of_not_gt hn
      exact h (u,⟨t,ht,htD⟩) hz rfl
  rw [he]
  exact hp.isOpen_compl

/-- The safe hold-action slice is genuinely Lebesgue measurable, so its real
volume in the previous bounds is the stated safety measure, not only an
outer-measure estimate of an unspecified controller set. -/
theorem actual_safe_hold_action_set_is_lebesgue_measurable
    (a L x v Delta : ℝ) (ha : 0 < a) (hD : 0 < Delta) :
    MeasurableSet (heldContinuationActions a L x v Delta) := by
  have hprefix := actual_held_prefix_safety_set_is_open L x v Delta
  have hK : IsOpen (printedKernel a L) := by
    rw [actual_kernel_is_the_strict_stopping_barrier_sublevel a L ha]
    exact isOpen_lt (by fun_prop : Continuous (wallStoppingBarrier a)) continuous_const
  have hf : Continuous (fun u : ℝ => (x+v*Delta+(u/2)*Delta^2,v+u*Delta)) := by fun_prop
  have hbound : MeasurableSet {u : ℝ | |u| ≤ a} := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have he : heldContinuationActions a L x v Delta =
      {u : ℝ | |u| ≤ a} ∩
      {u : ℝ | ∀ t : ℝ, 0 ≤ t → t ≤ Delta → x+v*t+(u/2)*t^2 < L} ∩
      (fun u : ℝ => (x+v*Delta+(u/2)*Delta^2,v+u*Delta)) ⁻¹' printedKernel a L := by
    ext u
    simpa only [mem_inter_iff,mem_setOf_eq,mem_preimage,and_assoc] using
      actual_safe_hold_action_iff_prefix_and_successor_kernel a L x v Delta u ha hD
  rw [he]
  exact (hbound.inter hprefix.measurableSet).inter (hK.preimage hf).measurableSet

/-- The printed moving-away example has a genuine safe continuation for every
bounded held input, including the inputs which end the hold moving toward the
wall. Its initial position may be arbitrarily close to the wall from below. -/
theorem actual_printed_moving_away_example_has_all_inputs_safe
    (L x : ℝ) (hx : x < L) :
    heldContinuationActions 1 L x (-(3:ℝ)/10) (1/2) = Icc (-1) 1 := by
  apply Subset.antisymm
  · intro u hu
    exact abs_le.mp hu.1
  · intro u hu
    apply (actual_safe_hold_action_iff_prefix_and_successor_kernel
      1 L x (-(3:ℝ)/10) (1/2) u (by norm_num) (by norm_num)).mpr
    refine ⟨abs_le.mpr hu, ?_, ?_⟩
    · intro t ht htD
      have hsq : t^2 ≤ t/2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hu.2 (sq_nonneg t)
      nlinarith
    · change x+(-(3:ℝ)/10)*(1/2)+(u/2)*(1/2)^2 < L ∧
        (-(3:ℝ)/10+u*(1/2) ≤ 0 ∨
          x+(-(3:ℝ)/10)*(1/2)+(u/2)*(1/2)^2+
            (-(3:ℝ)/10+u*(1/2))^2/(2*1) < L)
      constructor
      · nlinarith [hu.2]
      · by_cases hw : -(3:ℝ)/10+u*(1/2) ≤ 0
        · exact Or.inl hw
        · right
          have hu0 : 0 ≤ u := by linarith
          have hsq : u^2 ≤ u := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu.2)]
          nlinarith

theorem actual_printed_moving_away_example_has_full_safe_action_measure
    (L x : ℝ) (hx : x < L) :
    volume.real (heldContinuationActions 1 L x (-(3:ℝ)/10) (1/2)) = 2 := by
  rw [actual_printed_moving_away_example_has_all_inputs_safe L x hx,
    Real.volume_real_Icc_of_le (by norm_num : -(1:ℝ) ≤ 1)]
  norm_num

/-- At rest, more than a Delta^2 of clearance suffices for every legal held
input. Positive held inputs use the attained hold-then-brake continuation; the
negative inputs use the attained constant nonpositive control. -/
theorem actual_far_wall_rest_has_all_inputs_safe
    (a L x Delta : ℝ) (ha : 0 < a) (hD : 0 < Delta)
    (hfar : a*Delta^2 < L-x) :
    heldContinuationActions a L x 0 Delta = Icc (-a) a := by
  have hx : x < L := by nlinarith [mul_nonneg ha.le (sq_nonneg Delta)]
  apply Subset.antisymm
  · intro u hu
    exact abs_le.mp hu.1
  · intro u hu
    by_cases hup : 0 < u
    · apply (actual_safe_hold_action_iff_prefix_and_successor_kernel a L x 0 Delta u ha hD).mpr
      refine ⟨abs_le.mpr hu, ?_, ?_⟩
      · intro t ht htD
        have hs : t^2 ≤ Delta^2 := by nlinarith
        have hm := mul_le_mul_of_nonneg_left hs hup.le
        have hm' := mul_le_mul_of_nonneg_right hu.2 (sq_nonneg Delta)
        nlinarith [mul_nonneg ha.le (sq_nonneg Delta)]
      · change x+0*Delta+(u/2)*Delta^2 < L ∧
          (0+u*Delta ≤ 0 ∨ x+0*Delta+(u/2)*Delta^2+(0+u*Delta)^2/(2*a) < L)
        have hu2 : u^2 ≤ a^2 := by nlinarith [mul_nonneg hup.le (sub_nonneg.mpr hu.2)]
        have hratio : u^2/a ≤ a := (div_le_iff₀ ha).mpr (by nlinarith)
        have hc : u+u^2/a ≤ 2*a := by linarith
        have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg Delta)
        have he : x+0*Delta+(u/2)*Delta^2+(0+u*Delta)^2/(2*a) =
            x+(u+u^2/a)*Delta^2/2 := by field_simp;ring
        constructor
        · nlinarith [mul_le_mul_of_nonneg_right hu.2 (sq_nonneg Delta)]
        · right
          rw [he]
          nlinarith
    · apply actual_nonpositive_constant_inputs_give_safe_hold_actions a L x 0 Delta u hx le_rfl
        (le_of_not_gt hup) (abs_le.mpr hu)

theorem actual_far_wall_rest_has_full_safe_action_measure
    (a L x Delta : ℝ) (ha : 0 < a) (hD : 0 < Delta)
    (hfar : a*Delta^2 < L-x) :
    volume.real (heldContinuationActions a L x 0 Delta) = 2*a := by
  rw [actual_far_wall_rest_has_all_inputs_safe a L x Delta ha hD hfar,
    Real.volume_real_Icc_of_le (by linarith : -a ≤ a)]
  ring

/-- Every unviable state fails in finite time for every admissible actual
trajectory, even though the family above precludes a common horizon. Initial
members of the closed failure set fail already at time zero. -/
theorem actual_every_unviable_state_has_finite_all_controller_failure
    (a L x v : ℝ) (ha : 0 < a) (hU : ¬ Viable a L x v)
    (P : ControlledPath a x v) :
    ∃ t : ℝ, 0 ≤ t ∧ L ≤ P.position t := by
  have hu := (actual_unviable_state_iff_printed_union a L x v ha).mp hU
  rcases hu with hfail | ⟨hv,hpeak⟩
  · exact ⟨0,le_rfl,by simpa only [P.position_zero] using hfail⟩
  · exact ⟨v/a,div_nonneg hv.le ha.le,
      actual_closed_wall_failure_by_stopping_time a L x v P ha hv hpeak⟩

end SafeLearning.CompleteAppliedDoubleIntegratorWall27
