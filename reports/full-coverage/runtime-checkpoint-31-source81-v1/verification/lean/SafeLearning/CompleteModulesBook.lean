import SafeLearning.Modules
import SafeLearning.BookApplications

/-! Explicit model statements for the eleven module application laboratories.
The source ledger distinguishes these results from any unproved probabilistic,
spectral, or research-level assertion in the prose. -/
set_option autoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesBook

-- Module 1: a robust sampled thermal model, including both interval endpoints.
theorem thermal_step (T u w : ℝ) (hT : T ∈ Icc 15 60)
    (hu : u ∈ Icc 0 12) (hw : w ∈ Icc (-1) 1) :
    (4/5)*T+4+(1/2)*u+w ∈ Icc 15 60 := by
  constructor <;> linarith [hT.1, hT.2, hu.1, hu.2, hw.1, hw.2]

theorem thermal_all_samples (T u w : ℕ → ℝ) (hzero : T 0 ∈ Icc 15 60)
    (hu : ∀ n, u n ∈ Icc 0 12) (hw : ∀ n, w n ∈ Icc (-1) 1)
    (hstep : ∀ n, T (n+1) = (4/5)*T n+4+(1/2)*u n+w n) :
    ∀ n, T n ∈ Icc 15 60 := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih => rw [hstep]; exact thermal_step _ _ _ ih (hu n) (hw n)

theorem peak_mean_examples :
    (9/10:ℝ)*58+(1/10)*68 = 59 ∧
    (49/50:ℝ)*59+(1/50)*109 = 60 := by norm_num

def rareSpikeRU (nu : ℝ) : ℝ :=
  nu+20*((49/50)*max (59-nu) 0+(1/50)*max (109-nu) 0)

theorem rare_spike_cvar_lower (nu : ℝ) : 79 ≤ rareSpikeRU nu := by
  unfold rareSpikeRU
  linarith [le_max_left (59-nu) 0, le_max_right (59-nu) 0,
    le_max_left (109-nu) 0]

theorem rare_spike_cvar_attained : rareSpikeRU 59 = 79 := by
  norm_num [rareSpikeRU]

theorem fleet_budget : (20:ℝ)*(1/400)=1/20 := by norm_num

-- Module 2: explicit two-dimensional energy and robust radius implications.
def thermalA (x y : ℝ) : ℝ × ℝ := ((3/5)*x+(1/10)*y,(1/10)*x+(7/10)*y)

theorem thermal_energy_identity (x y : ℝ) :
    (thermalA x y).1^2+(thermalA x y).2^2-(x^2+y^2) =
      -((63/100)*x^2-(26/100)*x*y+(1/2)*y^2) := by
  unfold thermalA
  ring

theorem thermal_energy_strict (x y : ℝ) (hne : x ≠ 0 ∨ y ≠ 0) :
    (thermalA x y).1^2+(thermalA x y).2^2 < x^2+y^2 := by
  have hsq : 0 < x^2+y^2 := by
    rcases hne with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y]
    · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg x]
  rw [← sub_neg]
  rw [thermal_energy_identity]
  nlinarith [sq_nonneg (x-y),sq_nonneg x,sq_nonneg y]

theorem thermal_disk_invariant (x y : ℝ) (h : x^2+y^2 ≤ 1) :
    (thermalA x y).1^2+(thermalA x y).2^2 ≤ 1 := by
  have hi := thermal_energy_identity x y
  nlinarith [sq_nonneg (x-y),sq_nonneg x,sq_nonneg y]

theorem disk_coordinate_containment (x y : ℝ) (h : x^2+y^2 ≤ 1) :
    |x| ≤ 1 ∧ |y| ≤ 1 := by
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg x,sq_nonneg y]

theorem startup_box_energy (x y : ℝ) (hx : |x| ≤ 7/10) (hy : |y| ≤ 7/10) :
    x^2+y^2 ≤ 49/50 := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  nlinarith [sq_nonneg (x-7/10),sq_nonneg (y-7/10),sq_nonneg (x+7/10),sq_nonneg (y+7/10)]

theorem thermal_starting_example : thermalA (3/5) (-4/5) = (7/25,-1/2) ∧
    (7/25:ℝ)^2+(-1/2)^2=821/2500 := by norm_num [thermalA]

theorem invariant_radius_iff (q allowance R : ℝ) (hq : q < 1) :
    q*R+allowance ≤ R ↔ allowance/(1-q) ≤ R := by
  rw [div_le_iff₀ (by linarith : 0 < 1-q)]
  constructor <;> intro h <;> nlinarith

theorem nonzero_forced_equilibrium (q allowance : ℝ) (hq : q < 1)
    (ha : 0 < allowance) :
    q*(allowance/(1-q))+allowance=allowance/(1-q) ∧
      0 < allowance/(1-q) := by
  have hd : 1-q ≠ 0 := by linarith
  constructor
  · field_simp; ring
  · exact div_pos ha (by linarith)

-- Module 3: solve the actual linear systems, rather than assuming the solution.
theorem gp_midpoint_linear_solutions :
    (5:ℝ)*(10/21)+2*(-4/21)=2 ∧
    (2:ℝ)*(10/21)+5*(-4/21)=0 ∧
    (5:ℝ)*(3/7)+2*(3/7)=3 ∧
    (2:ℝ)*(3/7)+5*(3/7)=3 ∧
    (3:ℝ)*(10/21)+3*(-4/21)=6/7 ∧
    (4:ℝ)-(3*(3/7)+3*(3/7))=10/7 := by norm_num

theorem gp_midpoint_unique_solution (a b : ℝ)
    (h₁ : 5*a+2*b=2) (h₂ : 2*a+5*b=0) : a=10/21 ∧ b= -4/21 := by
  constructor <;> linarith

theorem gp_midpoint_reject_accept :
    60 < (57:ℝ)+6/7+2*Real.sqrt (10/7) ∧
    (113/2:ℝ)+6/7+2*Real.sqrt (10/7) < 60 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 10/7)
  have hn := Real.sqrt_nonneg (10/7:ℝ)
  constructor <;> nlinarith

theorem repeated_gp_linear_system (n : ℕ) :
    (1+4*(n:ℝ))*(2/(1+4*n))=2 ∧
    (4:ℝ)*n*(2/(1+4*n))=(8*n)/(1+4*n) := by
  have hd : (1+4*(n:ℝ)) ≠ 0 := by positivity
  constructor <;> field_simp <;> ring

theorem repeated_gp_variance (n : ℕ) :
    (4:ℝ)-4*n*(4/(1+4*n))=4/(1+4*n) := by
  have hd : (1+4*(n:ℝ)) ≠ 0 := by positivity
  field_simp; ring

theorem repeated_gp_three_accept : (57:ℝ)+24/13+2*Real.sqrt (4/13) < 60 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4/13)
  have hn := Real.sqrt_nonneg (4/13:ℝ)
  nlinarith

theorem constant_kernel_regularized_unique {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (rhs : ℝ) (hsolve : ∀ i, a i+4*(∑ j, a j)=rhs) :
    ∀ i, a i=rhs/(1+4*(Fintype.card ι:ℝ)) := by
  have hsum : (∑ i, (a i+4*(∑ j, a j)))=∑ _i : ι, rhs :=
    Finset.sum_congr rfl (fun i _ => hsolve i)
  have hsum' : (∑ i, a i)+4*(Fintype.card ι:ℝ)*(∑ i, a i)=
      (Fintype.card ι:ℝ)*rhs := by
    simpa [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using hsum
  have hd : (1+4*(Fintype.card ι:ℝ)) ≠ 0 := by positivity
  intro i
  apply (eq_div_iff hd).mpr
  nlinarith [hsolve i]

theorem midpoint_kernel_positive (x y z : ℝ) (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    0 < 4*x^2+4*y^2+4*z^2+4*x*y+6*x*z+6*y*z := by
  have hi : 4*x^2+4*y^2+4*z^2+4*x*y+6*x*z+6*y*z=
      3*(x+y+z)^2+(x-y)^2+z^2 := by ring
  rw [hi]
  by_contra h
  have hz : z=0 := by nlinarith [sq_nonneg (x+y+z),sq_nonneg (x-y),sq_nonneg z]
  have heq : x-y=0 := by nlinarith [sq_nonneg (x+y+z),sq_nonneg (x-y)]
  have hsum : x+y+z=0 := by nlinarith [sq_nonneg (x+y+z),sq_nonneg (x-y)]
  rcases hne with hx | hy | hz'
  · apply hx; linarith
  · apply hy; linarith
  · exact hz' hz

theorem midpoint_discrepancy_reject :
    60 < (113/2:ℝ)+6/7+2*Real.sqrt (10/7)+2/5 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 10/7)
  have hn := Real.sqrt_nonneg (10/7:ℝ)
  nlinarith

theorem residual_with_discrepancy (f mean sigma b B nominal cap : ℝ)
    (hf : |f-mean| ≤ sigma) (hb : |b| ≤ B)
    (hdecision : nominal+mean+sigma+B ≤ cap) : nominal+f+b ≤ cap := by
  linarith [(abs_le.mp hf).2,(abs_le.mp hb).2]

theorem maximal_nominal (bound cap nominal : ℝ) :
    nominal+bound ≤ cap ↔ nominal ≤ cap-bound := by constructor <;> intro h <;> linarith

-- Modules 4--6: certificate intersections, implementation errors, and backups.
theorem two_constraints_radius (d : ℝ) :
    (0 ≤ 4/5-d ∧ 0 ≤ 3/25-(2/5)*d) ↔ d ≤ 3/10 := by
  constructor
  · intro h; linarith [h.2]
  · intro h; constructor <;> linarith

theorem gain_realization_radius (d : ℝ) : d+1/25 ≤ (3/10:ℝ) ↔ d ≤ 13/50 := by
  constructor <;> intro h <;> linarith

theorem gain_proposals_fail :
    (3/25:ℝ)-(2/5)*(2/5)= -1/25 ∧
    (3/25:ℝ)-(2/5)*(7/25+1/25)= -1/125 := by norm_num

theorem nominal_gain_positive_but_realization_fails :
    0 < (3/25:ℝ)-(2/5)*(7/25) ∧
    (3/25:ℝ)-(2/5)*(7/25+1/25) < 0 := by norm_num

theorem interval_realization_iff (a e lo hi : ℝ) (he : 0 ≤ e) :
    (∀ x ∈ Icc (a-e) (a+e), x ∈ Icc lo hi) ↔ lo+e ≤ a ∧ a ≤ hi-e := by
  constructor
  · intro h
    have hl := (h (a-e) (by constructor <;> linarith)).1
    have hr := (h (a+e) (by constructor <;> linarith)).2
    constructor <;> linarith
  · rintro ⟨hl,hr⟩ x ⟨hx₀,hx₁⟩
    constructor <;> linarith

theorem losbo_command_interval (a : ℝ) :
    (∀ x ∈ Icc (a-1/10) (a+1/10), x ∈ Icc (-1:ℝ) (31/20)) ↔
      a ∈ Icc (-9/10) (29/20) := by
  rw [interval_realization_iff a (1/10) (-1) (31/20) (by norm_num)]
  norm_num

theorem losbo_cones (a : ℝ) :
    (0 ≤ 4/5-(4/5)*|a| ↔ a ∈ Icc (-1) 1) ∧
    (0 ≤ 3/5-(4/5)*|a-4/5| ↔ a ∈ Icc (1/20) (31/20)) := by
  constructor
  · constructor
    · intro h
      have h' : |a| ≤ 1 := by linarith
      exact abs_le.mp h'
    · intro h; have h' := abs_le.mpr h; linarith
  · constructor
    · intro h; have h' : |a-4/5| ≤ 3/4 := by linarith
      have hh := abs_le.mp h'; constructor <;> linarith [hh.1,hh.2]
    · intro h; have hh : |a-4/5| ≤ 3/4 := by rw [abs_le]; constructor <;> linarith [h.1,h.2]
      linarith

theorem losbo_union :
    Icc (-1:ℝ) 1 ∪ Icc (1/20) (31/20) = Icc (-1) (31/20) := by
  ext x
  simp only [mem_union,mem_Icc]
  constructor
  · rintro (h | h) <;> constructor <;> linarith [h.1,h.2]
  · intro h
    by_cases hx : x ≤ 1
    · exact Or.inl ⟨h.1,hx⟩
    · right; constructor <;> linarith [h.1,h.2]

def backupDistance (d v db vb : ℝ) : ℝ := |d-db|+(1/2)*|v-vb|

theorem backup_distance_triangle (d v db vb dc vc : ℝ) :
    backupDistance d v db vb ≤ backupDistance d v dc vc+backupDistance dc vc db vb := by
  have hd : |d-db| ≤ |d-dc|+|dc-db| := by
    simpa [sub_add_sub_cancel] using abs_add_le (d-dc) (dc-db)
  have hv : |v-vb| ≤ |v-vc|+|vc-vb| := by
    simpa [sub_add_sub_cancel] using abs_add_le (v-vc) (vc-vb)
  unfold backupDistance; linarith

theorem backup_monitor_period (dt : ℝ) :
    (1/4:ℝ)+1/50+(4/5)*dt ≤ 2/5 ↔ dt ≤ 13/80 := by
  constructor <;> intro h <;> linarith

theorem backup_examples :
    backupDistance (3/5) (2/5) (4/5) (3/10)=1/4 ∧
    backupDistance (1/2) (1/2) (4/5) (3/10)=2/5 ∧
    backupDistance (2/5) (1/10) (4/5) (3/10)=1/2 ∧
    backupDistance (2/5) (1/10) (9/20) 0=1/10 ∧
    backupDistance (2/5) 1 (4/5) (3/10)=3/4 ∧
    backupDistance (2/5) 1 (9/20) 0=11/20 := by norm_num [backupDistance]

theorem backup_library_decisions :
    ¬ (backupDistance (2/5) (1/10) (4/5) (3/10)+1/10 ≤ 2/5) ∧
    backupDistance (2/5) (1/10) (9/20) 0+1/10 ≤ 1/4 ∧
    ¬ (backupDistance (2/5) 1 (4/5) (3/10)+1/10 ≤ 2/5) ∧
    ¬ (backupDistance (2/5) 1 (9/20) 0+1/10 ≤ 1/4) := by norm_num [backupDistance]

theorem backup_switch_and_transition (reported actual minimum margin reserve radius : ℝ)
    (hactivation : actual ≤ reported+reserve)
    (hrecovery : radius-actual ≤ minimum)
    (hgate : reported+reserve ≤ radius)
    (htransition : reserve ≤ margin) : 0 ≤ minimum ∧ 0 ≤ margin-reserve := by
  constructor <;> linarith

-- Module 7: strict discounted-return separation, with ties exposed explicitly.
def safeCycleReturn (gamma : ℝ) : ℝ := (3*gamma+3*gamma^2)/(1-gamma^3)
def unsafeRushReturn (gamma penalty : ℝ) : ℝ := 25+gamma*(3-penalty)

theorem safe_cycle_values : safeCycleReturn (9/10)=5130/271 ∧
    safeCycleReturn (4/5)=540/61 := by norm_num [safeCycleReturn]

theorem rush_strict_threshold (gamma penalty : ℝ) (hg : 0 < gamma) :
    unsafeRushReturn gamma penalty < safeCycleReturn gamma ↔
      (25+3*gamma-safeCycleReturn gamma)/gamma < penalty := by
  unfold unsafeRushReturn
  rw [div_lt_iff₀ hg]
  constructor <;> intro h <;> nlinarith

theorem rush_threshold_equality (gamma : ℝ) (hg : gamma ≠ 0) :
    unsafeRushReturn gamma ((25+3*gamma-safeCycleReturn gamma)/gamma)=
      safeCycleReturn gamma := by
  unfold unsafeRushReturn; field_simp; ring

theorem rush_eight_tenths_threshold :
    ((25:ℝ)+3*(4/5)-safeCycleReturn (4/5))/(4/5)=5657/244 ∧
    unsafeRushReturn (4/5) 24=41/5 ∧
    unsafeRushReturn (4/5) 24 < safeCycleReturn (4/5) := by
  norm_num [safeCycleReturn,unsafeRushReturn]

-- Module 12: the displayed SDP's negative semidefiniteness, for every vector.
def lipSdpQuadratic (x y z w : ℝ) : ℝ :=
  -(4/3)*x^2-(4/3)*y^2+(2/3)*x*z+(2/3)*x*w+
    (4/3)*y*z-(4/3)*y*w-(5/12)*z^2+(1/2)*z*w-(5/12)*w^2

theorem lipsdp_sum_of_squares (x y z w : ℝ) :
    lipSdpQuadratic x y z w =
      -(4/3)*(x-(z+w)/4)^2-(4/3)*(y-(z-w)/2)^2 := by
  unfold lipSdpQuadratic; ring

theorem lipsdp_negative_semidefinite (x y z w : ℝ) :
    lipSdpQuadratic x y z w ≤ 0 := by
  rw [lipsdp_sum_of_squares]
  nlinarith [sq_nonneg (x-(z+w)/4),sq_nonneg (y-(z-w)/2)]

theorem lipsdp_physical_budget : (2:ℝ)*Real.sqrt (4/3)*(1/25) < 1/10 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4/3)
  have hn := Real.sqrt_nonneg (4/3:ℝ)
  nlinarith

theorem lipsdp_box_radius (x y : ℝ) (hx : |x| ≤ 1/50) (hy : |y| ≤ 1/50) :
    x^2+y^2 ≤ 1/1250 := by
  have hx' := abs_le.mp hx; have hy' := abs_le.mp hy
  nlinarith [sq_nonneg (x-1/50),sq_nonneg (y-1/50),sq_nonneg (x+1/50),sq_nonneg (y+1/50)]

theorem coupled_multiplier_failure :
    (max (2:ℝ) 0-max 1 0)=1 ∧
    (max (-2:ℝ) 0-max (-3) 0)=0 ∧
    2*((1:ℝ)*(0-1)+0*(0+1))= -2 := by norm_num

-- Module 13: implementation gain budgets with a finite number of stages.
theorem gain_stack_bound (gain : ℕ → ℝ) (bound : ℝ) (hb : 0 ≤ bound)
    (hg : ∀ n, 0 ≤ gain n ∧ gain n ≤ bound) :
    ∀ n, (∏ k ∈ Finset.range n, gain k) ≤ bound^n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ,pow_succ]
    exact mul_le_mul ih (hg n).2 (hg n).1 (pow_nonneg hb n)

theorem external_scale_certificate (factor target scale : ℝ)
    (hf : 0 < factor) (hc : scale ≤ target/factor) : scale*factor ≤ target := by
  exact (le_div_iff₀ hf).mp hc

theorem six_stage_scale : (3/10:ℝ)/(501/500)^6*(501/500)^6=3/10 := by norm_num

theorem normalized_target_incompatible (a b : ℝ)
    (h : ∀ x y : ℝ, |(2/5)*(x-y)| ≤ (3/10)*|x-y|)
    (hne : a ≠ b) : False := by
  have hh := h a b
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2/5)] at hh
  have hp : 0 < |a-b| := abs_pos.mpr (sub_ne_zero.mpr hne)
  nlinarith

theorem architecture_sensor_budget :
    (3/10:ℝ)*Real.sqrt ((1/50)^2+(3/100)^2) < 3/250 := by
  have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ (1/50)^2+(3/100)^2)
  have hn := Real.sqrt_nonneg ((1/50:ℝ)^2+(3/100)^2)
  nlinarith

-- Module 14: revised disturbances and the independently initialized delay.
theorem biased_feedback_error (bias error : ℝ) (hb : |bias| ≤ 3/100)
    (he : |error| ≤ 1/50) : |(3/10)*bias+error| ≤ 29/1000 := by
  calc |(3/10)*bias+error| ≤ |(3/10)*bias|+|error| := abs_add_le _ _
    _ = (3/10)*|bias|+|error| := by rw [abs_mul]; norm_num
    _ ≤ 29/1000 := by linarith

theorem biased_invariant_and_ultimate :
    (9/10:ℝ)*(1/2)+29/1000 ≤ 1/2 ∧
    (29/1000:ℝ)/(1-9/10)=29/100 := by norm_num

theorem delayed_square_counterexample :
    |(1/2:ℝ)| ≤ 1/2 ∧ |(-1/2:ℝ)| ≤ 1/2 ∧
    (9/10:ℝ)*(1/2)-(3/10)*(-1/2)=3/5 ∧
    1/2 < |(3/5:ℝ)| ∧ |(-3/2:ℝ)*(-1/2)| ≤ 4/5 := by norm_num

-- Module 15: an exhaustive piecewise proof, including changed-domain extrema.
def verificationNetwork (z : ℝ) : ℝ := max (z+1/5) 0-2*max (z-1/10) 0

theorem verification_left_region (z : ℝ) (hz : z ≤ -1/5) :
    verificationNetwork z=0 := by
  unfold verificationNetwork
  rw [max_eq_right (by linarith),max_eq_right (by linarith)]
  ring

theorem verification_middle_region (z : ℝ) (hl : -1/5 ≤ z) (hr : z ≤ 1/10) :
    verificationNetwork z=z+1/5 := by
  unfold verificationNetwork
  rw [max_eq_left (by linarith),max_eq_right (by linarith)]
  ring

theorem verification_right_region (z : ℝ) (hz : 1/10 ≤ z) :
    verificationNetwork z=2/5-z := by
  unfold verificationNetwork
  rw [max_eq_left (by linarith),max_eq_left (by linarith)]
  ring

theorem verification_original_range (z : ℝ) (hz : z ∈ Icc (-3/10) (2/5)) :
    verificationNetwork z ∈ Icc 0 (3/10) := by
  by_cases hl : z ≤ -1/5
  · rw [verification_left_region z hl]; norm_num
  · by_cases hr : z ≤ 1/10
    · rw [verification_middle_region z (by linarith) hr]
      constructor <;> linarith
    · rw [verification_right_region z (by linarith)]
      constructor <;> linarith [hz.2]

theorem verification_changed_range (z : ℝ) (hz : z ∈ Icc (-1/10) (1/2)) :
    verificationNetwork z ∈ Icc (-1/10) (3/10) := by
  by_cases hr : z ≤ 1/10
  · rw [verification_middle_region z (by linarith [hz.1]) hr]
    constructor <;> linarith [hz.1]
  · rw [verification_right_region z (by linarith)]
    constructor <;> linarith [hz.2]

theorem verification_extrema_attained :
    verificationNetwork (-3/10)=0 ∧ verificationNetwork (2/5)=0 ∧
    verificationNetwork (1/10)=3/10 ∧ verificationNetwork (1/2)= -1/10 := by
  norm_num [verificationNetwork]

theorem deterministic_temperature_pass (z : ℝ) (hz : z ∈ Icc (-3/10) (2/5)) :
    (1193/20:ℝ)+verificationNetwork z ≤ 1199/20 := by
  linarith [(verification_original_range z hz).2]

theorem changed_temperature_pass (z : ℝ) (hz : z ∈ Icc (-1/10) (1/2)) :
    (597/10:ℝ)+verificationNetwork z ≤ 60 := by
  linarith [(verification_changed_range z hz).2]

theorem changed_zero_margin_attained :
    (597/10:ℝ)+verificationNetwork (1/10)=60 ∧
    verificationNetwork (1/2) < 0 := by norm_num [verificationNetwork]

theorem trajectory_conformal_size (n : ℕ) :
    (99/100:ℝ)*((n:ℝ)+1) ≤ n ↔ 99 ≤ n := by
  constructor
  · intro h
    have hn : (99:ℝ) ≤ n := by linarith
    exact_mod_cast hn
  · intro h
    have hn : (99:ℝ) ≤ n := by exact_mod_cast h
    linarith

theorem trajectory_residual_transfer (nominal correction residual : ℕ → ℝ)
    (hn : ∀ t, nominal t ≤ 1187/20)
    (hc : ∀ t, correction t ≤ 3/10)
    (hr : ∀ t, |residual t| ≤ 8/25) :
    ∀ t, nominal t+correction t+residual t ≤ 5997/100 := by
  intro t
  linarith [hn t,hc t,(abs_le.mp (hr t)).2]

end SafeLearning.CompleteModulesBook
