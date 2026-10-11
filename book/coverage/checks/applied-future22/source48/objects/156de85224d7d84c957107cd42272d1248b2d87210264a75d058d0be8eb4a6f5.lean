import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedSystems
open Filter
open scoped Topology

def thermalA : ℝ := Real.exp (-(1/4:ℝ))
def thermalB : ℝ := 4*(1-thermalA)
def thermalQ : ℝ := thermalA-thermalB/2
def heldThermal (x v s : ℝ) : ℝ := Real.exp (-s/20)*x+4*(1-Real.exp (-s/20))*v

theorem thermalA_enclosure : (778800/1000000:ℝ)≤thermalA ∧
    thermalA≤778802/1000000 := by
  have h := Real.exp_bound (x := -(1/4:ℝ)) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have hh := abs_le.mp h
  unfold thermalA
  constructor <;> linarith

theorem thermal_coefficients : 0<thermalA ∧ thermalA<1 ∧ 0<thermalB ∧
    0<thermalQ ∧ thermalQ<1 ∧
    (336400/1000000:ℝ)≤thermalQ ∧ thermalQ≤336406/1000000 := by
  obtain ⟨hl,hu⟩ := thermalA_enclosure
  unfold thermalQ thermalB
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem heldThermal_initial (x v : ℝ) : heldThermal x v 0=x := by simp [heldThermal]

theorem heldThermal_derivative (x v s : ℝ) :
    HasDerivAt (heldThermal x v) (-(1/20)*heldThermal x v s+(1/5)*v) s := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t/20))
      (Real.exp (-s/20)*(-(1/20))) s := by
    convert ((hasDerivAt_id s).neg.div_const 20).exp using 1 <;>
      (try ext t) <;> simp only [Pi.neg_apply,id_eq] <;> ring
  have hh := (he.mul_const x).add (((hasDerivAt_const s (1:ℝ)).sub he).const_mul (4*v))
  convert hh using 1 <;> (try ext t) <;>
    simp only [heldThermal,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,id_eq] <;> ring

theorem sampled_thermal (x v : ℝ) : heldThermal x v 5=thermalA*x+thermalB*v := by
  simp only [heldThermal,thermalA,thermalB]
  norm_num

theorem shifted_temperature (x v : ℝ) :
    -((x+22)-18)/20+(1/5)*(v+1)=-(1/20)*x+(1/5)*v := by ring

theorem equilibrium_input : -((22:ℝ)-18)/20+(1/5)*1=0 := by norm_num

theorem sampled_feedback (x : ℝ) :
    thermalA*x+thermalB*(-x/2)=thermalQ*x := by unfold thermalQ; ring

theorem actuator_admissible (x k : ℝ) (hx : |x|≤2) (hk : k ∈ Set.Icc 0 (1/2)) :
    1-k*x ∈ Set.Icc (0:ℝ) 2 := by
  have habs : |k*x|≤1 := by
    rw [abs_mul,abs_of_nonneg hk.1]
    nlinarith [mul_le_mul_of_nonneg_left hx hk.1,hk.2]
  have hh := abs_le.mp habs
  constructor <;> linarith

theorem sampled_thermal_invariant (x : ℝ) (hx : |x|≤2) :
    |thermalQ*x|≤2 := by
  have hq := thermal_coefficients
  rw [abs_mul,abs_of_pos hq.2.2.2.1]
  nlinarith [mul_le_mul_of_nonneg_left hx hq.2.2.2.1.le]

theorem geometric_trajectory (x : ℕ → ℝ) (hstep : ∀ n, x (n+1)=thermalQ*x n) :
    ∀ n, x n=thermalQ^n*x 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [hstep n,ih]; ring

theorem sampled_convergence (x0 : ℝ) :
    Tendsto (fun n : ℕ => thermalQ^n*x0) atTop (𝓝 0) := by
  have hq := thermal_coefficients
  have hh := tendsto_pow_atTop_nhds_zero_of_lt_one hq.2.2.2.1.le hq.2.2.2.2.1
  simpa using hh.mul_const x0

theorem thermal_lyapunov (x : ℝ) : (thermalQ*x)^2=thermalQ^2*x^2 := by ring

theorem thermal_lyapunov_strict (x : ℝ) (hx : x≠0) :
    (thermalQ*x)^2<x^2 := by
  have hq := thermal_coefficients
  have hs : thermalQ^2<1 := by nlinarith [hq.2.2.2.1,hq.2.2.2.2.1]
  nlinarith [sq_pos_of_ne_zero hx]

theorem held_feedback_formula (x s : ℝ) :
    heldThermal x (-x/2) s=(3*Real.exp (-s/20)-2)*x := by unfold heldThermal; ring

theorem intersample_multiplier (s : ℝ) (hs : s ∈ Set.Icc 0 5) :
    thermalQ≤3*Real.exp (-s/20)-2 ∧ 3*Real.exp (-s/20)-2≤1 := by
  have hlo : thermalA ≤ Real.exp (-s/20) := by
    unfold thermalA
    apply Real.exp_le_exp.mpr
    linarith [hs.2]
  have hhi : Real.exp (-s/20)≤1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    linarith [hs.1]
  unfold thermalQ thermalB
  constructor <;> linarith

theorem intersample_thermal_invariant (x s : ℝ) (hx : |x|≤2)
    (hs : s ∈ Set.Icc 0 5) : |heldThermal x (-x/2) s|≤2 := by
  have hm := intersample_multiplier s hs
  have hq := thermal_coefficients
  have hm0 : 0≤3*Real.exp (-s/20)-2 := by linarith [hq.2.2.2.1]
  rw [held_feedback_formula,abs_mul,abs_of_nonneg hm0]
  nlinarith [mul_le_mul_of_nonneg_left hx hm0]

theorem deadline_readings :
    (3/10:ℝ) < |(-2:ℝ)| ∧ (3/10:ℝ) < |thermalQ*(-2)| ∧
    |thermalQ^2*(-2)|≤3/10 := by
  have hq := thermal_coefficients
  have hl := hq.2.2.2.2.2.1
  have hu := hq.2.2.2.2.2.2
  have hq0 := hq.2.2.2.1
  rw [abs_mul,abs_of_pos hq0,abs_mul,abs_pow,abs_of_pos hq0]
  norm_num
  constructor
  · linarith
  · nlinarith [sq_nonneg (thermalQ-(336406/1000000:ℝ))]

theorem robust_scalar_interval (q radius disturbance : ℝ)
    (hq : 0≤q) (hr : 0≤radius) (hd : 0≤disturbance) :
    (∀ x w : ℝ, |x|≤radius → |w|≤disturbance → |q*x+w|≤radius) ↔
      q*radius+disturbance≤radius := by
  constructor
  · intro h
    have hh := h radius disturbance (by simpa [abs_of_nonneg hr])
      (by simpa [abs_of_nonneg hd])
    have := (abs_le.mp hh).2
    linarith
  · intro h x w hx hw
    calc
      |q*x+w|≤|q*x|+|w| := abs_add_le _ _
      _=q*|x|+|w| := by rw [abs_mul,abs_of_nonneg hq]
      _≤q*radius+disturbance := by nlinarith [mul_le_mul_of_nonneg_left hx hq]
      _≤radius := h

theorem disturbed_gain_interval (k : ℝ) (hk : k ∈ Set.Icc 0 (1/2)) :
    (∀ x w : ℝ, |x|≤1/5 → |w|≤1/10 → |(thermalA-thermalB*k)*x+w|≤1/5) ↔
      (thermalA-1/2)/thermalB≤k := by
  have ha := thermal_coefficients
  have hq : 0≤thermalA-thermalB*k := by
    have hb : thermalB*k≤thermalB/2 := by nlinarith [ha.2.2.1,hk.2]
    have he : thermalA-thermalB/2=thermalQ := rfl
    linarith [ha.2.2.2.1]
  rw [robust_scalar_interval _ _ _ hq (by norm_num) (by norm_num),
    div_le_iff₀ ha.2.2.1]
  constructor <;> intro h <;> nlinarith

def saturatedDeviation (x : ℝ) : ℝ := max (-1) (min (-x) 1)

theorem saturated_map_invariant (x : ℝ) (hx : |x|≤2) :
    |thermalA*x+thermalB*saturatedDeviation x|≤2 := by
  obtain ⟨hl,hu⟩ := thermalA_enclosure
  have hb : thermalB=4*(1-thermalA) := rfl
  have ha : 0<thermalA := thermal_coefficients.1
  have hx' := abs_le.mp hx
  unfold saturatedDeviation
  by_cases hm : x≤-1
  · rw [min_eq_right (by linarith),max_eq_right (by norm_num)]
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx'.1 ha.le,
      mul_le_mul_of_nonneg_left hm ha.le]
  · by_cases hp : 1≤x
    · rw [min_eq_left (by linarith),max_eq_left (by linarith)]
      rw [abs_le]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx'.2 ha.le,
        mul_le_mul_of_nonneg_left hp ha.le]
    · rw [min_eq_left (by linarith),max_eq_right (by linarith)]
      rw [abs_le]
      have hc : |thermalA-thermalB|≤1 := by rw [abs_le]; constructor <;> linarith
      have hab : |(thermalA-thermalB)*x|≤1 := by
        rw [abs_mul]
        have hx1 : |x|≤1 := by rw [abs_le]; constructor <;> linarith
        nlinarith [abs_nonneg x,abs_nonneg (thermalA-thermalB)]
      have hab' := abs_le.mp hab
      constructor <;> nlinarith

def brakeSpeed (v a t : ℝ) : ℝ := v-a*t
def brakeDistance (d v a t : ℝ) : ℝ := d-v*t+a*t^2/2
def stoppingClearance (d v a : ℝ) : ℝ := d-v^2/(2*a)

theorem brake_dynamics (d v a t : ℝ) :
    HasDerivAt (brakeSpeed v a) (-a) t ∧
    HasDerivAt (brakeDistance d v a) (-(brakeSpeed v a t)) t := by
  constructor
  · unfold brakeSpeed
    convert (hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul a) using 1 <;> (try ext s) <;> (try simp only [Pi.sub_apply,id_eq]) <;> ring
  · unfold brakeDistance brakeSpeed
    convert ((hasDerivAt_const t d).sub ((hasDerivAt_id t).const_mul v)).add
      ((((hasDerivAt_id t).pow 2).const_mul a).div_const 2) using 1 <;>
      (try ext s) <;> simp only [Pi.add_apply,Pi.sub_apply,Pi.pow_apply,id_eq] <;> ring

theorem brake_clearance_constant (d v a t : ℝ) (ha : 0<a) :
    stoppingClearance (brakeDistance d v a t) (brakeSpeed v a t) a=
      stoppingClearance d v a := by
  unfold stoppingClearance brakeDistance brakeSpeed
  field_simp
  ring

theorem stopping_distance (d v a : ℝ) (ha : 0<a) :
    brakeSpeed v a (v/a)=0 ∧ brakeDistance d v a (v/a)=d-v^2/(2*a) := by
  unfold brakeSpeed brakeDistance
  constructor <;> field_simp <;> ring

theorem braking_all_time_safe (d v a t : ℝ) (ha : 0<a)
    (hc : 0 ≤ stoppingClearance d v a) : 0≤brakeDistance d v a t := by
  have hh := brake_clearance_constant d v a t ha
  have hpos : 0≤(brakeSpeed v a t)^2/(2*a) := by positivity
  unfold stoppingClearance at hh hc
  linarith

theorem delayed_brake_condition (d v a tau : ℝ) (hv : 0<v) :
    v*tau+v^2/(2*a)≤d ↔ tau≤(d-v^2/(2*a))/v := by
  rw [le_div_iff₀ hv]
  constructor <;> intro h <;> nlinarith

theorem braking_examples :
    stoppingClearance (4/5) 1 1=3/10 ∧
    (1:ℝ)*(2/5)+1^2/2>4/5 ∧
    (11/10:ℝ)*(1/5)+(11/10)^2/2=33/40 ∧
    (18/25:ℝ)<33/40 ∧ (1:ℝ)*(1/5)+1^2/2≤3/4 := by
  norm_num [stoppingClearance]

theorem worst_case_delay (tau : ℝ) :
    (11/10:ℝ)*tau+121/200≤18/25 ↔ tau≤23/220 := by
  constructor <;> intro h <;> linarith

theorem uncertain_braking_guarantee (d v a tau : ℝ)
    (hd : d ∈ Set.Icc (18/25) (39/50)) (hv : v ∈ Set.Icc (9/10) (11/10))
    (ha : 1≤a) (ht : tau ∈ Set.Icc 0 (23/220)) :
    v*tau+v^2/(2*a)≤d := by
  have hv0 : 0≤v := by linarith [hv.1]
  have hs : v^2≤(11/10:ℝ)^2 := by nlinarith [hv.1,hv.2]
  have hquot : v^2/(2*a)≤121/200 := by
    apply (div_le_iff₀ (by linarith : 0<2*a)).2
    nlinarith
  have htravel := mul_le_mul_of_nonneg_right hv.2 ht.1
  have hb := (worst_case_delay tau).2 ht.2
  linarith [hd.1]

end SafeLearning.CompleteAppliedSystems
