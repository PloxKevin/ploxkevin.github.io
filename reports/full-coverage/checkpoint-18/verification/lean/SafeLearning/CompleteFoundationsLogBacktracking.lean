import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsLogBacktracking

def objective (x : ℝ) : ℝ := x-Real.log x

theorem actual_derivative (x : ℝ) (hx : 0<x) : HasDerivAt objective (1-x⁻¹) x := by
  exact (hasDerivAt_id x).sub (Real.hasDerivAt_log hx.ne')

theorem derivative_identification (x : ℝ) (hx : 0<x) : deriv objective x=1-x⁻¹ :=
  (actual_derivative x hx).deriv

theorem actual_second_derivative (x : ℝ) (hx : 0<x) :
    HasDerivAt (deriv objective) (1/x^2) x := by
  have hh : HasDerivAt (fun z : ℝ => 1-z⁻¹) (1/x^2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).inv hx.ne') using 1
    · ext z
      rfl
    · simp [one_div,neg_div]
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with z hz
  exact derivative_identification z hz

theorem second_derivative_identification (x : ℝ) (hx : 0<x) :
    deriv (deriv objective) x=1/x^2 := (actual_second_derivative x hx).deriv

theorem positive_hessian (x : ℝ) (hx : 0<x) : 0<deriv (deriv objective) x := by
  rw [second_derivative_identification x hx]
  positivity

theorem unique_global_minimum (x : ℝ) (hx : 0<x) :
    objective 1≤objective x ∧ (objective x=objective 1 ↔ x=1) := by
  have h1 : objective 1=1 := by simp [objective]
  rw [h1]
  constructor
  · have hh := Real.log_le_sub_one_of_pos hx
    unfold objective
    linarith
  · constructor
    · intro h
      by_contra hn
      have hh := Real.log_lt_sub_one_of_pos hx hn
      unfold objective at h
      linarith
    · rintro rfl
      simp [objective]

def newtonDirection (x : ℝ) : ℝ := -(deriv objective x)/deriv (deriv objective) x
def candidate (x t : ℝ) : ℝ := x+t*newtonDirection x
def accepted (x t : ℝ) : Prop := 0<candidate x t ∧
  objective (candidate x t)≤objective x+(1/4 : ℝ)*t*(deriv objective x*newtonDirection x)

theorem newton_direction_formula (x : ℝ) (hx : 0<x) :
    newtonDirection x=x-x^2 := by
  rw [newtonDirection,derivative_identification x hx,second_derivative_identification x hx]
  field_simp
  ring

theorem newton_equation (x : ℝ) (hx : 0<x) :
    deriv (deriv objective) x*newtonDirection x= -deriv objective x := by
  unfold newtonDirection
  field_simp [(positive_hessian x hx).ne']

theorem actual_descent_direction (x : ℝ) (hx : 0<x) (hne : x≠1) :
    deriv objective x*newtonDirection x<0 := by
  rw [derivative_identification x hx,newton_direction_formula x hx]
  field_simp
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]

theorem source_four_numerics :
    deriv objective 4=3/4 ∧ deriv (deriv objective) 4=1/16 ∧
    newtonDirection 4= -12 ∧ deriv objective 4*newtonDirection 4= -9 ∧
    candidate 4 1= -8 ∧ candidate 4 (1/2)= -2 ∧ candidate 4 (1/4)=1 := by
  norm_num [derivative_identification 4 (by norm_num),
    second_derivative_identification 4 (by norm_num),newton_direction_formula 4 (by norm_num),candidate]

theorem log_four_bounds : (13862943606/10^10 : ℝ)<Real.log 4 ∧
    Real.log 4<(13862943616/10^10 : ℝ) := by
  rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
  constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]

theorem source_armijo_decimal :
    |(objective 4+(1/4 : ℝ)*(1/4)*(deriv objective 4*newtonDirection 4))-2051206/10^6|<1/(2*10^6) := by
  rw [source_four_numerics.2.2.2.1]
  unfold objective
  rw [abs_lt]
  constructor <;> linarith [log_four_bounds.1,log_four_bounds.2]

theorem source_quarter_step_accepted : accepted 4 (1/4) := by
  unfold accepted
  rw [source_four_numerics.2.2.2.2.2.2]
  rw [source_four_numerics.2.2.2.1]
  constructor
  · norm_num
  · simp only [objective,Real.log_one,sub_zero]
    linarith [log_four_bounds.2]

theorem source_larger_steps_rejected : ¬accepted 4 1 ∧ ¬accepted 4 (1/2) := by
  constructor <;> intro h
  · have hh := h.1
    rw [source_four_numerics.2.2.2.2.1] at hh
    norm_num at hh
  · have hh := h.1
    rw [source_four_numerics.2.2.2.2.2.1] at hh
    norm_num at hh

theorem source_first_accepted_backtracking_index :
    IsLeast {k : ℕ | accepted 4 ((1/2 : ℝ)^k)} 2 := by
  constructor
  · convert source_quarter_step_accepted using 1 <;> norm_num
  · intro k hk
    by_contra h
    have hklt : k<2 := by omega
    interval_cases k
    · exact source_larger_steps_rejected.1 (by simpa using hk)
    · exact source_larger_steps_rejected.2 (by simpa using hk)

theorem source_accepted_step_is_global_optimum :
    candidate 4 (1/4)=1 ∧ ∀x : ℝ,0<x → objective (candidate 4 (1/4))≤objective x := by
  refine ⟨source_four_numerics.2.2.2.2.2.2,?_⟩
  rw [source_four_numerics.2.2.2.2.2.2]
  exact fun x hx => (unique_global_minimum x hx).1

def fullStep (x : ℝ) : ℝ := 2*x-x^2

theorem full_newton_step_formula (x : ℝ) (hx : 0<x) :
    candidate x 1=fullStep x ∧ 1-fullStep x=(1-x)^2 := by
  rw [candidate,newton_direction_formula x hx]
  unfold fullStep
  constructor <;> ring

theorem source_half_initial_iterations :
    (fullStep)^[1] (1/2)=3/4 ∧ (fullStep)^[2] (1/2)=15/16 ∧
    |(fullStep)^[3] (1/2)-99609/10^5|<1/(2*10^5) ∧
    |(fullStep)^[4] (1/2)-9999847/10^7|<1/(2*10^7) := by
  norm_num [Function.iterate_succ_apply',fullStep]

theorem full_step_preserves_half_open_unit_interval (x : ℝ) (hx : x∈Ioc 0 1) : fullStep x∈Ioc 0 1 := by
  have heq : fullStep x=x*(2-x) := by unfold fullStep;ring
  have hp : 0<fullStep x := by rw [heq];exact mul_pos hx.1 (by linarith [hx.2])
  have herror : 1-fullStep x=(1-x)^2 := by unfold fullStep;ring
  exact ⟨hp,by nlinarith [sq_nonneg (1-x)]⟩

theorem source_half_iteration_in_domain (n : ℕ) : (fullStep)^[n] (1/2)∈Ioc 0 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact full_step_preserves_half_open_unit_interval _ ih

theorem source_half_error_closed_form (n : ℕ) :
    1-(fullStep)^[n] (1/2)=(1/2 : ℝ)^(2^n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Function.iterate_succ_apply',
      (full_newton_step_formula _ (source_half_iteration_in_domain n).1).2,ih,
      show (2 : ℕ)^(n+1)=2^n*2 by rw [pow_succ],pow_mul]

theorem source_half_iteration_converges :
    Tendsto (fun n : ℕ => (fullStep)^[n] (1/2)) atTop (𝓝 1) := by
  have hexp : Tendsto (fun n : ℕ => 2^n) atTop atTop := by
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ)<2)
  have herr := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2)
    (by norm_num : (1/2 : ℝ)<1)).comp hexp
  have heq : (fun n : ℕ => (fullStep)^[n] (1/2))=
      (fun n : ℕ => 1-(1/2 : ℝ)^(2^n)) := by
    ext n
    linarith [source_half_error_closed_form n]
  rw [heq]
  simpa using tendsto_const_nhds.sub herr

theorem source_three_domain_checks :
    candidate 3 1= -3 ∧ candidate 3 (1/2)=0 ∧ candidate 3 (1/4)=3/2 ∧
    ¬accepted 3 1 ∧ ¬accepted 3 (1/2) := by
  have hd : newtonDirection 3= -6 := by rw [newton_direction_formula 3 (by norm_num)];norm_num
  have h1 : candidate 3 1= -3 := by norm_num [candidate,hd]
  have h2 : candidate 3 (1/2)=0 := by norm_num [candidate,hd]
  refine ⟨h1,h2,by norm_num [candidate,hd],?_,?_⟩
  · intro h
    have hh := h.1
    rw [h1] at hh
    norm_num at hh
  · intro h
    have hh := h.1
    rw [h2] at hh
    norm_num at hh

theorem log_three_bounds : |Real.log 3-109861228867/10^11|≤1/10^10 :=
  by convert Real.log_three_near_10 using 1 <;> norm_num

theorem source_three_quarter_accepted_and_decimals : accepted 3 (1/4) ∧
    |objective (candidate 3 (1/4))-1095/1000|<1/2000 ∧
    |(objective 3+(1/4 : ℝ)*(1/4)*(deriv objective 3*newtonDirection 3))-1651/1000|<1/2000 := by
  have hlog : Real.log (3/2)=Real.log 3-Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  have hl3 := abs_le.mp log_three_bounds
  have hc : candidate 3 (1/4)=3/2 := source_three_domain_checks.2.2.1
  have hg : deriv objective 3*newtonDirection 3= -4 := by
    rw [derivative_identification 3 (by norm_num),newton_direction_formula 3 (by norm_num)]
    norm_num
  refine ⟨?_,?_,?_⟩
  · unfold accepted
    rw [hc,hg]
    constructor
    · norm_num
    · unfold objective
      rw [hlog]
      linarith [Real.log_two_lt_d9]
  · rw [hc]
    unfold objective
    rw [hlog,abs_lt]
    constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]
  · rw [hg]
    unfold objective
    rw [abs_lt]
    constructor <;> linarith

end SafeLearning.CompleteFoundationsLogBacktracking
