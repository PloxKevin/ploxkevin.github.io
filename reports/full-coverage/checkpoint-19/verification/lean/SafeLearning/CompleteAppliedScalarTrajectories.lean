import SafeLearning.CompleteAppliedElementary
import SafeLearning.CompleteAppliedGridConfidence
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedScalarTrajectories
open Set Filter
open scoped Topology

theorem actual_three_input_recursion (x u : ℕ → ℝ)
    (h : ∀ n,x (n+1)=(1/2)*x n+u n) (hx : x 0=2)
    (hu0 : u 0=1) (hu1 : u 1=0) (hu2 : u 2=-1) :
    x 1=2 ∧ x 2=1 ∧ x 3=-1/2 := by
  have h1 : x 1=2 := by rw [h 0,hx,hu0];norm_num
  have h2 : x 2=1 := by rw [h 1,h1,hu1];norm_num
  have h3 : x 3=-1/2 := by rw [h 2,h2,hu2];norm_num
  exact ⟨h1,h2,h3⟩

theorem actual_constant_input_unique_equilibrium (x : ℝ) :
    x=(1/2)*x+1 ↔ x=2 := by constructor <;> intro h <;> linarith

theorem actual_feedback_closed_loop (x : ℝ) :
    (1/2)*x-(1/4)*x=(1/4)*x := by ring

theorem actual_feedback_unique_equilibrium (x : ℝ) :
    x=(1/2)*x-(1/4)*x ↔ x=0 := by constructor <;> intro h <;> linarith

theorem actual_feedback_recursion_solution_and_limit (x : ℕ → ℝ)
    (h : ∀ n,x (n+1)=(1/2)*x n-(1/4)*x n) :
    (∀ n,x n=(1/4:ℝ)^n*x 0) ∧ Tendsto x atTop (𝓝 0) := by
  have hf := SafeLearning.CompleteAppliedElementary.feedback_quarter_closed_form x h
  exact ⟨hf,(SafeLearning.CompleteAppliedElementary.feedback_quarter_converges (x 0)).congr
    (fun n => (hf n).symm)⟩

theorem actual_feedback_initial_four_readings (x : ℕ → ℝ)
    (h : ∀ n,x (n+1)=(1/2)*x n-(1/4)*x n) (hx : x 0=4) :
    x 0=4 ∧ x 1=1 ∧ x 2=1/4 ∧ x 3=1/16 := by
  have hf := (actual_feedback_recursion_solution_and_limit x h).1
  refine ⟨hx,?_,?_,?_⟩ <;> rw [hf,hx] <;> norm_num

theorem actual_scalar_derivative_comparison (x dx : ℝ → ℝ) (rate horizon : ℝ)
    (hc : ContinuousOn x (Icc 0 horizon))
    (hd : ∀ t ∈ Ico 0 horizon,HasDerivAt x (dx t) t)
    (hb : ∀ t ∈ Ico 0 horizon,dx t≤rate*x t) :
    ∀ t ∈ Icc 0 horizon,x t≤x 0*Real.exp (rate*t) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le (δ := x 0) (K := rate) (ε := 0) hc
    (fun t ht r hr => (hd t ht).hasDerivWithinAt.liminf_right_slope_le hr)
    (le_refl (x 0)) (by intro t ht;simpa using hb t ht)
  simpa only [gronwallBound_ε0,sub_zero] using h

theorem actual_negative_derivative_comparison (x dx : ℝ → ℝ) (rate horizon : ℝ)
    (hc : ContinuousOn x (Icc 0 horizon))
    (hd : ∀ t ∈ Ico 0 horizon,HasDerivAt x (dx t) t)
    (hb : ∀ t ∈ Ico 0 horizon,rate*x t≤dx t) :
    ∀ t ∈ Icc 0 horizon,x 0*Real.exp (rate*t)≤x t := by
  have h := actual_scalar_derivative_comparison (fun t => -x t) (fun t => -dx t)
    rate horizon hc.neg (fun t ht => (hd t ht).neg) (by intro t ht;nlinarith [hb t ht])
  intro t ht
  have hh := h t ht
  linarith

theorem actual_sublevel_entry_time (V dV : ℝ → ℝ) (horizon : ℝ)
    (hc : ContinuousOn V (Icc 0 horizon)) (h0 : V 0=4)
    (hd : ∀ t ∈ Ico 0 horizon,HasDerivAt V (dV t) t)
    (hb : ∀ t ∈ Ico 0 horizon,dV t≤-3*V t) :
    (∀ t ∈ Icc 0 horizon,V t≤4*Real.exp (-3*t)) ∧
    (∀ t ∈ Icc 0 horizon,Real.log 20/3≤t → V t≤1/5) := by
  have h := actual_scalar_derivative_comparison V dV (-3) horizon hc hd hb
  rw [h0] at h
  refine ⟨h,?_⟩
  intro t ht htime
  have hex : Real.exp (-3*t)≤1/20 := by
    have he : Real.exp (-Real.log (20:ℝ))=1/20 := by
      rw [Real.exp_neg,Real.exp_log (by norm_num)];norm_num
    rw [← he,Real.exp_le_exp]
    linarith
  linarith [h t ht]

theorem actual_sublevel_entry_time_rounding :
    |Real.log (20:ℝ)/3-(998577/1000000:ℝ)|≤1/2000000 := by
  have h := SafeLearning.CompleteAppliedGridConfidence.log400_enclosure
  have hl : Real.log (400:ℝ)=2*Real.log 20 := by
    rw [show (400:ℝ)=20*20 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hl] at h
  rw [abs_le]
  constructor <;> linarith [h.1,h.2]

theorem actual_safety_filter_constraint (x u : ℝ) :
    -u≥-2*(1-x) ↔ u≤2*(1-x) := by constructor <;> intro h <;> linarith

theorem actual_safety_filter_unique_projection (u : ℝ) (hu : u≤2*(1-(9/10:ℝ))) :
    ((1/5:ℝ)-1)^2≤(u-1)^2 ∧ (((1/5:ℝ)-1)^2=(u-1)^2 ↔ u=1/5) := by
  have h : u≤(1/5:ℝ) := by linarith
  constructor
  · nlinarith [sq_nonneg (u-1/5)]
  · constructor
    · intro he
      nlinarith [sq_nonneg (u-1/5)]
    · intro he;rw [he]

theorem actual_safe_boundary_inputs (u : ℝ) :
    u≤2*(1-(1:ℝ)) ↔ u≤0 := by norm_num

theorem actual_continuously_enforced_safety (x u : ℝ → ℝ) (horizon : ℝ)
    (hc : ContinuousOn x (Icc 0 horizon)) (h0 : x 0≤1)
    (hd : ∀ t ∈ Ico 0 horizon,HasDerivAt x (u t) t)
    (hu : ∀ t ∈ Ico 0 horizon,u t≤2*(1-x t)) :
    ∀ t ∈ Icc 0 horizon,(1-x 0)*Real.exp (-2*t)≤1-x t ∧ x t≤1 := by
  have h := actual_negative_derivative_comparison (fun t => 1-x t)
    (fun t => -u t) (-2) horizon (continuousOn_const.sub hc)
    (fun t ht => (hd t ht).const_sub 1) (by
      intro t ht
      change -2*(1-x t)≤-u t
      linarith [hu t ht])
  intro t ht
  have hh := h t ht
  exact ⟨hh,by nlinarith [Real.exp_pos (-2*t)]⟩

theorem actual_one_sample_check_is_insufficient :
    (∀ t : ℝ,HasDerivAt (fun s : ℝ => 9/10+(1/5)*s) (1/5) t) ∧
    (1/5:ℝ)≤2*(1-(9/10+(1/5)*0)) ∧ 1<(9/10:ℝ)+(1/5)*1 := by
  refine ⟨?_,by norm_num,by norm_num⟩
  intro t
  simpa using ((hasDerivAt_id t).const_mul (1/5:ℝ)).const_add (9/10:ℝ)

end SafeLearning.CompleteAppliedScalarTrajectories
