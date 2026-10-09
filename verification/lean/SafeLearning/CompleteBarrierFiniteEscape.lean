import Mathlib

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteBarrierFiniteEscape

def reciprocalState (t : ℝ) : ℝ := 1-Real.exp t/2
def escapingState (t : ℝ) : ℝ := 1/reciprocalState t

theorem genuine_reciprocal_positive_before_escape (t : ℝ) (ht : t<Real.log 2) :
    0<reciprocalState t := by
  have h : Real.exp t < (2:ℝ) := by
    have h := Real.exp_lt_exp.mpr ht
    rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at h
    exact h
  dsimp [reciprocalState]
  linarith

theorem genuine_reciprocal_derivative (t : ℝ) :
    HasDerivAt reciprocalState (reciprocalState t-1) t := by
  convert (hasDerivAt_const t (1:ℝ)).sub ((Real.hasDerivAt_exp t).div_const 2) using 1 <;>
    (try ext s) <;> dsimp [reciprocalState] <;> ring

theorem genuine_escaping_state_solves_actual_ODE (t : ℝ) (ht : t<Real.log 2) :
    HasDerivAt escapingState (-escapingState t+escapingState t^2) t := by
  have hy := (genuine_reciprocal_positive_before_escape t ht).ne'
  convert (genuine_reciprocal_derivative t).inv hy using 1
  · ext s; simp [escapingState,one_div]
  · dsimp [escapingState]
    field_simp
    ring

theorem actual_initial_condition_and_bounded_disturbance :
    escapingState 0 = 2 ∧ ∀ t : ℝ, |(fun _ : ℝ => (1:ℝ)) t| ≤ 1 := by
  norm_num [escapingState,reciprocalState]

theorem genuine_any_positive_time_before_escape_is_unsafe (t : ℝ)
    (ht0 : 0<t) (ht : t<Real.log 2) : 2<escapingState t := by
  have hy := genuine_reciprocal_positive_before_escape t ht
  have he : (1:ℝ)<Real.exp t := by simpa using Real.exp_lt_exp.mpr ht0
  change (2:ℝ)<1/reciprocalState t
  rw [lt_div_iff₀ hy]
  dsimp [reciprocalState]
  linarith

theorem genuine_finite_time_escape :
    0<Real.log (2:ℝ) ∧ Tendsto escapingState (𝓝[<] Real.log 2) atTop := by
  refine ⟨Real.log_pos (by norm_num),?_⟩
  have hy : Tendsto reciprocalState (𝓝[<] Real.log 2) (𝓝 (0:ℝ)) := by
    have hc : Continuous reciprocalState := by unfold reciprocalState; fun_prop
    have hzero : reciprocalState (Real.log 2) = 0 := by
      simp only [reciprocalState,Real.exp_log (by norm_num : (0:ℝ)<2)]
      norm_num
    rw [← hzero]
    exact (hc.tendsto (Real.log 2)).mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[<] Real.log (2:ℝ), reciprocalState t ∈ Ioi (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact genuine_reciprocal_positive_before_escape t ht
  change Tendsto (fun t : ℝ => 1/reciprocalState t) (𝓝[<] Real.log 2) atTop
  simpa only [one_div,Function.comp_def] using tendsto_inv_nhdsGT_zero.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hy,hpos⟩)

theorem genuine_small_disturbance_boundary_points_inward (r d : ℝ)
    (hr : 0≤r) (hr1 : r≤1/4) (hd : |d|≤r) :
    -(2+r)+(2+r)^2*d ≤ (2+r)*(-1+(9/4)*(1/4)) ∧
      (2+r)*(-1+(9/4)*(1/4)) < 0 := by
  have hd1 : d≤r := (le_abs_self d).trans hd
  have hx : 0<2+r := by linarith
  have hxr : (2+r)*r ≤ (9/4)*(1/4) :=
    mul_le_mul (by linarith) hr1 hr (by norm_num)
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hd1 (sq_nonneg (2+r))
    have h2 := mul_le_mul_of_nonneg_left hxr hx.le
    nlinarith
  · nlinarith

/-- Every existing differentiable trajectory has the local inflated-set guarantee.
No existence or all-time continuation is assumed as a conclusion. -/
theorem genuine_differentiable_local_inflated_set_invariance
    (x d : ℝ → ℝ) (r T : ℝ) (hr : 0≤r) (hr1 : r≤1/4)
    (hc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (-x t+x t^2*d t) (Ici t) t)
    (hd : ∀ t ∈ Ico 0 T, |d t|≤r) (h0 : x 0≤2+r) :
    ∀ t ∈ Icc 0 T, x t≤2+r := by
  apply image_le_of_deriv_right_lt_deriv_boundary hc hx h0
    (fun t => hasDerivAt_const t (2+r))
  intro t ht hb
  rw [hb]
  exact (genuine_small_disturbance_boundary_points_inward r (d t) hr hr1 (hd t ht)).1.trans_lt
    (genuine_small_disturbance_boundary_points_inward r (d t) hr hr1 (hd t ht)).2

theorem genuine_large_disturbance_points_outward (r x : ℝ)
    (hr : 1/2≤r) (hx : 2<x) : 0< -x+x^2*r := by
  have hmul : (1/2)*x ≤ r*x := mul_le_mul_of_nonneg_right hr (by linarith)
  have h : 1<x*r := by nlinarith
  have hpos := mul_pos (by linarith : 0<x) (sub_pos.mpr h)
  nlinarith

end SafeLearning.CompleteBarrierFiniteEscape
