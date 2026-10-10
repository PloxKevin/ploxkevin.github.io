import SafeLearning.CompleteAppliedSmallGainStorage

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SafeLearning.CompleteAppliedCubicSublevel

def field (state : ℝ) : ℝ := -state + state ^ 3
def storage (state : ℝ) : ℝ := state ^ 2
def denominator (initial time : ℝ) : ℝ :=
  initial ^ 2 + (1 - initial ^ 2) * Real.exp (2 * time)
def actualSolution (initial time : ℝ) : ℝ :=
  initial / Real.sqrt (denominator initial time)

theorem actual_polynomial_field_is_locally_lipschitz : LocallyLipschitz field := by
  have hf : ContDiff ℝ 1 field := by
    unfold field
    fun_prop
  exact hf.locallyLipschitz

theorem actual_storage_derivative_and_sublevel_decrease (state c : ℝ)
    (hc : state ^ 2 ≤ c) :
    HasDerivAt storage (2 * state) state ∧
      2 * state * field state = -2 * state ^ 2 * (1 - state ^ 2) ∧
      2 * state * field state ≤ -2 * (1 - c) * storage state := by
  refine ⟨?_, ?_, ?_⟩
  · convert (hasDerivAt_id state).pow 2 using 1 <;> first | rfl | norm_num
  · unfold field
    ring
  · unfold field storage
    nlinarith [sq_nonneg state]

theorem actual_boundary_derivative_is_strictly_negative (state c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hs : storage state = c) :
    2 * state * field state < 0 := by
  have h := (actual_storage_derivative_and_sublevel_decrease state c (by simpa [storage] using hs.le)).2.2
  rw [hs] at h
  have hp : 0 < (1 - c) * c := mul_pos (sub_pos.mpr hc1) hc0
  have hn : -2 * (1 - c) * c < 0 := by nlinarith
  exact h.trans_lt hn

theorem actual_forward_denominator_is_at_least_one (initial time : ℝ)
    (hi : initial ^ 2 ≤ 1) (ht : 0 ≤ time) :
    1 ≤ denominator initial time := by
  have he : 1 ≤ Real.exp (2 * time) := by
    simpa using Real.exp_le_exp.mpr (show 0 ≤ 2 * time by linarith)
  have hm := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hi)
  unfold denominator
  nlinarith

theorem actual_initial_condition (initial : ℝ) : actualSolution initial 0 = initial := by
  simp [actualSolution, denominator]

theorem actual_solution_has_the_true_cubic_ode (initial time : ℝ)
    (hden : 0 < denominator initial time) :
    HasDerivAt (actualSolution initial) (field (actualSolution initial time)) time := by
  have hd : HasDerivAt (denominator initial)
      ((1 - initial ^ 2) * (Real.exp (2 * time) * 2)) time := by
    convert (((Real.hasDerivAt_exp (2 * time)).comp time
      ((hasDerivAt_id time).const_mul 2)).const_mul
        (1 - initial ^ 2)).const_add (initial ^ 2) using 1 <;> first | rfl | ring
  have hsqrt : Real.sqrt (denominator initial time) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hden)
  convert (hasDerivAt_const time initial).div (hd.sqrt (ne_of_gt hden)) hsqrt using 1
  · rfl
  · dsimp [field, actualSolution]
    have hs := Real.sq_sqrt hden.le
    field_simp
    dsimp [denominator] at hs ⊢
    rw [hs]
    ring

theorem actual_global_solution_is_locally_absolutely_continuous (initial horizon : ℝ)
    (hi : initial ^ 2 ≤ 1) (hT : 0 ≤ horizon) :
    AbsolutelyContinuousOnInterval (actualSolution initial) 0 horizon := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  rw [uIcc_of_le hT]
  have hd : ContDiffOn ℝ 1 (denominator initial) (Icc 0 horizon) := by
    unfold denominator
    fun_prop
  have hs : ∀ time ∈ Icc 0 horizon, denominator initial time ≠ 0 := by
    intro time ht
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (actual_forward_denominator_is_at_least_one initial time hi ht.1))
  exact contDiffOn_const.div (hd.sqrt hs) (by
    intro time ht
    exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (actual_forward_denominator_is_at_least_one initial time hi ht.1))))

theorem actual_every_initial_in_the_closed_unit_sublevel_has_a_global_solution
    (initial : ℝ) (hi : initial ^ 2 ≤ 1) :
    actualSolution initial 0 = initial ∧
      (∀ horizon : ℝ, 0 ≤ horizon →
        AbsolutelyContinuousOnInterval (actualSolution initial) 0 horizon) ∧
      ∀ time : ℝ, 0 ≤ time →
        HasDerivAt (actualSolution initial) (field (actualSolution initial time)) time := by
  refine ⟨actual_initial_condition initial,
    fun horizon ht => actual_global_solution_is_locally_absolutely_continuous initial horizon hi ht,
    ?_⟩
  intro time ht
  apply actual_solution_has_the_true_cubic_ode
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (actual_forward_denominator_is_at_least_one initial time hi ht)

theorem actual_forward_solution_magnitude_does_not_exceed_initial_magnitude
    (initial time : ℝ) (hi : initial ^ 2 ≤ 1) (ht : 0 ≤ time) :
    |actualSolution initial time| ≤ |initial| := by
  have hd := actual_forward_denominator_is_at_least_one initial time hi ht
  have hs : 1 ≤ Real.sqrt (denominator initial time) := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hd)
  rw [actualSolution, abs_div, abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs)]
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs)).mpr
    (by nlinarith [abs_nonneg initial])

end SafeLearning.CompleteAppliedCubicSublevel
