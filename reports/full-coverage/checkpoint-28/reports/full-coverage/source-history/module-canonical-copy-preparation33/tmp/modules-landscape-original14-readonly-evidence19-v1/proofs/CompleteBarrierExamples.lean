import Mathlib
import SafeLearning.CoreModules
import SafeLearning.CompleteCoreControl

namespace SafeLearning.CompleteBarrierExamples

open Set

theorem actual_safe_interval : {x : ℝ | 0 ≤ 1-x^2} = Icc (-1) 1 := by
  ext x
  exact SafeLearning.CoreModules.barrier_p1_safe_set x

theorem actual_safe_boundary : frontier {x : ℝ | 0 ≤ 1-x^2} = {-1, 1} := by
  rw [actual_safe_interval, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]

theorem barrier_values : (1-(1/2 : ℝ)^2 = 3/4) ∧
    (1-(1 : ℝ)^2 = 0) ∧ (1-(2 : ℝ)^2 = -3) := by norm_num

theorem allowed_input_at_half (u : ℝ) : 0 ≤ u+2*(1/2) ↔ -1 ≤ u := by
  constructor <;> intro h <;> linarith

theorem allowed_input_at_boundary (u : ℝ) : 0 ≤ u+2*0 ↔ 0 ≤ u := by simp

theorem approaching_boundary_restricts_inputs (x y u : ℝ)
    (hxy : x ≤ y) (hx : 0 ≤ u+2*x) : 0 ≤ u+2*y := by linarith

theorem explicit_feedback_initial (x₀ : ℝ) :
    1+(x₀-1)*Real.exp (-(0 : ℝ)) = x₀ := by simp

theorem explicit_feedback_derivative (x₀ t : ℝ) :
    HasDerivAt (fun s : ℝ => 1+(x₀-1)*Real.exp (-s))
      (1-(1+(x₀-1)*Real.exp (-t))) t := by
  convert (((hasDerivAt_id t).neg.exp).const_mul (x₀-1)).const_add 1 using 1 <;>
    (try ext s) <;> simp <;> ring

theorem boundary_inward : (0 : ℝ) < 1-0 ∧ 1-2 < (0 : ℝ) := by norm_num

theorem scalar_actuator_set (x : ℝ) :
    {u : ℝ | -1/5 ≤ u ∧ u ≤ 1/5 ∧ 0 ≤ -1+u+x} =
      Icc (max (-1/5) (1-x)) (1/5) := by
  ext u
  simp only [mem_setOf_eq, mem_Icc, max_le_iff]
  constructor
  · rintro ⟨a,b,c⟩
    exact ⟨⟨a,by linarith⟩,b⟩
  · rintro ⟨⟨a,c⟩,b⟩
    exact ⟨a,b,by linarith⟩

theorem infeasible_actuator_set :
    {u : ℝ | -1/5 ≤ u ∧ u ≤ 1/5 ∧ 0 ≤ -1+u+1/10} = ∅ := by
  ext u
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨_,b,c⟩
  linarith

theorem all_actuators_feasible_at_two :
    {u : ℝ | -1/5 ≤ u ∧ u ≤ 1/5 ∧ 0 ≤ -1+u+2} = Icc (-1/5) (1/5) := by
  ext u
  simp only [mem_setOf_eq, mem_Icc]
  constructor
  · rintro ⟨a,b,_⟩; exact ⟨a,b⟩
  · rintro ⟨a,b⟩; exact ⟨a,b,by linarith⟩

theorem no_global_actuator_certificate :
    ¬ ∀ x : ℝ, 0 ≤ x → ∃ u ∈ Icc (-1/5 : ℝ) (1/5), 0 ≤ -1+u+x := by
  intro h
  obtain ⟨u,hu,hc⟩ := h (1/10) (by norm_num)
  linarith [hu.2]

theorem robust_input_comparison :
    (∀ u : ℝ, (∀ w : ℝ, |w| ≤ 3/10 → 0 ≤ u+w+1/5) ↔ 1/10 ≤ u) ∧
    (∀ u : ℝ, 0 ≤ u+1/5 ↔ -1/5 ≤ u) ∧
    (1/10 : ℝ)-3/10 = -(1/5 : ℝ) := by
  constructor
  · intro u
    rw [SafeLearning.CoreModules.barrier_p7_robust]
    norm_num
  constructor
  · intro u; constructor <;> intro h <;> linarith
  · norm_num

theorem high_order_actual_auxiliary (p v u : ℝ → ℝ) (t : ℝ)
    (hp : HasDerivAt p (v t) t) (hv : HasDerivAt v (u t) t) :
    HasDerivAt (fun s => v s+p s) (u t+v t) t ∧
      (u t+v t)+(v t+p t) = u t+2*v t+p t := by
  exact ⟨hv.add hp, by ring⟩

theorem regular_defining_function_exposes_outward_derivative :
    HasDerivAt (fun x : ℝ => x) 1 0 ∧ (1 : ℝ)*(-1) < 0 := by
  exact ⟨hasDerivAt_id 0, by norm_num⟩

theorem held_affine_derivative (x₀ u t : ℝ) :
    HasDerivAt (fun s : ℝ => x₀+u*s) u t := by
  convert ((hasDerivAt_id t).const_mul u).const_add x₀ using 1 <;>
    (try ext s) <;> simp <;> ring

theorem held_ode_unique_on_interval (x : ℝ → ℝ) (x₀ u horizon : ℝ)
    (hc : ContinuousOn x (Icc 0 horizon)) (hi : x 0 = x₀)
    (hd : ∀ t ∈ Ico 0 horizon, HasDerivAt x u t) :
    ∀ t ∈ Icc 0 horizon, x t = x₀+u*t := by
  apply eq_of_has_deriv_right_eq
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t _ => (held_affine_derivative x₀ u t).hasDerivWithinAt) hc
    (by fun_prop)
  simpa using hi

theorem actual_held_interval_safety (x : ℝ → ℝ) (horizon : ℝ)
    (hT : 0 ≤ horizon) (hc : ContinuousOn x (Icc 0 horizon)) (hi : x 0 = 1)
    (hd : ∀ t ∈ Ico 0 horizon, HasDerivAt x (-1) t) :
    (∀ t ∈ Icc 0 horizon, 0 ≤ x t) ↔ horizon ≤ 1 := by
  have he := held_ode_unique_on_interval x 1 (-1) horizon hc hi hd
  have hm : (∀ t ∈ Icc 0 horizon, 0 ≤ x t) ↔
      (∀ t ∈ Icc 0 horizon, 0 ≤ 1-t) := by
    constructor <;> intro h t ht
    · simpa [he t ht] using h t ht
    · simpa [he t ht] using h t ht
  exact hm.trans (SafeLearning.CompleteCoreControl.held_first_interval_iff horizon hT)

def twoStepPlan (x u₀ u₁ : ℝ) : Prop :=
  |x| ≤ 1 ∧ |u₀| ≤ 1/2 ∧ |x+u₀| ≤ 1 ∧ |u₁| ≤ 1/2 ∧ |x+u₀+u₁| ≤ 1/4

theorem original_and_shifted_feasible_plans :
    twoStepPlan 1 (-1/2) (-1/4) ∧ twoStepPlan (1/2) (-1/4) (-1/4) := by
  norm_num [twoStepPlan]

theorem terminal_controller_invariant (x : ℝ) (hx : x ∈ Icc (-1/4 : ℝ) (1/4)) :
    (-x) ∈ Icc (-1/2 : ℝ) (1/2) ∧ x+(-x) ∈ Icc (-1/4 : ℝ) (1/4) := by
  constructor
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num

open SafeLearning.CoreModules

def robustSuccessor (s : ShieldState) (a : ShieldAction) (adverse : Bool) : ShieldState :=
  match s, a, adverse with
  | .b, .right, true => .failure
  | _, _, _ => successor s a

theorem exact_original_shield (s : ShieldState) (a : ShieldAction) :
    safe s ∧ safe (successor s a) ↔
      (s = .a ∧ a = .left) ∨ s = .b := by
  cases s <;> cases a <;> simp [safe,successor]

theorem exact_robust_shield (s : ShieldState) (a : ShieldAction) :
    safe s ∧ (∀ adverse : Bool, safe (robustSuccessor s a adverse)) ↔
      (s = .a ∨ s = .b) ∧ a = .left := by
  cases s <;> cases a <;> simp [safe,robustSuccessor,successor]

theorem exact_winning_set (s : ShieldState) :
    (∃ a : ShieldAction, safe s ∧ ∀ w : Bool, safe (robustSuccessor s a w)) ↔
      s = .a ∨ s = .b := by
  simp_rw [exact_robust_shield]
  cases s <;> simp

end SafeLearning.CompleteBarrierExamples
