import Mathlib

namespace SafeLearning.CompleteBarrierTrajectories

noncomputable section
open Set

theorem stable_linear_ode_unique (x : ℝ → ℝ) (c x₀ horizon : ℝ)
    (hc : ContinuousOn x (Icc 0 horizon)) (hi : x 0 = x₀)
    (hd : ∀ t ∈ Ico 0 horizon, HasDerivAt x (c-x t) t) :
    ∀ t ∈ Icc 0 horizon, x t = c+(x₀-c)*Real.exp (-t) := by
  have hgcont : ContinuousOn (fun t => Real.exp t*(x t-c)) (Icc 0 horizon) :=
    Real.continuous_exp.continuousOn.mul (hc.sub continuousOn_const)
  have hgderiv : ∀ t ∈ Ico 0 horizon,
      HasDerivWithinAt (fun t => Real.exp t*(x t-c)) 0 (Ici t) t := by
    intro t ht
    have h : HasDerivAt (fun t => Real.exp t*(x t-c)) 0 t := by
      convert (Real.hasDerivAt_exp t).mul ((hd t ht).sub_const c) using 1 <;> ring
    exact h.hasDerivWithinAt
  have hg := constant_of_has_deriv_right_zero hgcont hgderiv
  intro t ht
  have he : Real.exp t*(x t-c) = x₀-c := by simpa [hi] using hg t ht
  have hp : Real.exp t*Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have hz : (Real.exp t*(x t-c))*Real.exp (-t) = x t-c := by
    calc
      _ = (x t-c)*(Real.exp t*Real.exp (-t)) := by ring
      _ = x t-c := by rw [hp]; ring
  rw [he] at hz
  linarith

theorem actual_unit_equilibrium_trajectory (x : ℝ → ℝ) (x₀ horizon : ℝ)
    (hc : ContinuousOn x (Icc 0 horizon)) (hi : x 0 = x₀)
    (hd : ∀ t ∈ Ico 0 horizon, HasDerivAt x (1-x t) t) :
    ∀ t ∈ Icc 0 horizon, x t = 1+(x₀-1)*Real.exp (-t) :=
  stable_linear_ode_unique x 1 x₀ horizon hc hi hd

theorem actual_zero_equilibrium_trajectory (x : ℝ → ℝ) (horizon : ℝ)
    (hc : ContinuousOn x (Icc 0 horizon)) (hi : x 0 = 1)
    (hd : ∀ t ∈ Ico 0 horizon, HasDerivAt x (-x t) t) :
    ∀ t ∈ Icc 0 horizon, x t = Real.exp (-t) := by
  simpa using stable_linear_ode_unique x 0 1 horizon hc hi (by simpa using hd)

theorem unit_equilibrium_vector_field_lipschitz :
    LipschitzWith 1 (fun x : ℝ => 1-x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  have he : 1-x-(1-y) = -(x-y) := by ring
  rw [he, abs_neg]
  simp

theorem unit_equilibrium_vector_field_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => 1-x) := by fun_prop

theorem cubic_actual_derivative (x : ℝ) :
    HasDerivAt (fun x : ℝ => x^3) (3*x^2) x := by
  convert (hasDerivAt_id x).pow 3 using 1 <;> (try ext y) <;> simp

def position (t : ℝ) : ℝ := (1/10-9/10*t)*Real.exp (-t)
def velocity (t : ℝ) : ℝ := (-1+9/10*t)*Real.exp (-t)
def acceleration (t : ℝ) : ℝ := (19/10-9/10*t)*Real.exp (-t)

theorem counterexample_position_ode (t : ℝ) : HasDerivAt position (velocity t) t := by
  unfold position velocity
  convert (((hasDerivAt_const t (1/10 : ℝ)).sub
    ((hasDerivAt_id t).const_mul (9/10))).mul ((hasDerivAt_id t).neg.exp)) using 1 <;>
    (try ext s) <;> simp <;> ring

theorem counterexample_velocity_ode (t : ℝ) : HasDerivAt velocity (acceleration t) t := by
  unfold velocity acceleration
  convert (((hasDerivAt_const t (-1 : ℝ)).add
    ((hasDerivAt_id t).const_mul (9/10))).mul ((hasDerivAt_id t).neg.exp)) using 1 <;>
    (try ext s) <;> simp <;> ring

theorem final_auxiliary_identically_zero (t : ℝ) :
    acceleration t+2*velocity t+position t = 0 := by
  unfold acceleration velocity position
  ring

theorem auxiliary_initial_assumption_is_necessary :
    position 0 = 1/10 ∧ velocity 0 = -1 ∧ position 0+velocity 0 < 0 ∧
      (∀ t : ℝ, 0 ≤ acceleration t+2*velocity t+position t) ∧ position 1 < 0 := by
  constructor
  · norm_num [position]
  constructor
  · norm_num [velocity]
  constructor
  · norm_num [position,velocity]
  constructor
  · intro t; rw [final_auxiliary_identically_zero]
  · unfold position
    nlinarith [Real.exp_pos (-(1 : ℝ))]

end
end SafeLearning.CompleteBarrierTrajectories
