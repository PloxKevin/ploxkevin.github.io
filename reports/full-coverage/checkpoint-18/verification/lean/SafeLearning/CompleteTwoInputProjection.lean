import Mathlib

set_option autoImplicit false
noncomputable section

namespace SafeLearning.CompleteTwoInputProjection

def objective (u : ℝ × ℝ) : ℝ := (1 / 2) * (u.1 ^ 2 + u.2 ^ 2)

def lagrangian (u : ℝ × ℝ) (mu : ℝ) : ℝ :=
  objective u + mu * (1 - u.1 - u.2)

theorem zero_infeasible : ¬ (1 ≤ (0 : ℝ) + 0) := by norm_num

theorem first_coordinate_derivative (u : ℝ × ℝ) (mu : ℝ) :
    HasDerivAt (fun x : ℝ => lagrangian (x, u.2) mu) (u.1 - mu) u.1 := by
  convert (((hasDerivAt_id u.1).pow 2).add_const (u.2 ^ 2)).const_mul (1 / 2) |>.add
    (((hasDerivAt_const u.1 (1 : ℝ)).sub (hasDerivAt_id u.1)).sub_const u.2 |>.const_mul mu)
    using 1
  · ext x
    simp [lagrangian, objective, id_eq] <;> ring
  · simp [id_eq] <;> ring

theorem second_coordinate_derivative (u : ℝ × ℝ) (mu : ℝ) :
    HasDerivAt (fun y : ℝ => lagrangian (u.1, y) mu) (u.2 - mu) u.2 := by
  convert ((hasDerivAt_const u.2 (u.1 ^ 2)).add ((hasDerivAt_id u.2).pow 2)).const_mul (1 / 2) |>.add
    ((hasDerivAt_const u.2 (1 - u.1)).sub (hasDerivAt_id u.2) |>.const_mul mu)
    using 1
  · ext y
    simp [lagrangian, objective, id_eq] <;> ring
  · simp [id_eq] <;> ring

theorem kkt_iff_exact_solution (u : ℝ × ℝ) (mu : ℝ) :
    (1 ≤ u.1 + u.2 ∧ 0 ≤ mu ∧ u.1 = mu ∧ u.2 = mu ∧
      mu * (1 - u.1 - u.2) = 0) ↔ u = (1 / 2, 1 / 2) ∧ mu = 1 / 2 := by
  constructor
  · rintro ⟨hf, hm, h1, h2, hc⟩
    have hpos : 0 < mu := by linarith
    have active : 1 - u.1 - u.2 = 0 := (mul_eq_zero.mp hc).resolve_left (ne_of_gt hpos)
    have he : mu = 1 / 2 := by linarith
    refine ⟨?_, he⟩
    exact Prod.ext (by simpa [he] using h1) (by simpa [he] using h2)
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem objective_remainder (u : ℝ × ℝ) :
    objective u - 1 / 4 =
      (1 / 4) * ((u.1 + u.2) ^ 2 - 1 + (u.1 - u.2) ^ 2) := by
  unfold objective
  ring

theorem unique_global_minimum (u : ℝ × ℝ) (hu : 1 ≤ u.1 + u.2) :
    objective (1 / 2, 1 / 2) = 1 / 4 ∧ 1 / 4 ≤ objective u ∧
      (objective u = 1 / 4 ↔ u = (1 / 2, 1 / 2)) := by
  have hs : 1 ≤ (u.1 + u.2) ^ 2 := by nlinarith
  have hd := sq_nonneg (u.1 - u.2)
  have hr := objective_remainder u
  refine ⟨by norm_num [objective], by nlinarith, ?_⟩
  constructor
  · intro he
    have same : u.1 = u.2 := by nlinarith
    have sum : u.1 + u.2 = 1 := by nlinarith
    exact Prod.ext (by linarith) (by linarith)
  · rintro rfl
    norm_num [objective]

theorem actual_strict_convexity :
    StrictConvexOn ℝ Set.univ objective := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hdiff : 0 < (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2 := by
    have hn1 := sq_nonneg (x.1 - y.1)
    have hn2 := sq_nonneg (x.2 - y.2)
    by_contra hn
    have e1 : x.1 = y.1 := by nlinarith
    have e2 : x.2 = y.2 := by nlinarith
    exact hxy (Prod.ext e1 e2)
  have hp : 0 < (1 / 2 : ℝ) * a * b *
      ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2) := by positivity
  have gap : a * objective x + b * objective y - objective (a • x + b • y) =
      (1 / 2) * a * b * ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2) := by
    have he : a = 1 - b := by linarith
    simp [objective, he, smul_eq_mul]
    ring
  simpa only [smul_eq_mul] using (show objective (a • x + b • y) <
    a * objective x + b * objective y by linarith)

end SafeLearning.CompleteTwoInputProjection
