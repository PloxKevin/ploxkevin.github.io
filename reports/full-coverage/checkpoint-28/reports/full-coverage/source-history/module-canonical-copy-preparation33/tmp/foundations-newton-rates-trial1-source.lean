import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace SafeLearning.CompleteFoundationsNewtonRates

def newtonStep (f : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / deriv f x
def regularObjective (x : ℝ) : ℝ := x ^ 2 - 1
def singularObjective (x : ℝ) : ℝ := x ^ 2
def singularOrbit (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem actual_regular_and_singular_objectives_have_their_literal_derivatives (x : ℝ) :
    HasDerivAt regularObjective (2 * x) x ∧
      HasDerivAt singularObjective (2 * x) x ∧
      deriv regularObjective 1 = 2 ∧ deriv singularObjective 0 = 0 := by
  have hr : HasDerivAt regularObjective (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1 <;> simp [regularObjective]
  have hs : HasDerivAt singularObjective (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp [singularObjective]
  refine ⟨hr, hs, ?_, ?_⟩
  · have h := ((hasDerivAt_id (1 : ℝ)).pow 2).sub_const 1
    simpa [regularObjective] using h.deriv
  · have h := (hasDerivAt_id (0 : ℝ)).pow 2
    simpa [singularObjective] using h.deriv

theorem actual_regular_newton_step_has_the_exact_quadratic_error
    (x : ℝ) (hx : x ≠ 0) :
    newtonStep regularObjective x = (x + 1 / x) / 2 ∧
      newtonStep regularObjective x - 1 = (x - 1) ^ 2 / (2 * x) := by
  have hd := (actual_regular_and_singular_objectives_have_their_literal_derivatives x).1.deriv
  simp only [newtonStep, hd, regularObjective]
  constructor <;> field_simp <;> ring

theorem actual_regular_newton_neighborhood_is_invariant_and_has_quadratic_error
    (x : ℝ) (hx : x ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
    newtonStep regularObjective x ∈ Icc (1 / 2 : ℝ) (3 / 2) ∧
      |newtonStep regularObjective x - 1| ≤ |x - 1| ^ 2 := by
  have hp : 0 < x := by linarith [hx.1]
  have he := (actual_regular_newton_step_has_the_exact_quadratic_error x hp.ne').2
  have hn : 0 ≤ newtonStep regularObjective x - 1 := by
    rw [he]
    positivity
  have hm : (2 * x) * (newtonStep regularObjective x - 1) = (x - 1) ^ 2 := by
    rw [he]
    field_simp
  have hb : (x - 1) ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg (by linarith [hx.1] : 0 ≤ x - 1 / 2)
      (by linarith [hx.2] : 0 ≤ 3 / 2 - x)]
  have hquad : newtonStep regularObjective x - 1 ≤ (x - 1) ^ 2 := by
    nlinarith [hx.1]
  constructor
  · constructor <;> linarith
  · rw [abs_of_nonneg hn, sq_abs]
    exact hquad

theorem actual_every_regular_newton_iterate_stays_in_the_neighborhood
    (initial : ℝ) (hinitial : initial ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
    ∀ n : ℕ, (newtonStep regularObjective)^[n] initial ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
  intro n
  induction n with
  | zero => simpa using hinitial
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (actual_regular_newton_neighborhood_is_invariant_and_has_quadratic_error _ ih).1

theorem actual_regular_newton_errors_have_a_geometric_envelope_and_converge
    (initial : ℝ) (hinitial : initial ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
    (∀ n : ℕ, |(newtonStep regularObjective)^[n] initial - 1| ≤ (1 / 2 : ℝ) ^ n * (1 / 2)) ∧
      Tendsto (fun n : ℕ => (newtonStep regularObjective)^[n] initial) atTop (𝓝 1) := by
  have hb : ∀ n : ℕ,
      |(newtonStep regularObjective)^[n] initial - 1| ≤ (1 / 2 : ℝ) ^ n * (1 / 2) := by
    intro n
    induction n with
    | zero =>
        simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
        rw [abs_le]
        constructor <;> linarith [hinitial.1, hinitial.2]
    | succ n ih =>
        have hbox := actual_every_regular_newton_iterate_stays_in_the_neighborhood initial hinitial n
        have hsmall : |(newtonStep regularObjective)^[n] initial - 1| ≤ 1 / 2 := by
          rw [abs_le]
          constructor <;> linarith [hbox.1, hbox.2]
        have hquad := (actual_regular_newton_neighborhood_is_invariant_and_has_quadratic_error
          _ hbox).2
        rw [Function.iterate_succ_apply', pow_succ]
        nlinarith [abs_nonneg ((newtonStep regularObjective)^[n] initial - 1)]
  refine ⟨hb, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2 : ℝ)
  apply squeeze_zero (fun _ => abs_nonneg _) hb
  simpa using ht

theorem actual_singular_newton_step_is_linear_for_every_nonzero_point
    (x : ℝ) (hx : x ≠ 0) : newtonStep singularObjective x = x / 2 := by
  have hd := (actual_regular_and_singular_objectives_have_their_literal_derivatives x).2.1.deriv
  simp only [newtonStep, hd, singularObjective]
  field_simp
  ring

theorem actual_singular_newton_orbit_starts_at_one_is_positive_and_converges :
    singularOrbit 0 = 1 ∧
      (∀ n : ℕ, 0 < singularOrbit n) ∧
      (∀ n : ℕ, singularOrbit (n + 1) = newtonStep singularObjective (singularOrbit n)) ∧
      Tendsto singularOrbit atTop (𝓝 0) := by
  have hp : ∀ n : ℕ, 0 < singularOrbit n := fun n => pow_pos (by norm_num) n
  refine ⟨by norm_num [singularOrbit], hp, ?_, ?_⟩
  · intro n
    rw [actual_singular_newton_step_is_linear_for_every_nonzero_point _ (hp n).ne']
    simp [singularOrbit, pow_succ, div_eq_mul_inv]
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem actual_singular_newton_errors_have_no_eventual_quadratic_constant :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, singularOrbit (n + 1) ≤ C * (singularOrbit n) ^ 2 := by
  rintro ⟨C, N, h⟩
  have ht : Tendsto (fun n : ℕ => C * singularOrbit n) atTop (𝓝 0) := by
    simpa using actual_singular_newton_orbit_starts_at_one_is_positive_and_converges.2.2.2.const_mul C
  have he : ∀ᶠ n : ℕ in atTop, C * singularOrbit n < 1 / 2 :=
    (tendsto_order.1 ht).2 _ (by norm_num)
  obtain ⟨n, hn, hN⟩ := (he.and (eventually_ge_atTop N)).exists
  have hb := h n hN
  have hp := actual_singular_newton_orbit_starts_at_one_is_positive_and_converges.2.1 n
  have hs : singularOrbit (n + 1) = singularOrbit n / 2 := by
    simp [singularOrbit, pow_succ, div_eq_mul_inv]
  rw [hs] at hb
  nlinarith

end SafeLearning.CompleteFoundationsNewtonRates
