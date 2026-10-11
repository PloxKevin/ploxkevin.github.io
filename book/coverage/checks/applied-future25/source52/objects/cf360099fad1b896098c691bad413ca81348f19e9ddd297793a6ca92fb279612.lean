import SafeLearning.CompleteCompactLyapunov
import SafeLearning.CompleteLyapunovCounterexample

namespace SafeLearning.CompleteLyapunovExerciseModels

noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators Matrix

theorem actual_linear_decrement (x : ℝ) :
    ((3 / 5 : ℝ) * x)^2 - x^2 = -(16 / 25 : ℝ) * x^2 := by ring

theorem actual_square_sublevel_four : {x : ℝ | x^2 ≤ 4} = Icc (-2) 2 := by
  ext x
  constructor
  · intro hx
    change x^2 ≤ 4 at hx
    constructor <;> nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2)]
  · rintro ⟨hl, hu⟩
    change x^2 ≤ 4
    nlinarith [mul_nonneg (show 0 ≤ 2-x by linarith) (show 0 ≤ x+2 by linarith)]

theorem actual_linear_sublevel_image :
    (fun x : ℝ => (3 / 5 : ℝ) * x) '' Icc (-2) 2 = Icc (-(6 / 5)) (6 / 5) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hl, hu⟩, rfl⟩
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    refine ⟨(5 / 3 : ℝ) * y, ⟨by linarith, by linarith⟩, ?_⟩
    ring

theorem actual_linear_image_is_inside_sublevel :
    Icc (-(6 / 5 : ℝ)) (6 / 5) ⊆ Icc (-2) 2 := by
  rintro x ⟨hl, hu⟩
  constructor <;> linarith

theorem actual_linear_decrease_iff_nonzero (x : ℝ) :
    ((3 / 5 : ℝ) * x)^2 < x^2 ↔ x ≠ 0 := by
  constructor
  · intro h hx
    simp [hx] at h
  · intro hx
    nlinarith [sq_pos_of_ne_zero hx]

theorem fixed_equilibrium_has_zero_decrement (F V : ℝ → ℝ) (hF : F 0 = 0) :
    V (F 0) - V 0 = 0 := by rw [hF]; ring

def actualQuadraticWeight : Matrix (Fin 2) (Fin 2) ℝ := !![4, 0; 0, 1]
def actualPoint (first second : ℝ) : Fin 2 → ℝ := ![first, second]
def actualWeightedValue (first second : ℝ) : ℝ :=
  actualPoint first second ⬝ᵥ (actualQuadraticWeight *ᵥ actualPoint first second)

theorem actual_weighted_quadratic_formula (first second : ℝ) :
    actualWeightedValue first second = 4 * first^2 + second^2 := by
  simp [actualWeightedValue, actualPoint, actualQuadraticWeight,
    dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem actual_ellipse_axis_intersections :
    {x : ℝ | actualWeightedValue x 0 ≤ 1} = Icc (-(1 / 2)) (1 / 2) ∧
    {y : ℝ | actualWeightedValue 0 y ≤ 1} = Icc (-1) 1 := by
  constructor <;> ext x <;> simp only [mem_setOf_eq, mem_Icc, actual_weighted_quadratic_formula]
  · constructor
    · intro h
      constructor <;> nlinarith [sq_nonneg (2*x-1), sq_nonneg (2*x+1)]
    · rintro ⟨hl, hu⟩
      nlinarith
  · constructor
    · intro h
      constructor <;> nlinarith [sq_nonneg (x-1), sq_nonneg (x+1)]
    · rintro ⟨hl, hu⟩
      nlinarith

theorem actual_ellipse_point_values :
    actualWeightedValue (2 / 5) (1 / 2) = 89 / 100 ∧
    actualWeightedValue (3 / 5) 0 = 36 / 25 := by
  norm_num [actual_weighted_quadratic_formula]

theorem actual_same_euclidean_length_different_certificates :
    (3 / 5 : ℝ)^2 + 0^2 = 0^2 + (3 / 5 : ℝ)^2 ∧
    1 < actualWeightedValue (3 / 5) 0 ∧ actualWeightedValue 0 (3 / 5) ≤ 1 := by
  norm_num [actual_weighted_quadratic_formula]

theorem actual_uncertain_successor_interval :
    (fun w : ℝ => (1 / 5 : ℝ) + w) '' Icc (-(1 / 10)) (1 / 10) =
      Icc (1 / 10) (3 / 10) := by
  ext y
  constructor
  · rintro ⟨w, ⟨hl, hu⟩, rfl⟩
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    refine ⟨y - 1 / 5, ⟨by linarith, by linarith⟩, ?_⟩
    ring

theorem actual_uncertain_decrease_maximum (w : ℝ) (hw : |w| ≤ 1 / 10) :
    ((1 / 5 : ℝ) + w)^2 ≤ 9 / 100 ∧
    ((1 / 5 : ℝ) + w)^2 - (2 / 5 : ℝ)^2 ≤ -(7 / 100) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hw
  constructor <;> nlinarith

theorem actual_uncertain_maximum_attained :
    |(1 / 10 : ℝ)| ≤ 1 / 10 ∧
    ((1 / 5 : ℝ) + 1 / 10)^2 = 9 / 100 ∧
    ((1 / 5 : ℝ) + 1 / 10)^2 - (2 / 5 : ℝ)^2 = -(7 / 100) := by norm_num

theorem actual_origin_disturbance_counterexample :
    |(1 / 10 : ℝ)| ≤ 1 / 10 ∧ (1 / 2 : ℝ) * 0 + 1 / 10 ≠ 0 ∧
    0 < ((1 / 2 : ℝ) * 0 + 1 / 10)^2 := by norm_num

theorem actual_origin_successor_interval :
    (fun w : ℝ => (1 / 2 : ℝ) * 0 + w) '' Icc (-(1 / 10)) (1 / 10) =
      Icc (-(1 / 10)) (1 / 10) := by simp

theorem actual_absolute_disturbance_all_time_counterexample :
    (∀ n : ℕ, |(1 / 10 : ℝ)| ≤ 1 / 10 ∧
      (1 / 5 : ℝ) = (1 / 2 : ℝ) * (1 / 5) + 1 / 10) ∧
    ¬Tendsto (fun _ : ℕ => (1 / 5 : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro n
    norm_num
  · intro h
    have he := tendsto_nhds_unique
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 5 : ℝ)) atTop (𝓝 (1 / 5))) h
    norm_num at he

theorem actual_expected_budget_and_slack :
    (1 / 5 : ℝ) + (1 / 2) * (4 / 5) = 3 / 5 ∧
    (1 / 5 : ℝ) + (1 / 2) * (4 / 5) ≤ 7 / 10 ∧
    (7 / 10 : ℝ) - ((1 / 5) + (1 / 2) * (4 / 5)) = 1 / 10 := by norm_num

theorem actual_sample_margin_transfer (trueDecrease estimate gain radius error : ℝ)
    (hdistance : |trueDecrease - estimate| ≤ error + gain * radius) :
    trueDecrease ≤ estimate + error + gain * radius := by
  have h := (abs_le.mp hdistance).2
  linarith

theorem actual_lipschitz_sample_transfer (decrease : ℝ → ℝ) (query sample estimate : ℝ)
    (radius error : ℝ) (hsample : |decrease sample - estimate| ≤ error)
    (hlipschitz : |decrease query - decrease sample| ≤ 5 * |query - sample|)
    (hdistance : |query - sample| ≤ radius) :
    decrease query ≤ estimate + error + 5 * radius := by
  have he := (abs_le.mp hsample).2
  have hl := (abs_le.mp hlipschitz).2
  linarith

theorem actual_grid_radius_bounds (decrease : ℝ → ℝ) (query sample estimate : ℝ)
    (hsample : |decrease sample - estimate| ≤ 1 / 50)
    (hlipschitz : |decrease query - decrease sample| ≤ 5 * |query - sample|)
    (hestimate : estimate ≤ -(3 / 25)) :
    (|query - sample| ≤ 1 / 100 → decrease query ≤ -(1 / 20)) ∧
    (|query - sample| ≤ 3 / 100 → decrease query ≤ 1 / 20) := by
  constructor <;> intro hd
  · have h := actual_lipschitz_sample_transfer decrease query sample estimate _ _ hsample hlipschitz hd
    linarith
  · have h := actual_lipschitz_sample_transfer decrease query sample estimate _ _ hsample hlipschitz hd
    linarith

theorem actual_coarse_grid_bound_allows_opposite_signs :
    (-(1 / 20 : ℝ) ≤ 1 / 20 ∧ -(1 / 20 : ℝ) < 0) ∧
    ((1 / 25 : ℝ) ≤ 1 / 20 ∧ 0 < (1 / 25 : ℝ)) := by norm_num

theorem actual_coarse_grid_compatible_positive_and_negative_models :
    let positiveModel : ℝ → ℝ := fun x => -(1 / 10) + 5*x
    let negativeModel : ℝ → ℝ := fun _ => -(1 / 10)
    (∀ x y, |positiveModel x-positiveModel y| ≤ 5*|x-y|) ∧
    (∀ x y, |negativeModel x-negativeModel y| ≤ 5*|x-y|) ∧
    |positiveModel 0-(-(3 / 25))| ≤ 1 / 50 ∧
    |negativeModel 0-(-(3 / 25))| ≤ 1 / 50 ∧
    positiveModel (3 / 100) = 1 / 20 ∧ negativeModel (3 / 100) = -(1 / 10) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have he : -(1 / 10 : ℝ)+5*x-(-(1 / 10)+5*y)=5*(x-y) := by ring
    rw [he, abs_mul]
    norm_num
  · intro x y
    simp only [sub_self, abs_zero]
    positivity
  all_goals norm_num

theorem actual_error_tube_one_step (e w : ℝ)
    (he : |e| ≤ 1 / 5) (hw : |w| ≤ 1 / 10) : |(1 / 2 : ℝ) * e + w| ≤ 1 / 5 := by
  obtain ⟨hel, heu⟩ := abs_le.mp he
  obtain ⟨hwl, hwu⟩ := abs_le.mp hw
  apply abs_le.mpr
  constructor <;> linarith

theorem actual_error_tube_all_time (e w : ℕ → ℝ) (hi : |e 0| ≤ 1 / 5)
    (hw : ∀ n, |w n| ≤ 1 / 10) (hstep : ∀ n, e (n + 1) = (1 / 2 : ℝ) * e n + w n) :
    ∀ n, |e n| ≤ 1 / 5 := by
  intro n
  induction n with
  | zero => exact hi
  | succ n ih => rw [hstep]; exact actual_error_tube_one_step _ _ ih (hw n)

theorem actual_nominal_state_and_input_tightening (z v e : ℝ)
    (he : |e| ≤ 1 / 5) (hz : |z| ≤ 4 / 5) (hv : |v| ≤ 9 / 10) :
    |z + e| ≤ 1 ∧ |v - (1 / 2 : ℝ) * e| ≤ 1 := by
  obtain ⟨hel, heu⟩ := abs_le.mp he
  obtain ⟨hzl, hzu⟩ := abs_le.mp hz
  obtain ⟨hvl, hvu⟩ := abs_le.mp hv
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

def actualMPCObjective (state input : ℝ) : ℝ := state^2 + input^2 + 2 * (state + input)^2

theorem actual_mpc_objective_derivative (state input : ℝ) :
    HasDerivAt (actualMPCObjective state) (6 * input + 4 * state) input := by
  convert (hasDerivAt_const input (state^2)).add ((hasDerivAt_id input).pow 2) |>.add
    (((hasDerivAt_const input state).add (hasDerivAt_id input)).pow 2 |>.const_mul 2) using 1 <;>
    (try ext z) <;> simp [actualMPCObjective] <;> ring

theorem actual_mpc_complete_square (state input : ℝ) :
    actualMPCObjective state input =
      3 * (input + 2 * state / 3)^2 + 5 * state^2 / 3 := by unfold actualMPCObjective; ring

theorem actual_mpc_unconstrained_unique_optimum (state input : ℝ) :
    actualMPCObjective state (-(2 * state / 3)) ≤ actualMPCObjective state input ∧
    (actualMPCObjective state input = actualMPCObjective state (-(2 * state / 3)) ↔
      input = -(2 * state / 3)) := by
  simp only [actual_mpc_complete_square]
  constructor
  · nlinarith [sq_nonneg (input + 2 * state / 3)]
  · constructor
    · intro h
      have hz : (input + 2 * state / 3)^2 = 0 := by nlinarith
      have hh := sq_eq_zero_iff.mp hz
      linarith
    · rintro rfl
      rfl

theorem actual_mpc_objective_strictly_convex (state : ℝ) :
    StrictConvexOn ℝ univ (actualMPCObjective state) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ huv a b ha hb hab
  have hgap : actualMPCObjective state (a*u+b*v) =
      a*actualMPCObjective state u+b*actualMPCObjective state v-3*a*b*(u-v)^2 := by
    have he : b = 1-a := by linarith
    rw [he]
    unfold actualMPCObjective
    ring
  have hp : 0 < 3*a*b*(u-v)^2 :=
    mul_pos (mul_pos (mul_pos (by norm_num) ha) hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr huv))
  simp only [smul_eq_mul]
  rw [hgap]
  linarith

theorem actual_mpc_constrained_unique_optimum (input : ℝ) (hi : |input| ≤ 1 / 2) :
    actualMPCObjective 1 (-(1 / 2)) ≤ actualMPCObjective 1 input ∧
    (actualMPCObjective 1 input = actualMPCObjective 1 (-(1 / 2)) ↔ input = -(1 / 2)) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hi
  have hg : actualMPCObjective 1 input - actualMPCObjective 1 (-(1 / 2)) =
      (input + 1 / 2) * (3 * input + 5 / 2) := by unfold actualMPCObjective; ring
  have hnonneg : 0 ≤ (input + 1 / 2) * (3 * input + 5 / 2) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · linarith
  · constructor
    · intro he
      have hz : (input + 1 / 2) * (3 * input + 5 / 2) = 0 := by linarith
      rcases mul_eq_zero.mp hz with h | h <;> linarith
    · rintro rfl
      rfl

theorem actual_mpc_numeric_solution :
    (-(2 / 3 : ℝ) < -(1 / 2)) ∧ |(-(1 / 2 : ℝ))| ≤ 1 / 2 ∧
    (1 : ℝ) + (-(1 / 2)) = 1 / 2 ∧ actualMPCObjective 1 (-(1 / 2)) = 7 / 4 := by
  norm_num [actualMPCObjective]

theorem actual_mpc_constrained_nearest_allowed_input (input : ℝ) (hi : |input| ≤ 1 / 2) :
    |(-(1 / 2 : ℝ))-(-(2 / 3))| ≤ |input-(-(2 / 3))| := by
  have hl := (abs_le.mp hi).1
  rw [abs_of_nonneg (by linarith : 0 ≤ input-(-(2 / 3 : ℝ)))]
  norm_num
  linarith

end
end SafeLearning.CompleteLyapunovExerciseModels
