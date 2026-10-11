import SafeLearning.CompleteAppliedGlobalLipschitzPicard

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SafeLearning.CompleteAppliedGlobalLipschitzTrajectory
open CompleteAppliedGlobalLipschitzPicard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private def origin (n : ℕ) : Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) :=
  ⟨0, by constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n]⟩

def finiteSolution (field : E → E) (initial : E) (K : ℝ≥0)
    (hfield : LipschitzWith K field) (n : ℕ) : ℝ → E :=
  Classical.choose (actual_globally_lipschitz_field_has_a_genuine_finite_interval_integral_solution
    (origin n) field initial K hfield)

theorem actual_finite_solution_has_derived_integral_and_differential_properties
    (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field) (n : ℕ) :
    Continuous (finiteSolution field initial K hfield n) ∧
      finiteSolution field initial K hfield n 0 = initial ∧
      (∀ time ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
        finiteSolution field initial K hfield n time = initial +
          ∫ t in (0 : ℝ)..time, field (finiteSolution field initial K hfield n t)) ∧
      ∀ time ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
        HasDerivAt (finiteSolution field initial K hfield n)
          (field (finiteSolution field initial K hfield n time)) time :=
  Classical.choose_spec (actual_globally_lipschitz_field_has_a_genuine_finite_interval_integral_solution
    (origin n) field initial K hfield)

theorem actual_chosen_finite_solutions_agree_where_both_time_bounds_apply
    (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field)
    (n m : ℕ) (time : ℝ) (hn : |time| ≤ (n : ℝ)) (hm : |time| ≤ (m : ℝ)) :
    finiteSolution field initial K hfield n time = finiteSolution field initial K hfield m time := by
  have hs := actual_finite_solution_has_derived_integral_and_differential_properties
    field initial K hfield n
  have ht := actual_finite_solution_has_derived_integral_and_differential_properties
    field initial K hfield m
  let radius := min ((n : ℝ) + 1) ((m : ℝ) + 1)
  have hr : 0 < radius := lt_min (by positivity) (by positivity)
  have htime : |time| < radius := lt_min (by linarith) (by linarith)
  have hnm : ∀ t ∈ Ioo (-radius) radius,
      t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) ∧
        t ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) := by
    intro t h
    have hleft : radius ≤ (n : ℝ) + 1 := min_le_left _ _
    have hright : radius ≤ (m : ℝ) + 1 := min_le_right _ _
    constructor <;> constructor <;> linarith [h.1, h.2]
  have hu := ODE_solution_unique_of_mem_Ioo (K := K) (v := fun _ => field)
    (s := fun _ => univ)
    (fun _ _ => hfield.lipschitzOnWith)
    (show (0 : ℝ) ∈ Ioo (-radius) radius by constructor <;> linarith)
    (fun t h => ⟨hs.2.2.2 t (hnm t h).1, mem_univ _⟩)
    (fun t h => ⟨ht.2.2.2 t (hnm t h).2, mem_univ _⟩)
    (hs.2.1.trans ht.2.1.symm)
  exact hu (abs_lt.mp htime)

def globalSolution (field : E → E) (initial : E) (K : ℝ≥0)
    (hfield : LipschitzWith K field) (time : ℝ) : E :=
  finiteSolution field initial K hfield (Nat.ceil |time|) time

theorem actual_global_solution_agrees_with_any_applicable_finite_solution
    (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field)
    (n : ℕ) (time : ℝ) (ht : |time| ≤ (n : ℝ)) :
    globalSolution field initial K hfield time = finiteSolution field initial K hfield n time :=
  actual_chosen_finite_solutions_agree_where_both_time_bounds_apply field initial K hfield
    (Nat.ceil |time|) n time (Nat.le_ceil _) ht

theorem actual_global_solution_has_the_true_ode_at_every_real_time
    (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field) (time : ℝ) :
    HasDerivAt (globalSolution field initial K hfield)
      (field (globalSolution field initial K hfield time)) time := by
  let n := Nat.ceil (|time| + 1)
  have hn : |time| < (n : ℝ) := by
    have h := Nat.le_ceil (|time| + 1)
    dsimp [n]
    linarith
  have heq : globalSolution field initial K hfield =ᶠ[𝓝 time]
      finiteSolution field initial K hfield n := by
    filter_upwards [continuous_abs.continuousAt.eventually (eventually_lt_nhds hn)] with t ht
    exact actual_global_solution_agrees_with_any_applicable_finite_solution
      field initial K hfield n t ht.le
  have hs := actual_finite_solution_has_derived_integral_and_differential_properties
    field initial K hfield n
  have hmem : time ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    have h := abs_lt.mp hn
    constructor <;> linarith [h.1, h.2]
  rw [actual_global_solution_agrees_with_any_applicable_finite_solution field initial K hfield n time hn.le]
  exact (hs.2.2.2 time hmem).congr_of_eventuallyEq heq

theorem actual_global_solution_initial_condition
    (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field) :
    globalSolution field initial K hfield 0 = initial := by
  rw [actual_global_solution_agrees_with_any_applicable_finite_solution
    field initial K hfield 0 0 (by norm_num)]
  exact (actual_finite_solution_has_derived_integral_and_differential_properties
    field initial K hfield 0).2.1

theorem actual_global_solution_is_c1_and_locally_absolutely_continuous
    (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field) :
    ContDiff ℝ 1 (globalSolution field initial K hfield) ∧
      ∀ a b : ℝ, AbsolutelyContinuousOnInterval (globalSolution field initial K hfield) a b := by
  have hd := actual_global_solution_has_the_true_ode_at_every_real_time field initial K hfield
  have hdiff : Differentiable ℝ (globalSolution field initial K hfield) :=
    fun time => (hd time).differentiableAt
  have hderiv : deriv (globalSolution field initial K hfield) =
      fun time => field (globalSolution field initial K hfield time) := funext (fun time => (hd time).deriv)
  have hc : ContDiff ℝ 1 (globalSolution field initial K hfield) :=
    contDiff_one_iff_deriv.mpr ⟨hdiff, by rw [hderiv]; exact hfield.continuous.comp hdiff.continuous⟩
  exact ⟨hc, fun a b => hc.contDiffOn.absolutelyContinuousOnInterval⟩

theorem actual_globally_lipschitz_autonomous_field_has_a_constructed_global_solution
    (field : E → E) (initial : E) (K : ℝ≥0) (hfield : LipschitzWith K field) :
    ∃ path : ℝ → E,
      path 0 = initial ∧ (∀ a b : ℝ, AbsolutelyContinuousOnInterval path a b) ∧
        ∀ time : ℝ, HasDerivAt path (field (path time)) time :=
  ⟨globalSolution field initial K hfield,
    actual_global_solution_initial_condition field initial K hfield,
    (actual_global_solution_is_c1_and_locally_absolutely_continuous field initial K hfield).2,
    actual_global_solution_has_the_true_ode_at_every_real_time field initial K hfield⟩

end SafeLearning.CompleteAppliedGlobalLipschitzTrajectory
