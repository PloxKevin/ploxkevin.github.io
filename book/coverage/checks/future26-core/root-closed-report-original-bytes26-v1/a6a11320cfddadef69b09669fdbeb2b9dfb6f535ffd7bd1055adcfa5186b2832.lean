import Mathlib
import SafeLearning.CompleteLyapunovScenarioConvexSupport23
import SafeLearning.CompleteLyapunovScalarLinearScenarioRiskCumulative26

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteLyapunovChangedOptimizerSupport26
open CompleteLyapunovScenarioConvexSupport23 CompleteLyapunovScalarLinearScenarioRisk26

def removedFeasible {ι : Type*} (domain : Set ℝ) (constraints : ι → Set ℝ)
    (removedIndex : ι) : Set ℝ :=
  {x | x ∈ domain ∧ ∀ j, j ≠ removedIndex → x ∈ constraints j}

def linearSupportsAt {ι : Type*} (a : ℝ) (domain : Set ℝ)
    (constraints : ι → Set ℝ) (optimum : ℝ) (removedIndex : ι) : Prop :=
  ∃ x, x ∈ removedFeasible domain constraints removedIndex ∧ a*x < a*optimum

/-- Uniqueness belongs to the actual removed program, not to an arbitrary selected
point from a nonunique optimum set. Equal cost would make the original feasible
optimizer a second optimizer of that removed program. -/
theorem actual_changed_unique_removed_optimizer_iff_strict_objective_improvement
    {ι : Type*} (a : ℝ) (domain : Set ℝ) (constraints : ι → Set ℝ)
    (optimum removedOptimum : ℝ) (i : ι)
    (hopt : optimum ∈ feasible domain constraints)
    (hremovedMin : ∀ x ∈ removedFeasible domain constraints i, a*removedOptimum ≤ a*x)
    (hremovedUnique : ∀ x ∈ removedFeasible domain constraints i,
      a*x = a*removedOptimum → x = removedOptimum) :
    removedOptimum ≠ optimum ↔ a*removedOptimum < a*optimum := by
  have hoptRemoved : optimum ∈ removedFeasible domain constraints i :=
    ⟨hopt.1, fun j _ => hopt.2 j⟩
  constructor
  · intro hchanged
    have hle := hremovedMin optimum hoptRemoved
    by_contra hnot
    have heq : a*optimum = a*removedOptimum := le_antisymm (le_of_not_gt hnot) hle
    exact hchanged (hremovedUnique optimum hoptRemoved heq).symm
  · intro hstrict hequal
    rw [hequal] at hstrict
    exact (lt_irrefl _) hstrict

theorem actual_changed_unique_removed_optimizer_iff_actual_linear_support_witness
    {ι : Type*} (a : ℝ) (domain : Set ℝ) (constraints : ι → Set ℝ)
    (optimum removedOptimum : ℝ) (i : ι)
    (hopt : optimum ∈ feasible domain constraints)
    (hremovedMem : removedOptimum ∈ removedFeasible domain constraints i)
    (hremovedMin : ∀ x ∈ removedFeasible domain constraints i, a*removedOptimum ≤ a*x)
    (hremovedUnique : ∀ x ∈ removedFeasible domain constraints i,
      a*x = a*removedOptimum → x = removedOptimum) :
    removedOptimum ≠ optimum ↔ linearSupportsAt a domain constraints optimum i := by
  rw [actual_changed_unique_removed_optimizer_iff_strict_objective_improvement
    a domain constraints optimum removedOptimum i hopt hremovedMin hremovedUnique]
  constructor
  · intro hstrict
    exact ⟨removedOptimum, hremovedMem, hstrict⟩
  · rintro ⟨x, hx, hstrict⟩
    exact (hremovedMin x hx).trans_lt hstrict

theorem actual_linear_support_witness_iff_selected_oriented_support
    {ι : Type*} (a : ℝ) (ha : a ≠ 0) (domain : Set ℝ)
    (constraints : ι → Set ℝ) (optimum : ℝ) (i : ι) :
    linearSupportsAt a domain constraints optimum i ↔
      supportsAt (orientedSet a domain) (fun j => orientedSet a (constraints j))
        (a*optimum) i := by
  constructor
  · rintro ⟨x, hx, hstrict⟩
    refine ⟨a*x, ?_, ?_, hstrict⟩
    · simpa [orientedSet, ha] using hx.1
    · intro j hj
      simpa [orientedSet, ha] using hx.2 j hj
  · rintro ⟨y, hyd, hyc, hstrict⟩
    refine ⟨y/a, ⟨hyd, hyc⟩, ?_⟩
    have heq : a*(y/a) = y := by field_simp [ha]
    simpa only [heq] using hstrict

/-- The literal changed-optimizer support set, for either sign of the original
linear objective and even the genuinely unique zero-objective case, inherits the
actual scalar convex support bound. -/
theorem actual_unique_removed_scalar_linear_programs_have_at_most_one_changed_optimizer
    {ι : Type*} (a : ℝ) (domain : Set ℝ) (constraints : ι → Set ℝ)
    (optimum : ℝ) (removedOptimum : ι → ℝ)
    (hconv : ∀ i, Convex ℝ (constraints i))
    (hoptMem : optimum ∈ feasible domain constraints)
    (hoptMin : ∀ x ∈ feasible domain constraints, a*optimum ≤ a*x)
    (hremovedMem : ∀ i, removedOptimum i ∈ removedFeasible domain constraints i)
    (hremovedMin : ∀ i, ∀ x ∈ removedFeasible domain constraints i,
      a*removedOptimum i ≤ a*x)
    (hremovedUnique : ∀ i, ∀ x ∈ removedFeasible domain constraints i,
      a*x = a*removedOptimum i → x = removedOptimum i) :
    Set.Subsingleton {i | removedOptimum i ≠ optimum} := by
  by_cases ha : a = 0
  · intro i hi j hj
    have hoptRemoved : optimum ∈ removedFeasible domain constraints i :=
      ⟨hoptMem.1, fun k _ => hoptMem.2 k⟩
    have heq : optimum = removedOptimum i :=
      hremovedUnique i optimum hoptRemoved (by simp [ha])
    exact (hi heq.symm).elim
  · have hleast : IsLeast
        (feasible (orientedSet a domain) (fun i => orientedSet a (constraints i)))
        (a*optimum) := by
      constructor
      · change (a*optimum)/a ∈ domain ∧ ∀ i, (a*optimum)/a ∈ constraints i
        simpa [ha, feasible] using hoptMem
      · intro y hy
        have h := hoptMin (y/a) ⟨hy.1, hy.2⟩
        have heq : a*(y/a) = y := by field_simp [ha]
        simpa only [heq] using h
    have hconvOriented : ∀ i, Convex ℝ (orientedSet a (constraints i)) :=
      fun i => actual_linear_objective_constraint_orientation_preserves_convexity
        a (constraints i) (hconv i)
    have hsub := actual_general_convex_scalar_support_set_has_at_most_one_element
      (orientedSet a domain) (fun i => orientedSet a (constraints i)) (a*optimum)
      hconvOriented hleast
    have hs (i : ι) (hi : removedOptimum i ≠ optimum) :
        supportsAt (orientedSet a domain) (fun j => orientedSet a (constraints j))
          (a*optimum) i := by
      apply (actual_linear_support_witness_iff_selected_oriented_support
        a ha domain constraints optimum i).mp
      exact (actual_changed_unique_removed_optimizer_iff_actual_linear_support_witness
        a domain constraints optimum (removedOptimum i) i hoptMem (hremovedMem i)
        (hremovedMin i) (hremovedUnique i)).mp hi
    intro i hi j hj
    exact hsub (hs i hi) (hs j hj)

theorem actual_finite_changed_optimizer_support_count_is_at_most_one
    {ι : Type*} [Fintype ι] (a : ℝ) (domain : Set ℝ) (constraints : ι → Set ℝ)
    (optimum : ℝ) (removedOptimum : ι → ℝ)
    (hconv : ∀ i, Convex ℝ (constraints i))
    (hoptMem : optimum ∈ feasible domain constraints)
    (hoptMin : ∀ x ∈ feasible domain constraints, a*optimum ≤ a*x)
    (hremovedMem : ∀ i, removedOptimum i ∈ removedFeasible domain constraints i)
    (hremovedMin : ∀ i, ∀ x ∈ removedFeasible domain constraints i,
      a*removedOptimum i ≤ a*x)
    (hremovedUnique : ∀ i, ∀ x ∈ removedFeasible domain constraints i,
      a*x = a*removedOptimum i → x = removedOptimum i) :
    (Finset.univ.filter (fun i => removedOptimum i ≠ optimum)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact actual_unique_removed_scalar_linear_programs_have_at_most_one_changed_optimizer
    a domain constraints optimum removedOptimum hconv hoptMem hoptMin
    hremovedMem hremovedMin hremovedUnique
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

end SafeLearning.CompleteLyapunovChangedOptimizerSupport26
