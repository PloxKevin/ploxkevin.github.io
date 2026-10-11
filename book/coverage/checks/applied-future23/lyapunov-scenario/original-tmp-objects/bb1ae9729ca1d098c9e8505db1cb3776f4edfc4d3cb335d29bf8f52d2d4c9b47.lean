import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteLyapunovScenarioConvexSupport23

def feasible {ι : Type*} (domain : Set ℝ) (constraints : ι → Set ℝ) : Set ℝ :=
  {x | x ∈ domain ∧ ∀ i, x ∈ constraints i}

/-- Removing one actual sampled constraint permits a strictly smaller scalar objective. -/
def supportsAt {ι : Type*} (domain : Set ℝ) (constraints : ι → Set ℝ)
    (optimum : ℝ) (i : ι) : Prop :=
  ∃ x : ℝ, x ∈ domain ∧ (∀ j, j ≠ i → x ∈ constraints j) ∧ x < optimum

theorem actual_two_distinct_convex_scalar_constraints_cannot_both_support
    {ι : Type*} (domain : Set ℝ) (constraints : ι → Set ℝ) (optimum : ℝ)
    (hc : ∀ i, Convex ℝ (constraints i))
    (hopt : IsLeast (feasible domain constraints) optimum)
    (i j : ι) (hij : i ≠ j)
    (hi : supportsAt domain constraints optimum i)
    (hj : supportsAt domain constraints optimum j) : False := by
  obtain ⟨x, hxd, hx, hxo⟩ := hi
  obtain ⟨y, hyd, hy, hyo⟩ := hj
  rcases le_total x y with hxy | hyx
  · have hcy : y ∈ constraints j :=
      (hc j).ordConnected.out (hx j (Ne.symm hij)) (hopt.1.2 j) ⟨hxy, hyo.le⟩
    have hf : y ∈ feasible domain constraints := by
      refine ⟨hyd, ?_⟩
      intro k
      by_cases hkj : k = j
      · exact hkj ▸ hcy
      · exact hy k hkj
    exact (not_le_of_gt hyo) (hopt.2 hf)
  · have hcx : x ∈ constraints i :=
      (hc i).ordConnected.out (hy i hij) (hopt.1.2 i) ⟨hyx, hxo.le⟩
    have hf : x ∈ feasible domain constraints := by
      refine ⟨hxd, ?_⟩
      intro k
      by_cases hki : k = i
      · exact hki ▸ hcx
      · exact hx k hki
    exact (not_le_of_gt hxo) (hopt.2 hf)

theorem actual_general_convex_scalar_support_set_has_at_most_one_element
    {ι : Type*} (domain : Set ℝ) (constraints : ι → Set ℝ) (optimum : ℝ)
    (hc : ∀ i, Convex ℝ (constraints i))
    (hopt : IsLeast (feasible domain constraints) optimum) :
    Set.Subsingleton {i | supportsAt domain constraints optimum i} := by
  intro i hi j hj
  by_contra hij
  exact actual_two_distinct_convex_scalar_constraints_cannot_both_support
    domain constraints optimum hc hopt i j hij hi hj

theorem actual_finite_convex_scalar_support_count_is_at_most_one
    {ι : Type*} [Fintype ι] (domain : Set ℝ) (constraints : ι → Set ℝ)
    (optimum : ℝ) (hc : ∀ i, Convex ℝ (constraints i))
    (hopt : IsLeast (feasible domain constraints) optimum)
    [DecidablePred (supportsAt domain constraints optimum)] :
    (Finset.univ.filter (supportsAt domain constraints optimum)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact actual_general_convex_scalar_support_set_has_at_most_one_element
    domain constraints optimum hc hopt (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

end SafeLearning.CompleteLyapunovScenarioConvexSupport23
