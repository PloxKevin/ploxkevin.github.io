import SafeLearning.CompleteMonitoringAchievable22
import SafeLearning.CompleteMonitoringDualValue22
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter MeasureTheory
namespace SafeLearning.CompleteMonitoringPolicyValues22
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteFiniteMarkovPathCorrespondence
open SafeLearning.CompleteMonitoringGeometry21
open SafeLearning.CompleteMonitoringMeans22
open SafeLearning.CompleteMonitoringAchievable22
open SafeLearning.CompleteMonitoringDualValue22

def actualPolicyValues : Set Fractions := {v | ∃ π : HistoryPolicy (Fin 3) Bool,
  Tendsto (fun N => expectedHistoryFraction π N 0) atTop (𝓝 v.v0) ∧
  Tendsto (fun N => expectedHistoryFraction π N 1) atTop (𝓝 v.v1) ∧
  Tendsto (fun N => expectedHistoryFraction π N 2) atTop (𝓝 v.v2)}

theorem actual_expected_policy_values_are_exactly_the_source_polytope (v : Fractions) :
    v ∈ actualPolicyValues ↔ AchievablePolytope v := by
  constructor
  · rintro ⟨π,h0,h1,h2⟩
    exact actual_every_history_policy_with_expected_fraction_limits_is_in_the_source_polytope π v h0 h1 h2
  · intro hv
    obtain ⟨q,b,hq0,hq1,hb0,hb1,h0,h1,h2⟩:=actual_every_source_polytope_fraction_has_a_markov_average_realization v hv
    have hm (N : ℕ) (s : Fin 3) : expectedHistoryFraction (markovHistoryPolicy (policy q b hq0 hq1 hb0 hb1)) N s = averageState q b hq0 hq1 hb0 hb1 N s := by
      change expectedPathFraction q b hq0 hq1 hb0 hb1 N s = _
      exact actual_expected_path_fraction_is_the_marginal_average q b hq0 hq1 hb0 hb1 N s
    refine ⟨markovHistoryPolicy (policy q b hq0 hq1 hb0 hb1),?_,?_,?_⟩ <;> simpa only [hm] using (by assumption)

def actualPrimalValue : ℝ := sSup {x : ℝ | ∃ v ∈ actualPolicyValues, 1/3 ≤ v.v1 ∧ 1/3 ≤ v.v2 ∧ x=v.v0}
def actualPolicyDual (l1 l2 : ℝ) : ℝ := sSup {x : ℝ | ∃ v ∈ actualPolicyValues, x=lagrangian l1 l2 v}

theorem actual_policy_dual_is_the_computed_finite_dual (l1 l2 : ℝ) :
    actualPolicyDual l1 l2=dualValue l1 l2 := by
  unfold actualPolicyDual dualValue values
  congr 1
  ext x
  simp only [Set.mem_setOf_eq,actual_expected_policy_values_are_exactly_the_source_polytope]

theorem actual_constrained_policy_optimum_is_attained_and_equal_to_one_third :
    actualPrimalValue=1/3 ∧ optimum ∈ actualPolicyValues ∧
    ∀ v ∈ actualPolicyValues, 1/3 ≤ v.v1 → 1/3 ≤ v.v2 → v.v0 ≤ 1/3 := by
  have hop:=actual_four_vertices_and_primal_optimum_in_the_polytope
  have hm : optimum ∈ actualPolicyValues := (actual_expected_policy_values_are_exactly_the_source_polytope optimum).mpr hop.2.2.2.2.1
  have bound (v : Fractions) (hv : v∈actualPolicyValues) (h1 : 1/3≤v.v1) (h2 : 1/3≤v.v2) : v.v0≤1/3 := by
    have h:=(actual_expected_policy_values_are_exactly_the_source_polytope v).mp hv
    linarith [h.2.2.2.1]
  have mem : (1/3:ℝ) ∈ {x : ℝ | ∃ v ∈ actualPolicyValues, 1/3 ≤ v.v1 ∧ 1/3 ≤ v.v2 ∧ x=v.v0} := by
    exact ⟨optimum,hm,by norm_num [optimum],by norm_num [optimum],by norm_num [optimum]⟩
  have hb : BddAbove {x : ℝ | ∃ v ∈ actualPolicyValues, 1/3 ≤ v.v1 ∧ 1/3 ≤ v.v2 ∧ x=v.v0} := by
    refine ⟨1/3,?_⟩
    rintro x ⟨v,hv,h1,h2,rfl⟩
    exact bound v hv h1 h2
  refine ⟨le_antisymm ?_ (le_csSup hb mem),hm,bound⟩
  apply csSup_le ⟨1/3,mem⟩
  rintro x ⟨v,hv,h1,h2,rfl⟩
  exact bound v hv h1 h2

theorem actual_policy_problem_has_zero_duality_gap_and_unique_optimal_prices :
    actualPrimalValue=1/3 ∧ actualPolicyDual 1 1=1/3 ∧
    ∀ l1 l2, actualPolicyDual l1 l2=1/3 ↔ l1=1 ∧ l2=1 := by
  refine ⟨actual_constrained_policy_optimum_is_attained_and_equal_to_one_third.1,?_,?_⟩
  · rw [actual_policy_dual_is_the_computed_finite_dual]
    exact actual_unit_dual_prices_have_value_one_third
  · intro l1 l2
    rw [actual_policy_dual_is_the_computed_finite_dual]
    exact actual_unit_prices_are_the_unique_dual_optimum l1 l2

theorem actual_every_policy_with_existing_values_maximizes_at_unit_prices
    (v : Fractions) (hv : v∈actualPolicyValues) :
    lagrangian 1 1 v=actualPolicyDual 1 1 := by
  rw [actual_policy_dual_is_the_computed_finite_dual,actual_unit_dual_prices_have_value_one_third]
  exact actual_lagrangian_is_constant_at_the_dual_prices v ((actual_expected_policy_values_are_exactly_the_source_polytope v).mp hv)

end SafeLearning.CompleteMonitoringPolicyValues22
