import SafeLearning.CompleteMonitoringTrappingConsequences22
import SafeLearning.CompleteMonitoringGeometry21
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
namespace SafeLearning.CompleteMonitoringEpochBias22
open SafeLearning.CompleteMonitoringMeans22
open SafeLearning.CompleteMonitoringGeometry21

theorem actual_no_return_initial_epoch_expected_zero_fraction (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (N : ℕ) (hN : N≠0) :
    expectedPathFraction q 0 hq0 hq1 (le_refl 0) (by norm_num) N 0=1/(N:ℝ) := by
  rw [actual_expected_path_fraction_is_the_marginal_average,actual_average_zero_state_formula q 0 hq0 hq1 (le_refl 0) (by norm_num) N hN]
  have hs : (∑ n ∈ Finset.range N,(0:ℝ)^n)=1 := by
    rw [geom_sum_eq (by norm_num : (0:ℝ)≠1)]
    norm_num [zero_pow hN]
  simpa using congrArg (fun x : ℝ => x/(N:ℝ)) hs

theorem actual_no_return_initial_epoch_expected_region_fraction (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (N : ℕ) (hN : N≠0) :
    expectedPathFraction q 0 hq0 hq1 (le_refl 0) (by norm_num) N 1=q*(1-1/(N:ℝ)) := by
  have h0:=actual_no_return_initial_epoch_expected_zero_fraction q hq0 hq1 N hN
  rw [actual_expected_path_fraction_is_the_marginal_average] at h0 ⊢
  rw [(actual_other_state_average_formulas q 0 hq0 hq1 (le_refl 0) (by norm_num) N hN).1,h0]

theorem actual_exact_lagrangian_maximizer_can_have_biased_finite_initial_epoch
    (N : ℕ) (hN : N≠0) :
    Tendsto (fun T => expectedPathFraction 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) T 1) atTop (𝓝 1) ∧
    expectedPathFraction 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) N 1<1 ∧
    IsMaximizer 2 0 vertex1 := by
  have hl:=(actual_expected_path_fraction_limits 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.1
  have hn : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hp : 0<(1:ℝ)/(N:ℝ) := div_pos (by norm_num) hn
  refine ⟨by simpa using hl,?_,?_⟩
  · rw [actual_no_return_initial_epoch_expected_region_fraction 1 (by norm_num) (by norm_num) N hN]
    linarith
  · have hv:=actual_four_vertices_and_primal_optimum_in_the_polytope
    refine ⟨hv.1,?_⟩
    intro v hv
    exact (actual_larger_first_price_vertex_one_bound 2 0 v hv (by norm_num) (by norm_num)).1

end SafeLearning.CompleteMonitoringEpochBias22
