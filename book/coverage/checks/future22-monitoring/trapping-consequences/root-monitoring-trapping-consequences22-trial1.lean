import SafeLearning.CompleteMonitoringTrapping22
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace SafeLearning.CompleteMonitoringTrappingConsequences22
open SafeLearning.CompleteMonitoringMeans22
open SafeLearning.CompleteMonitoringTrapping22
open SafeLearning.CompleteMonitoringGeometry21
local instance : MeasurableSpace (Fin 3) := ⊤
local instance : MeasurableSingletonClass (Fin 3) := ⟨fun _ => MeasurableSet.of_discrete⟩

theorem actual_trapped_path_has_the_exact_finite_visit_counts
    (path : ℕ → Fin 3 × Bool) (h0 : (path 0).1=0) (h1 : (path 1).1≠0)
    (hp : ∀ n : ℕ, (path (n+1)).1=(path 1).1) (N : ℕ) (s : Fin 3) :
    (∑ n ∈ Finset.range (N+1), if (path n).1=s then (1:ℝ) else 0)=
      (if s=0 then (1:ℝ) else 0)+(N:ℝ)*(if s=(path 1).1 then (1:ℝ) else 0) := by
  induction N with
  | zero => simp [h0,eq_comm]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,hp N]
    by_cases hs : s=(path 1).1 <;> simp [hs,eq_comm] <;> push_cast <;> ring

theorem actual_trapped_path_fraction_formula
    (path : ℕ → Fin 3 × Bool) (h0 : (path 0).1=0) (h1 : (path 1).1≠0)
    (hp : ∀ n : ℕ, (path (n+1)).1=(path 1).1) (N : ℕ) (hN : N≠0) (s : Fin 3) :
    pathFraction path N s = (if s=(path 1).1 then (1:ℝ) else 0)+
      ((if s=0 then (1:ℝ) else 0)-(if s=(path 1).1 then (1:ℝ) else 0))/(N:ℝ) := by
  cases N with
  | zero => contradiction
  | succ N =>
    unfold pathFraction
    rw [actual_trapped_path_has_the_exact_finite_visit_counts path h0 h1 hp N s]
    have hn : ((N+1:ℕ):ℝ)≠0 := by positivity
    field_simp
    push_cast
    ring

theorem actual_trapped_path_fraction_limits
    (path : ℕ → Fin 3 × Bool) (h0 : (path 0).1=0) (h1 : (path 1).1≠0)
    (hp : ∀ n : ℕ, (path (n+1)).1=(path 1).1) (s : Fin 3) :
    Tendsto (fun N => pathFraction path N s) atTop (𝓝 (if s=(path 1).1 then (1:ℝ) else 0)) := by
  have h := (tendsto_const_nhds (x:=(if s=(path 1).1 then (1:ℝ) else 0))).add
    (tendsto_const_div_atTop_nhds_zero_nat ((if s=0 then (1:ℝ) else 0)-(if s=(path 1).1 then (1:ℝ) else 0)))
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop (0:ℕ)] with N hN
  exact (actual_trapped_path_fraction_formula path h0 h1 hp N hN s).symm

theorem actual_stationary_no_return_path_fractions_are_extreme_almost_surely
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ᵐ path ∂law q 0 hq0 hq1 (le_refl 0) (by norm_num),
      Tendsto (fun N => pathFraction path N 0) atTop (𝓝 0) ∧
      ((Tendsto (fun N => pathFraction path N 1) atTop (𝓝 1) ∧ Tendsto (fun N => pathFraction path N 2) atTop (𝓝 0)) ∨
       (Tendsto (fun N => pathFraction path N 1) atTop (𝓝 0) ∧ Tendsto (fun N => pathFraction path N 2) atTop (𝓝 1))) := by
  filter_upwards [actual_stationary_no_return_paths_remain_in_the_first_region_almost_surely q hq0 hq1] with path hp
  have h0:=actual_trapped_path_fraction_limits path hp.1 hp.2.1 hp.2.2 0
  have h1:=actual_trapped_path_fraction_limits path hp.1 hp.2.1 hp.2.2 1
  have h2:=actual_trapped_path_fraction_limits path hp.1 hp.2.1 hp.2.2 2
  have hc:=(hp.2.1)
  generalize hx : (path 1).1=s at *
  fin_cases s <;> norm_num at *
  · contradiction
  · exact ⟨h0,Or.inl ⟨h1,h2⟩⟩
  · exact ⟨h0,Or.inr ⟨h1,h2⟩⟩

theorem actual_stationary_no_return_expected_fractions_and_feasibility
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Tendsto (fun N => expectedPathFraction q 0 hq0 hq1 (le_refl 0) (by norm_num) N 0) atTop (𝓝 0) ∧
    Tendsto (fun N => expectedPathFraction q 0 hq0 hq1 (le_refl 0) (by norm_num) N 1) atTop (𝓝 q) ∧
    Tendsto (fun N => expectedPathFraction q 0 hq0 hq1 (le_refl 0) (by norm_num) N 2) atTop (𝓝 (1-q)) ∧
    ((1/3 ≤ q ∧ 1/3 ≤ 1-q) ↔ (1/3 ≤ q ∧ q ≤ 2/3)) := by
  have h:=actual_expected_path_fraction_limits q 0 hq0 hq1 (le_refl 0) (by norm_num)
  simpa using ⟨h.1,h.2.1,h.2.2,actual_stationary_no_return_expected_feasibility_interval q⟩

end SafeLearning.CompleteMonitoringTrappingConsequences22
