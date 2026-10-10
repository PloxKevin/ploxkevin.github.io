import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SafeLearning.CompleteFoundationsRatesCosts
open Set Filter Asymptotics
open scoped Topology BigOperators

def averageBound (t : ℝ) : ℝ := 4*Real.log t/Real.sqrt t

theorem actual_log_cube_vs_sqrt :
    IsLittleO atTop (fun t : ℝ=>(Real.log t)^3) Real.sqrt := by
  have h := isLittleO_log_rpow_rpow_atTop (3:ℝ) (by norm_num : (0:ℝ)<1/2)
  have hf : (fun t : ℝ=>Real.log t^(3:ℝ))=(fun t=>(Real.log t)^3) := by
    funext t;exact Real.rpow_natCast _ 3
  have hg : (fun t : ℝ=>t^(1/2:ℝ))=Real.sqrt := by
    funext t;exact (Real.sqrt_eq_rpow t).symm
  rw [hf,hg] at h
  exact h

theorem actual_sqrt_vs_two_thirds_ratio :
    Tendsto (fun t : ℝ=>Real.sqrt t/Real.rpow t (2/3)) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [Real.rpow_eq_pow,Real.sqrt_eq_rpow,←Real.rpow_sub ht]
  norm_num

theorem actual_two_thirds_vs_t_over_log_ratio :
    Tendsto (fun t : ℝ=>Real.rpow t (2/3)/(t/Real.log t)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/3)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  have hp : 0<t := by linarith
  have he : Real.rpow t (1/3)*Real.rpow t (2/3)=t := by
    rw [Real.rpow_eq_pow,Real.rpow_eq_pow,←Real.rpow_add hp];norm_num
  have hne : Real.rpow t (1/3)≠0 := (Real.rpow_pos_of_pos hp _).ne'
  have hlog : Real.log t≠0 := (Real.log_pos ht).ne'
  rw [Real.rpow_eq_pow,Real.rpow_eq_pow] at he
  rw [Real.rpow_eq_pow] at hne
  simp only [Real.rpow_eq_pow]
  field_simp
  nlinarith [he]

theorem actual_average_bound_limit : Tendsto averageBound atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have he : averageBound=(fun t : ℝ=>4*(Real.log t/t^(1/2:ℝ))) := by
    funext t;rw [averageBound,Real.sqrt_eq_rpow];ring
  rw [he]
  simpa using h.const_mul 4

theorem actual_average_bound_derivative (t : ℝ) (ht : 0<t) :
    HasDerivAt averageBound ((4-2*Real.log t)/(t*Real.sqrt t)) t := by
  have hs : Real.sqrt t≠0 := (Real.sqrt_pos.mpr ht).ne'
  have hq := Real.sq_sqrt ht.le
  convert (((hasDerivAt_id t).log ht.ne').const_mul 4).div
    (Real.hasDerivAt_sqrt ht.ne') hs using 1
  · rfl
  · dsimp only [id_eq]
    field_simp
    nlinarith [congrArg (fun x : ℝ=>x*Real.log t) hq]

theorem actual_average_bound_decreasing_after_exp_two :
    AntitoneOn averageBound (Ici (Real.exp 2)) := by
  have hp (t : ℝ) (ht : t∈Ici (Real.exp 2)) : 0<t :=
    lt_of_lt_of_le (Real.exp_pos _) ht
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (f' := fun t=>(4-2*Real.log t)/(t*Real.sqrt t))
  · intro t ht;exact (actual_average_bound_derivative t (hp t ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (actual_average_bound_derivative t (hp t (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    have hmem := interior_subset ht
    have ht' := hp t hmem
    have hl : 2≤Real.log t := by
      simpa using Real.log_le_log (Real.exp_pos 2) hmem
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem actual_log_quarter_million :
    Real.log (250000:ℝ)=4*Real.log 2+6*Real.log 5 := by
  rw [show (250000:ℝ)=2^4*5^6 by norm_num,Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow,Real.log_pow]
  norm_num

theorem actual_threshold_neighbor_log_bounds (n : ℕ)
    (hn : n=246638 ∨ n=246639) :
    12415676/1000000<Real.log (n:ℝ) ∧ Real.log (n:ℝ)<12415682/1000000 := by
  have hbase := actual_log_quarter_million
  have hnp : (n:ℝ)≠0 := by rcases hn with rfl|rfl <;> norm_num
  have he : Real.log (n:ℝ)=Real.log (250000:ℝ)+Real.log ((n:ℝ)/250000) := by
    rw [Real.log_div hnp (by norm_num)];ring
  rw [he,hbase]
  have h := Real.abs_log_sub_add_sum_range_le
    (x := (1-(n:ℝ)/250000)) (by rcases hn with rfl|rfl <;> norm_num) 4
  rcases hn with rfl|rfl
  all_goals
    norm_num [Finset.sum_range_succ] at h
    have hh := abs_le.mp h
    constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9,
      Real.log_five_gt_d9,Real.log_five_lt_d9]

theorem actual_threshold_neighbors :
    (1/10:ℝ)<averageBound 246638 ∧ averageBound 246639≤1/10 := by
  have hl := (actual_threshold_neighbor_log_bounds 246638 (Or.inl rfl)).1
  have hu := (actual_threshold_neighbor_log_bounds 246639 (Or.inr rfl)).2
  have hr₀ : Real.sqrt (246638:ℝ)<40*(12415676/1000000) := by
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).mpr
    norm_num
  have hr₁ : 40*(12415682/1000000)≤Real.sqrt (246639:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  constructor
  · rw [averageBound,lt_div_iff₀ (by positivity)]
    linarith
  · rw [averageBound,div_le_iff₀ (by positivity)]
    linarith

theorem actual_first_permanent_integer_budget (N : ℕ) :
    (∀ n : ℕ,N≤n→averageBound n≤1/10) ↔ 246639≤N := by
  have he : Real.exp 2≤(246639:ℝ) := by
    have hl := (actual_threshold_neighbor_log_bounds 246639 (Or.inr rfl)).1
    have h : (2:ℝ)≤Real.log (246639:ℝ) := by linarith
    exact (Real.exp_le_exp.mpr h).trans_eq (Real.exp_log (by norm_num))
  constructor
  · intro h
    by_contra hn
    exact (not_le.mpr actual_threshold_neighbors.1) (h 246638 (by omega))
  · intro hn n hN
    have hni : (246639:ℝ)≤n := by exact_mod_cast (hn.trans hN)
    exact (actual_average_bound_decreasing_after_exp_two he (he.trans hni) hni).trans
      actual_threshold_neighbors.2

theorem actual_log_fixed_budgets :
    Real.log (10000:ℝ)=4*(Real.log 2+Real.log 5) ∧
    Real.log (100000:ℝ)=5*(Real.log 2+Real.log 5) := by
  constructor
  · rw [show (10000:ℝ)=(2*5)^4 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  · rw [show (100000:ℝ)=(2*5)^5 by norm_num,Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num

theorem actual_average_fixed_budget_roundings :
    |averageBound 10000-368/1000|<1/2000 ∧
    |averageBound 100000-146/1000|<1/2000 := by
  have hs₀ : Real.sqrt (10000:ℝ)=100 := by norm_num
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤100000)
  have hn := Real.sqrt_nonneg (100000:ℝ)
  have hs₁ : (3162/10:ℝ)<Real.sqrt 100000 ∧ Real.sqrt 100000<3163/10 := by
    constructor <;> nlinarith
  constructor
  · rw [abs_lt,averageBound,hs₀,actual_log_fixed_budgets.1]
    constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9,
      Real.log_five_gt_d9,Real.log_five_lt_d9]
  · rw [abs_lt,averageBound,actual_log_fixed_budgets.2]
    have hp : (0:ℝ)<Real.sqrt 100000 := by positivity
    constructor
    · rw [lt_sub_iff_add_lt,lt_div_iff₀ hp]
      linarith [Real.log_two_gt_d9,Real.log_five_gt_d9,hs₁.2]
    · rw [sub_lt_iff_lt_add,div_lt_iff₀ hp]
      linarith [Real.log_two_lt_d9,Real.log_five_lt_d9,hs₁.1]

def cubicTime (coefficient size : ℝ) : ℝ := coefficient*size^3

theorem actual_cubic_runtime_scaling (coefficient : ℝ)
    (h : cubicTime coefficient 1000=0.05) : cubicTime coefficient 4000=3.2 := by
  unfold cubicTime at *
  norm_num at *
  linarith

theorem actual_cubic_cost_estimate :
    (0.05:ℝ)*(4000/1000)^3=3.2 ∧ (4000/1000:ℝ)^3=64 := by norm_num

theorem actual_grid_counts :
    (20:ℕ)^6=64000000 ∧ (20:ℕ)^10=10240000000000 ∧
    |((20:ℕ)^10:ℝ)-10000000000000|<500000000000 := by norm_num

theorem actual_grid_type_cardinalities :
    Fintype.card (Fin 6→Fin 20)=64000000 ∧
    Fintype.card (Fin 10→Fin 20)=10240000000000 := by norm_num

end SafeLearning.CompleteFoundationsRatesCosts
