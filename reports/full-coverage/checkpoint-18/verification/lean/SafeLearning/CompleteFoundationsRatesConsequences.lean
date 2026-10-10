import SafeLearning.CompleteFoundationsRatesCosts
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsRatesConsequences
open Set Filter Asymptotics
open scoped Topology
open SafeLearning.CompleteFoundationsRatesCosts

def sourceRate (n : ℕ) : ℝ := 4*Real.sqrt n*Real.log n

theorem actual_cumulative_bound_implies_average_bound (R : ℕ→ℝ)
    (hR : ∀ n,1≤n→0≤R n ∧ R n≤ sourceRate n) (n : ℕ) (hn : 1≤n) :
    0≤R n/n ∧ R n/n≤averageBound n := by
  have hp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hs := Real.mul_self_sqrt hp.le
  have hsn : Real.sqrt (n:ℝ)≠0 := by positivity
  have he : sourceRate n/n=averageBound n := by
    unfold sourceRate averageBound
    field_simp
    nlinarith [congrArg (fun z : ℝ=>z*Real.log n) hs]
  exact ⟨div_nonneg (hR n hn).1 hp.le,
    (div_le_div_of_nonneg_right (hR n hn).2 hp.le).trans_eq he⟩

theorem actual_nonnegative_source_average_regret_tends_to_zero (R : ℕ→ℝ)
    (hR : ∀ n,1≤n→0≤R n ∧ R n≤ sourceRate n) :
    Tendsto (fun n=>R n/n) atTop (𝓝 0) := by
  have hb : ∀ᶠ n in atTop,0≤R n/n ∧ R n/n≤averageBound n := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    exact actual_cumulative_bound_implies_average_bound R hR n hn
  exact squeeze_zero' (hb.mono fun _ h=>h.1) (hb.mono fun _ h=>h.2)
    (actual_average_bound_limit.comp tendsto_natCast_atTop_atTop)

theorem actual_source_regret_is_little_o (R : ℕ→ℝ) (h0 : R 0=0)
    (hR : ∀ n,1≤n→0≤R n ∧ R n≤ sourceRate n) :
    IsLittleO atTop R (fun n=>(n:ℝ)) := by
  apply isLittleO_of_tendsto
  · intro n hn
    have : n=0 := by exact_mod_cast hn
    simpa [this] using h0
  · exact actual_nonnegative_source_average_regret_tends_to_zero R hR

theorem actual_fixed_budget_decimals_are_strict_approximations :
    (368/1000:ℝ)<averageBound 10000 ∧ averageBound 100000<146/1000 := by
  constructor
  · have hs : Real.sqrt (10000:ℝ)=100 := by norm_num
    rw [averageBound,hs,actual_log_fixed_budgets.1]
    linarith [Real.log_two_gt_d9,Real.log_five_gt_d9]
  · have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤100000)
    have hn := Real.sqrt_nonneg (100000:ℝ)
    have hsl : (3162/10:ℝ)<Real.sqrt 100000 := by nlinarith
    rw [averageBound,actual_log_fixed_budgets.2,div_lt_iff₀ (by positivity)]
    linarith [Real.log_two_lt_d9,Real.log_five_lt_d9]

theorem actual_both_printed_decimals_are_not_equal :
    averageBound 10000≠368/1000 ∧ averageBound 100000≠146/1000 :=
  ⟨ne_of_gt actual_fixed_budget_decimals_are_strict_approximations.1,
   ne_of_lt actual_fixed_budget_decimals_are_strict_approximations.2⟩

def negativeExample (n : ℕ) : ℝ := -(n:ℝ)

theorem actual_one_sided_source_bound_without_nonnegativity (n : ℕ) (hn : 1≤n) :
    negativeExample n≤ sourceRate n ∧ negativeExample n/n= -1 := by
  have hp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hl : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  constructor
  · have hs : 0≤ sourceRate n := by unfold sourceRate;positivity
    unfold negativeExample
    linarith
  · simp [negativeExample,hp.ne']

theorem actual_one_sided_bound_alone_does_not_imply_zero_average :
    ¬Tendsto (fun n=>negativeExample n/n) atTop (𝓝 0) := by
  intro h
  have hm : Tendsto (fun n=>negativeExample n/n) atTop (𝓝 (-1:ℝ)) := by
    apply (tendsto_const_nhds (x := (-1:ℝ))).congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    exact (actual_one_sided_source_bound_without_nonnegativity n hn).2.symm
  have he := tendsto_nhds_unique h hm
  norm_num at he
end SafeLearning.CompleteFoundationsRatesConsequences
