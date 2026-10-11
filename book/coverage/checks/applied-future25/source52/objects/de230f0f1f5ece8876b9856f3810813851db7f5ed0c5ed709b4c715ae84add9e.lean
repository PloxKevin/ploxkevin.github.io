import SafeLearning.CompleteFoundationsNonnegativeSeriesModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteFoundationsDissipationSeries
open CompleteFoundationsNonnegativeSeriesModels

theorem actual_all_horizon_square_dissipation_implies_genuine_state_convergence
    {E : Type*} [NormedAddCommGroup E] (state : ℕ→E) (target : E)
    (epsilon initialValue : ℝ) (hepsilon : 0<epsilon)
    (hbound : ∀N:ℕ,epsilon*(∑n∈Finset.range N,‖state n-target‖^2) ≤ initialValue) :
    Summable (fun n=>‖state n-target‖^2) ∧ Tendsto state atTop (𝓝 target) := by
  have hs : Summable (fun n=>‖state n-target‖^2) :=
    summable_of_sum_range_le (fun _=>sq_nonneg _) (fun N=>
      (le_div_iff₀ hepsilon).mpr (by simpa only [mul_comm] using hbound N))
  have hzero : Tendsto (fun n=>‖state n-target‖^2) atTop (𝓝 0) :=
    actual_convergent_natural_partial_sums_force_the_actual_terms_to_zero _ _
      hs.hasSum.tendsto_sum_nat
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hzero
  have hnorm : Tendsto (fun n=>‖state n-target‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),
      Real.sqrt_zero] using hsqrt
  exact ⟨hs,tendsto_iff_norm_sub_tendsto_zero.mpr hnorm⟩

theorem actual_telescoping_dissipation_derives_every_partial_sum_bound
    {E : Type*} [NormedAddCommGroup E] (state : ℕ→E) (target : E)
    (value : ℕ→ℝ) (epsilon : ℝ)
    (hnonnegative : ∀n,0≤value n)
    (hstep : ∀n,value (n+1)-value n≤ -epsilon*‖state n-target‖^2) :
    ∀N:ℕ,epsilon*(∑n∈Finset.range N,‖state n-target‖^2)≤value 0 := by
  have hb : ∀N:ℕ,value N+epsilon*(∑n∈Finset.range N,‖state n-target‖^2)≤value 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ,mul_add]
      linarith [hstep N]
  intro N
  linarith [hb N,hnonnegative N]

theorem actual_nonnegative_strict_square_dissipation_implies_state_convergence
    {E : Type*} [NormedAddCommGroup E] (state : ℕ→E) (target : E)
    (value : ℕ→ℝ) (epsilon : ℝ) (hepsilon : 0<epsilon)
    (hnonnegative : ∀n,0≤value n)
    (hstep : ∀n,value (n+1)-value n≤ -epsilon*‖state n-target‖^2) :
    Tendsto state atTop (𝓝 target) := by
  exact (actual_all_horizon_square_dissipation_implies_genuine_state_convergence
    state target epsilon (value 0) hepsilon
    (actual_telescoping_dissipation_derives_every_partial_sum_bound
      state target value epsilon hnonnegative hstep)).2

end SafeLearning.CompleteFoundationsDissipationSeries
