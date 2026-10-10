import SafeLearning.CompleteFoundationsBanachModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsBanachOscillation

/-- A factor-one map genuinely fails convergence from every nonzero start. -/
theorem actual_negation_iterates_do_not_converge_from_any_nonzero_start
    (x : ℝ) (hx : x ≠ 0) :
    ¬ ∃ limit : ℝ, Tendsto (fun n : ℕ => (fun y : ℝ => -y)^[n] x) atTop (𝓝 limit) := by
  rintro ⟨limit, hlimit⟩
  have heven : Tendsto (fun n : ℕ => 2*n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hodd : Tendsto (fun n : ℕ => 2*n+1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hs := CompleteFoundationsBanachModels.actual_factor_one_negation_and_two_cycle x
  have he : Tendsto (fun _n : ℕ => x) atTop (𝓝 limit) := by
    simpa only [Function.comp_def, hs.2.2.1] using hlimit.comp heven
  have ho : Tendsto (fun _n : ℕ => -x) atTop (𝓝 limit) := by
    simpa only [Function.comp_def, hs.2.2.2] using hlimit.comp hodd
  have hel : x = limit := tendsto_nhds_unique tendsto_const_nhds he
  have hol : -x = limit := tendsto_nhds_unique tendsto_const_nhds ho
  apply hx
  linarith

theorem actual_negation_zero_start_is_a_fixed_and_convergent_exception :
    (fun y : ℝ => -y) 0=0 ∧
      (∀ n : ℕ, (fun y : ℝ => -y)^[n] 0=0) ∧
      Tendsto (fun n : ℕ => (fun y : ℝ => -y)^[n] 0) atTop (𝓝 0) := by
  have hi : ∀ n : ℕ, (fun y : ℝ => -y)^[n] 0=0 := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih]; simp
  exact ⟨by simp, hi, by simpa only [hi] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))⟩

theorem actual_source_factor_one_negation_has_an_oscillating_initial_point :
    LipschitzWith 1 (fun y : ℝ => -y) ∧
      (∀ n : ℕ, (fun y : ℝ => -y)^[2*n] 1=1) ∧
      (∀ n : ℕ, (fun y : ℝ => -y)^[2*n+1] 1= -1) ∧
      ¬ ∃ limit : ℝ, Tendsto (fun n : ℕ => (fun y : ℝ => -y)^[n] 1) atTop (𝓝 limit) := by
  have h := CompleteFoundationsBanachModels.actual_factor_one_negation_and_two_cycle 1
  exact ⟨h.1, h.2.2.1, h.2.2.2,
    actual_negation_iterates_do_not_converge_from_any_nonzero_start 1 (by norm_num)⟩

end SafeLearning.CompleteFoundationsBanachOscillation
