import SafeLearning.CompleteModulesSafeOptEightPointReachability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptEightPointAlgorithms
open CompleteModulesSafeOptEightPointReachability

theorem actual_every_algorithm_using_valid_source_cones_stays_in_the_five_point_closure
    (safeSets : ℕ → Set (Fin 8)) (lower : ℕ → Fin 8 → ℝ)
    (hseed : safeSets 0=({2}:Set (Fin 8)))
    (hvalid : ∀ n x, lower n x ≤ actualValue x)
    (hstep : ∀ n x, x ∈ safeSets (n+1) → x ∈ safeSets n ∨
      ∃ a ∈ safeSets n, 0 ≤ lower (n+1) a-actualDistance a x) :
    (∀ n, safeSets n ⊆ actualFinal) ∧ (∀ n, (7:Fin 8) ∉ safeSets n) := by
  have hi : ∀ n, safeSets n ⊆ actualFinal := by
    intro n
    induction n with
    | zero => rw [hseed];intro x hx;have he : x=2 := hx;rw [he];simp [actualFinal]
    | succ n ih =>
      intro x hx
      rcases hstep n x hx with hx | ⟨a,ha,hc⟩
      · exact ih hx
      · have hr : x ∈ actualReach 0 actualFinal := by
          refine Or.inr ⟨a,ih ha,?_⟩
          have hf := hvalid (n+1) a
          linarith
        rwa [actual_source_zero_slack_reaches_the_same_true_fixed_point.2] at hr
  exact ⟨hi,fun n hn => (by simp [actualFinal] : (7:Fin 8) ∉ actualFinal) (hi n hn)⟩

theorem actual_any_admissible_query_of_a_valid_cone_algorithm_cannot_be_the_global_maximum
    (safeSets : ℕ → Set (Fin 8)) (lower : ℕ → Fin 8 → ℝ) (query : ℕ → Fin 8)
    (hseed : safeSets 0=({2}:Set (Fin 8)))
    (hvalid : ∀ n x, lower n x ≤ actualValue x)
    (hstep : ∀ n x, x ∈ safeSets (n+1) → x ∈ safeSets n ∨
      ∃ a ∈ safeSets n, 0 ≤ lower (n+1) a-actualDistance a x)
    (hquery : ∀ n, query n ∈ safeSets n) :
    ∀ n, query n≠7 := by
  have hs := actual_every_algorithm_using_valid_source_cones_stays_in_the_five_point_closure safeSets lower hseed hvalid hstep
  intro n he
  have hq := hquery n
  rw [he] at hq
  exact hs.2 n hq

theorem actual_any_reachable_recommendation_meeting_the_stated_point_two_optimality_guarantee_is_two
    (report : Fin 8) (hr : report ∈ actualFinal) (hopt : 2-(1/5:ℝ) ≤ actualValue report) :
    report=2 ∧ actualValue report=2 := by
  have hi : report=2 := by
    fin_cases report
    all_goals norm_num [actualFinal] at hr
    all_goals norm_num [actualValue] at hopt
    all_goals rfl
  exact ⟨hi,by rw [hi];norm_num [actualValue]⟩

theorem actual_zero_threshold_gp_cone_free_certificate_has_the_literal_mean_sigma_condition
    (mu beta sigma : ℝ) : (0:ℝ) ≤ mu-beta*sigma ↔ beta*sigma ≤ mu := by
  constructor <;> intro h <;> linarith

theorem actual_source_point_five_exact_mean_requires_the_printed_variance_level
    (beta sigma : ℝ) (hb : 0 < beta) (hs : 0 ≤ sigma) :
    (0:ℝ) ≤ actualValue 5-beta*sigma ↔ sigma^2 ≤ ((1/5:ℝ)/beta)^2 := by
  rw [show actualValue 5=(1/5:ℝ) by norm_num [actualValue]]
  have hp : 0 < (1/5:ℝ)/beta := by positivity
  have hc : (0:ℝ) ≤ (1/5:ℝ)-beta*sigma ↔ sigma ≤ (1/5:ℝ)/beta := by
    rw [le_div_iff₀ hb]
    constructor <;> intro h <;> nlinarith
  rw [hc]
  constructor
  · intro h
    exact pow_le_pow_left₀ hs h 2
  · intro h
    nlinarith

end SafeLearning.CompleteModulesSafeOptEightPointAlgorithms
