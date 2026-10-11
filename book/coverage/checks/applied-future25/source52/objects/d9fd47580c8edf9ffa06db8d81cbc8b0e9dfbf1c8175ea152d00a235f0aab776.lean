import SafeLearning.CompleteCompactLyapunov

set_option autoImplicit false
noncomputable section

namespace SafeLearning.CompleteFoundationsCompactLyapunovPrintedRoute24

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem actual_nonempty_compact_positive_annulus_has_an_attained_uniform_negative_decrement
    (F : E → E) (V : E → ℝ) (c a : ℝ)
    (hF : Continuous F) (hV : Continuous V) (hV0 : V 0 = 0) (ha : 0 < a)
    (hcompact : IsCompact {y : E | V y ≤ c})
    (hne : ({y : E | a ≤ V y ∧ V y ≤ c} : Set E).Nonempty)
    (hdec : ∀ y, V y ≤ c → y ≠ 0 → V (F y) < V y) :
    ∃ z ∈ {y : E | a ≤ V y ∧ V y ≤ c}, ∃ η : ℝ, 0 < η ∧
      V (F z) - V z = -η ∧
      ∀ y ∈ {y : E | a ≤ V y ∧ V y ≤ c}, V (F y) - V y ≤ -η := by
  let K : Set E := {y | a ≤ V y ∧ V y ≤ c}
  have hK : IsCompact K := by
    simpa [K, Set.inter_def, and_comm] using
      hcompact.inter_right (isClosed_le continuous_const hV)
  have hΔ : Continuous (fun y => V (F y) - V y) := (hV.comp hF).sub hV
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne hΔ.continuousOn
  have hz0 : z ≠ 0 := by
    intro heq
    have := hz.1
    simp only [heq, hV0] at this
    linarith
  have hneg : V (F z) - V z < 0 := sub_neg.mpr (hdec z hz.2 hz0)
  refine ⟨z, hz, -(V (F z) - V z), neg_pos.mpr hneg, ?_, ?_⟩
  · ring
  · intro y hy
    simpa using hmax hy

theorem actual_uniform_negative_decrement_gives_the_printed_linear_in_time_bound
    (F : E → E) (V : E → ℝ) (x : ℕ → E) (η : ℝ)
    (hstep : ∀ n, x (n + 1) = F (x n))
    (hη : ∀ n, V (F (x n)) - V (x n) ≤ -η) :
    ∀ n, V (x n) ≤ V (x 0) - (n : ℝ) * η := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hd := hη n
    rw [hstep]
    push_cast
    nlinarith

theorem actual_positive_uniform_decrement_contradicts_nonnegative_trajectory_values
    (F : E → E) (V : E → ℝ) (x : ℕ → E) (η : ℝ) (hηpos : 0 < η)
    (hstep : ∀ n, x (n + 1) = F (x n))
    (hnonneg : ∀ n, 0 ≤ V (x n))
    (hη : ∀ n, V (F (x n)) - V (x n) ≤ -η) : False := by
  obtain ⟨n, hn⟩ := exists_nat_gt (V (x 0) / η)
  have hnη : V (x 0) < (n : ℝ) * η := (div_lt_iff₀ hηpos).mp hn
  have hb := actual_uniform_negative_decrement_gives_the_printed_linear_in_time_bound
    F V x η hstep hη n
  have hp := hnonneg n
  linarith

theorem actual_compact_annulus_away_from_zero_has_a_positive_attained_lyapunov_minimum
    (V : E → ℝ) (c ε : ℝ) (hε : 0 < ε) (hV : Continuous V)
    (hpos : ∀ y, y ≠ 0 → 0 < V y)
    (hcompact : IsCompact {y : E | V y ≤ c})
    (hne : ({y : E | V y ≤ c ∧ ε ≤ ‖y‖} : Set E).Nonempty) :
    ∃ z ∈ {y : E | V y ≤ c ∧ ε ≤ ‖y‖},
      0 < V z ∧ IsLeast (V '' {y : E | V y ≤ c ∧ ε ≤ ‖y‖}) (V z) := by
  have hK : IsCompact {y : E | V y ≤ c ∧ ε ≤ ‖y‖} := by
    simpa [Set.inter_def] using hcompact.inter_right (isClosed_le continuous_const continuous_norm)
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hV.continuousOn
  have hz0 : z ≠ 0 := by
    intro heq
    have hn := hz.2
    simp only [heq, norm_zero] at hn
    linarith
  refine ⟨z, hz, hpos z hz0, ⟨⟨z, hz, rfl⟩, ?_⟩⟩
  rintro v ⟨y, hy, rfl⟩
  exact hmin hy

theorem actual_value_below_the_annulus_minimum_forces_small_state_norm
    (V : E → ℝ) (c ε m : ℝ) (y : E)
    (hmin : IsLeast (V '' {z : E | V z ≤ c ∧ ε ≤ ‖z‖}) m)
    (hy : V y ≤ c) (hvalue : V y < m) : ‖y‖ < ε := by
  by_contra hn
  have hm : m ≤ V y := hmin.2 ⟨y, ⟨hy, le_of_not_gt hn⟩, rfl⟩
  linarith

theorem actual_printed_uniform_decrement_route_proves_lyapunov_value_limit_zero
    (F : E → E) (V : E → ℝ) (x : ℕ → E) (c : ℝ)
    (hF : Continuous F) (hV : Continuous V) (hV0 : V 0 = 0)
    (hcompact : IsCompact {y : E | V y ≤ c}) (hnonneg : ∀ y, 0 ≤ V y)
    (hF0 : F 0 = 0) (hstep : ∀ n, x (n + 1) = F (x n)) (hi : V (x 0) ≤ c)
    (hdec : ∀ y, V y ≤ c → y ≠ 0 → V (F y) < V y) :
    Tendsto (fun n => V (x n)) atTop (𝓝 0) := by
  have hinv := SafeLearning.CompleteCompactLyapunov.sublevel_forward_invariance
    F V x c hF0 hstep hi hdec
  have hanti := SafeLearning.CompleteCompactLyapunov.trajectory_values_antitone
    F V x c hF0 hstep hi hdec
  have hbdd : BddBelow (range (fun n => V (x n))) := by
    refine ⟨0, ?_⟩
    rintro v ⟨n, rfl⟩
    exact hnonneg (x n)
  have hlimit := tendsto_atTop_ciInf hanti hbdd
  let a : ℝ := ⨅ n, V (x n)
  have halower : ∀ n, a ≤ V (x n) := fun n => ciInf_le hbdd n
  have ha0 : 0 ≤ a := le_ciInf fun n => hnonneg (x n)
  have hazero : a = 0 := by
    by_contra ha
    have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    have hne : ({y : E | a ≤ V y ∧ V y ≤ c} : Set E).Nonempty :=
      ⟨x 0, halower 0, hinv 0⟩
    obtain ⟨z, hz, η, hηpos, heq, hη⟩ :=
      actual_nonempty_compact_positive_annulus_has_an_attained_uniform_negative_decrement
        F V c a hF hV hV0 hapos hcompact hne hdec
    exact actual_positive_uniform_decrement_contradicts_nonnegative_trajectory_values
      F V x η hηpos hstep (fun n => hnonneg (x n))
        (fun n => hη (x n) ⟨halower n, hinv n⟩)
  simpa [a, hazero] using hlimit

theorem actual_printed_positive_annulus_minimum_route_transfers_zero_values_to_state_convergence
    (V : E → ℝ) (x : ℕ → E) (c : ℝ) (hV : Continuous V)
    (hpos : ∀ y, y ≠ 0 → 0 < V y)
    (hcompact : IsCompact {y : E | V y ≤ c})
    (hinv : ∀ n, V (x n) ≤ c)
    (hlimit : Tendsto (fun n => V (x n)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_cases hne : ({y : E | V y ≤ c ∧ ε ≤ ‖y‖} : Set E).Nonempty
  · obtain ⟨z, hz, hzpos, hmin⟩ :=
      actual_compact_annulus_away_from_zero_has_a_positive_attained_lyapunov_minimum
        V c ε hε hV hpos hcompact hne
    have hevent : ∀ᶠ n in atTop, V (x n) < V z :=
      (tendsto_order.mp hlimit).2 (V z) hzpos
    filter_upwards [hevent] with n hn
    simpa only [dist_zero_right] using
      actual_value_below_the_annulus_minimum_forces_small_state_norm
        V c ε (V z) (x n) hmin (hinv n) hn
  · apply Eventually.of_forall
    intro n
    have hn : ‖x n‖ < ε := by
      by_contra hnorm
      exact hne ⟨x n, hinv n, le_of_not_gt hnorm⟩
    simpa only [dist_zero_right] using hn


theorem actual_the_printed_positive_slope_linear_bound_tends_to_negative_infinity
    (v η : ℝ) (hη : 0 < η) :
    Tendsto (fun n : ℕ => v - (n : ℝ) * η) atTop atBot := by
  apply tendsto_atBot.mpr
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt ((v - b) / η)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmul : (N : ℝ) * η ≤ (n : ℝ) * η :=
    mul_le_mul_of_nonneg_right hnreal hη.le
  have hdiv : v - b < (N : ℝ) * η := (div_lt_iff₀ hη).mp hN
  linarith

end SafeLearning.CompleteFoundationsCompactLyapunovPrintedRoute24
