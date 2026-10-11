import SafeLearning.CompleteCompactLyapunov

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesLandscapeLyapunovStability

def originStable {E : Type*} [NormedAddCommGroup E] (F : E → E) : Prop :=
  ∀ epsilon > 0, ∃ delta > 0, ∀ x : E,
    ‖x‖ < delta → ∀ n : ℕ, ‖(F^[n]) x‖ < epsilon

theorem actual_positive_definite_compact_sublevel_has_a_strict_small_value_neighborhood
    {E : Type*} [NormedAddCommGroup E] (V : E → ℝ) (c epsilon : ℝ)
    (hc : 0 < c) (hepsilon : 0 < epsilon) (hV : Continuous V)
    (hpositive : ∀ x, x ≠ 0 → 0 < V x)
    (hcompact : IsCompact {x : E | V x ≤ c}) :
    ∃ alpha > 0, alpha ≤ c ∧
      ∀ x, V x ≤ c → V x < alpha → ‖x‖ < epsilon := by
  let D : Set E := {x | V x ≤ c} ∩ {x | epsilon ≤ ‖x‖}
  have hD : IsCompact D :=
    hcompact.inter_right (isClosed_le continuous_const continuous_norm)
  by_cases hne : D.Nonempty
  · obtain ⟨p, hp, hminimum⟩ := hD.exists_isMinOn hne hV.continuousOn
    have hp0 : p ≠ 0 := by
      intro hzero
      have hnorm : epsilon ≤ ‖p‖ := hp.2
      rw [hzero, norm_zero] at hnorm
      linarith
    have hpv := hpositive p hp0
    refine ⟨min c (V p), lt_min hc hpv, min_le_left _ _, ?_⟩
    intro x hx hsmall
    by_contra hout
    have hxD : x ∈ D := ⟨hx, le_of_not_gt hout⟩
    have hm : V p ≤ V x := hminimum hxD
    have ha := min_le_right c (V p)
    linarith
  · refine ⟨c, hc, le_rfl, ?_⟩
    intro x hx _
    by_contra hout
    exact hne ⟨x, hx, le_of_not_gt hout⟩

theorem actual_positive_compact_strict_lyapunov_certificate_proves_origin_stability
    {E : Type*} [NormedAddCommGroup E] (F : E → E) (V : E → ℝ) (c : ℝ)
    (hc : 0 < c) (hV : Continuous V) (hV0 : V 0 = 0)
    (hpositive : ∀ x, x ≠ 0 → 0 < V x)
    (hcompact : IsCompact {x : E | V x ≤ c}) (hF0 : F 0 = 0)
    (hdecrease : ∀ x, V x ≤ c → x ≠ 0 → V (F x) < V x) :
    originStable F := by
  intro epsilon hepsilon
  obtain ⟨alpha, halpha, hac, hsmall⟩ :=
    actual_positive_definite_compact_sublevel_has_a_strict_small_value_neighborhood
      V c epsilon hc hepsilon hV hpositive hcompact
  obtain ⟨delta, hdelta, hclose⟩ :=
    Metric.continuousAt_iff.mp (hV.continuousAt (x := 0)) alpha halpha
  refine ⟨delta, hdelta, ?_⟩
  intro x hx n
  have hxV : V x < alpha := by
    have hd := hclose (x := x) (by simpa only [dist_zero_right] using hx)
    rw [Real.dist_eq, hV0, sub_zero] at hd
    exact (le_abs_self _).trans_lt hd
  have hxsub : V x ≤ c := hxV.le.trans hac
  have hv : ∀ n : ℕ, V ((F^[n]) x) ≤ V x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      by_cases hz : (F^[n]) x = 0
      · simpa only [hz, hF0] using ih
      · exact (hdecrease _ (ih.trans hxsub) hz).le.trans ih
  exact hsmall _ ((hv n).trans hxsub) ((hv n).trans_lt hxV)

theorem actual_positive_compact_strict_certificate_combines_stability_and_attraction
    {E : Type*} [NormedAddCommGroup E] (F : E → E) (V : E → ℝ) (c : ℝ)
    (hc : 0 < c) (hF : Continuous F) (hV : Continuous V) (hV0 : V 0 = 0)
    (hpositive : ∀ x, x ≠ 0 → 0 < V x)
    (hcompact : IsCompact {x : E | V x ≤ c}) (hF0 : F 0 = 0)
    (hdecrease : ∀ x, V x ≤ c → x ≠ 0 → V (F x) < V x) :
    originStable F ∧ ∀ x, V x ≤ c → Tendsto (fun n : ℕ => (F^[n]) x) atTop (𝓝 0) := by
  refine ⟨actual_positive_compact_strict_lyapunov_certificate_proves_origin_stability
    F V c hc hV hV0 hpositive hcompact hF0 hdecrease, ?_⟩
  intro x hx
  have hn : ∀ y, 0 ≤ V y := by
    intro y
    by_cases hy : y = 0
    · simp only [hy, hV0, le_refl]
    · exact (hpositive y hy).le
  exact CompleteCompactLyapunov.compact_strict_lyapunov_convergence F V
    (fun n : ℕ => (F^[n]) x) c hF hV hcompact hn hF0
    (fun n => Function.iterate_succ_apply' F n x) (by simpa using hx) hdecrease

theorem actual_unstable_doubling_iterates_are_the_true_exponential_sequence
    (x : ℝ) (n : ℕ) : ((fun y : ℝ => 2*y)^[n]) x = (2 : ℝ)^n*x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring

theorem actual_doubling_origin_is_not_lyapunov_stable :
    ¬originStable (fun x : ℝ => 2*x) := by
  intro hstable
  obtain ⟨delta, hdelta, hstay⟩ := hstable 1 (by norm_num)
  have hx : ‖delta/2‖ < delta := by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
  have hp : Tendsto (fun n : ℕ => (2 : ℝ)^n*(delta/2)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const (by positivity)
  obtain ⟨n, hn⟩ := (hp.eventually (eventually_ge_atTop (1 : ℝ))).exists
  have hbound := hstay (delta/2) hx n
  rw [actual_unstable_doubling_iterates_are_the_true_exponential_sequence, Real.norm_eq_abs] at hbound
  have ha := le_abs_self ((2 : ℝ)^n*(delta/2))
  linarith

theorem actual_zero_level_compact_certificate_can_be_vacuous_and_unstable :
    IsCompact {x : ℝ | x^2 ≤ 0} ∧
    (∀ x : ℝ, x^2 ≤ 0 → x ≠ 0 → (2*x)^2 < x^2) ∧
    ¬originStable (fun x : ℝ => 2*x) := by
  have he : {x : ℝ | x^2 ≤ 0} = {0} := by
    ext x
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro hx
      nlinarith [sq_nonneg x]
    · intro hx
      simp [hx]
  refine ⟨he ▸ isCompact_singleton, ?_, actual_doubling_origin_is_not_lyapunov_stable⟩
  intro x hx hnonzero
  have hz : x = 0 := by nlinarith [sq_nonneg x]
  exact False.elim (hnonzero hz)

end SafeLearning.CompleteModulesLandscapeLyapunovStability
