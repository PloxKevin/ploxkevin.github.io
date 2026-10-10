import SafeLearning.CompleteAppliedDiscreteLQR
import SafeLearning.CompleteAppliedIntegralTracking

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedDiscreteLQRNumbers
open SafeLearning.CompleteAppliedDiscreteLQR
open SafeLearning.CompleteAppliedIntegralTracking

theorem actual_positive_riccati_root_has_a_rigorous_rational_enclosure :
    (1952233/1000000:ℝ)<sourceP ∧ sourceP<1952234/1000000 := by
  have hs := actual_sqrt_and_both_source_riccati_roots.1
  have hn := Real.sqrt_nonneg (949:ℝ)
  have hl : (3080584/100000:ℝ)<Real.sqrt 949 := by nlinarith
  have hu : Real.sqrt 949<(3080585/100000:ℝ) := by nlinarith
  dsimp [sourceP]
  constructor <;> linarith

theorem actual_gain_and_pole_have_rigorous_rational_enclosures :
    (793528/1000000:ℝ)<sourceK ∧ sourceK<793529/1000000 ∧
    (406471/1000000:ℝ)<sourcePole ∧ sourcePole<406472/1000000 := by
  have hp := actual_positive_riccati_root_has_a_rigorous_rational_enclosure
  have hd : (0:ℝ)<1+sourceP := by linarith [hp.1]
  have hl : (793528/1000000:ℝ)<sourceK := by
    unfold sourceK
    apply (lt_div_iff₀ hd).mpr
    nlinarith [hp.1]
  have hu : sourceK<(793529/1000000:ℝ) := by
    unfold sourceK
    apply (div_lt_iff₀ hd).mpr
    nlinarith [hp.2]
  refine ⟨hl,hu,?_,?_⟩ <;> dsimp [sourcePole] <;> linarith

theorem actual_scaled_gain_boundaries_have_rigorous_rational_enclosures :
    (252038/1000000:ℝ)<(1/5)/sourceK ∧ (1/5)/sourceK<252040/1000000 ∧
    (2772425/1000000:ℝ)<(11/5)/sourceK ∧ (11/5)/sourceK<2772430/1000000 := by
  have hk := actual_gain_and_pole_have_rigorous_rational_enclosures
  have hd := actual_gain_and_pole_are_derived_and_stabilizing.1
  refine ⟨?_,?_,?_,?_⟩
  · apply (lt_div_iff₀ hd).mpr;nlinarith [hk.2.1]
  · apply (div_lt_iff₀ hd).mpr;nlinarith [hk.1]
  · apply (lt_div_iff₀ hd).mpr;nlinarith [hk.2.1]
  · apply (div_lt_iff₀ hd).mpr;nlinarith [hk.1]

theorem actual_all_source_discrete_LQR_decimal_displays_are_nearest_three_roundings :
    |sourceP-(1952/1000:ℝ)|<1/2000 ∧
    |sourceK-(794/1000:ℝ)|<1/2000 ∧
    |sourcePole-(406/1000:ℝ)|<1/2000 ∧
    |(1/5)/sourceK-(252/1000:ℝ)|<1/2000 ∧
    |(11/5)/sourceK-(2772/1000:ℝ)|<1/2000 := by
  have hp := actual_positive_riccati_root_has_a_rigorous_rational_enclosure
  have hk := actual_gain_and_pole_have_rigorous_rational_enclosures
  have hb := actual_scaled_gain_boundaries_have_rigorous_rational_enclosures
  refine ⟨?_,?_,?_,?_,?_⟩ <;> rw [abs_lt] <;> constructor <;> linarith

theorem actual_discrete_LQR_true_quantities_differ_from_the_printed_decimals :
    sourceP≠(1952/1000:ℝ) ∧ sourceK≠(794/1000:ℝ) ∧
    sourcePole≠(406/1000:ℝ) ∧ (1/5)/sourceK≠(252/1000:ℝ) ∧
    (11/5)/sourceK≠(2772/1000:ℝ) := by
  have hp := actual_positive_riccati_root_has_a_rigorous_rational_enclosure
  have hk := actual_gain_and_pole_have_rigorous_rational_enclosures
  have hb := actual_scaled_gain_boundaries_have_rigorous_rational_enclosures
  refine ⟨?_,?_,?_,?_,?_⟩ <;> intro h <;> linarith

theorem actual_rounded_P_input_is_only_a_proxy_and_the_rounded_gain_iff_is_false :
    ((6/5:ℝ)*(1952/1000)/(2952/1000))=488/615 ∧
    (488/615:ℝ)≠794/1000 ∧
    |(6/5:ℝ)-(794/1000)*(252/1000)|<1 ∧
    ¬((252/1000:ℝ)<252/1000 ∧ (252/1000:ℝ)<2772/1000) ∧
    ¬|(6/5:ℝ)-(252/1000)*sourceK|<1 := by
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
  rw [actual_scaled_gain_stability_region_is_exact]
  have hb := actual_scaled_gain_boundaries_have_rigorous_rational_enclosures.1
  intro h
  linarith [h.1]

theorem actual_P_only_steady_state_and_error_are_roundings_not_equalities :
    |(10/7:ℝ)-(1429/1000:ℝ)|<1/2000 ∧
    |(-3/7:ℝ)-(-429/1000:ℝ)|<1/2000 ∧
    (10/7:ℝ)≠1429/1000 ∧ (-3/7:ℝ)≠-429/1000 := by norm_num

theorem actual_PI_literal_Schur_checks_and_error_limit
    (x : ℕ → State) (hstep : ∀n,x (n+1)=piStep (x n)) :
    |(3/10:ℝ)|<1 ∧ (11/10:ℝ)<1+3/10 ∧
    Tendsto (fun n=>1-x n 0) atTop (𝓝 0) := by
  refine ⟨by norm_num,by norm_num,?_⟩
  have ht := tendsto_pi_nhds.mp (actual_every_source_PI_recurrence_converges x hstep) 0
  simpa [equilibrium] using (tendsto_const_nhds (x:=(1:ℝ))).sub ht

end SafeLearning.CompleteAppliedDiscreteLQRNumbers
