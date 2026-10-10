import SafeLearning.CompleteAppliedScalarEnergyAttainers

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedScalarEnergyGain
open CompleteAppliedScalarEnergyBound CompleteAppliedScalarEnergyAttainers

def actualEnergyGainBounds : Set ℝ := {gain | 0≤gain ∧
  ∀ state input : ℝ→ℝ,
    (∀ horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval state 0 horizon)→
    (∀ᵐ time ∂volume,time∈Ici (0:ℝ)→HasDerivAt state (-2*state time+input time) time)→
    state 0=0→MemLp input 2 (volume.restrict (Ioi (0:ℝ)))→
    Real.sqrt (∫time in Ioi (0:ℝ),state time^2)≤
      gain*Real.sqrt (∫time in Ioi (0:ℝ),input time^2)}

theorem actual_half_bounds_every_admitted_ac_input_output_pair :
    (1/2:ℝ)∈actualEnergyGainBounds := by
  refine ⟨by norm_num,?_⟩
  intro state input hlocal hode hinitial hinput
  exact (actual_every_square_integrable_input_has_a_square_integrable_output_and_half_energy_gain
    state input hlocal hode hinitial hinput).2.2

theorem actual_every_smaller_nonnegative_gain_is_disproved_by_a_true_finite_energy_pulse
    (gain : ℝ) (hg0 : 0≤gain) (hghalf : gain<(1/2:ℝ)) :
    ∃rate:ℝ,0<rate ∧ rate≠2 ∧
      Real.sqrt (∫time in Ioi (0:ℝ),pulseState rate time^2)>
        gain*Real.sqrt (∫time in Ioi (0:ℝ),pulseInput rate time^2) := by
  let rate : ℝ := (1-4*gain^2)/2
  have hg2 : gain^2<(1/4:ℝ) := by nlinarith
  have hr : 0<rate := by dsimp [rate];linarith
  have hrsmall : rate≤(1/2:ℝ) := by dsimp [rate];nlinarith [sq_nonneg gain]
  have hne : rate≠2 := by linarith
  refine ⟨rate,hr,hne,?_⟩
  by_contra h
  have hb : Real.sqrt (∫time in Ioi (0:ℝ),pulseState rate time^2)≤
      gain*Real.sqrt (∫time in Ioi (0:ℝ),pulseInput rate time^2) := le_of_not_gt h
  rw [actual_exponential_output_energy rate hr hne,actual_exponential_input_energy rate hr] at hb
  have hi : 0≤1/(2*rate) := by positivity
  have ho : 0≤1/(4*rate*(rate+2)) := by positivity
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) hb
  have hsi := Real.sq_sqrt hi
  have hso := Real.sq_sqrt ho
  have hsq2 : Real.sqrt (1/(4*rate*(rate+2)))^2≤
      (gain*Real.sqrt (1/(2*rate)))^2 := by simpa only [pow_two] using hsq
  rw [mul_pow,hso,hsi] at hsq2
  have hbound : 1/(4*rate*(rate+2))≤gain^2/(2*rate) := by
    simpa only [div_eq_mul_inv,mul_one,one_mul] using hsq2
  have hc := (div_le_div_iff₀ (by positivity : 0<4*rate*(rate+2))
    (by positivity : 0<2*rate)).mp hbound
  have hp : 0<(1-gain^2)*(1-4*gain^2) := mul_pos (by linarith) (by linarith)
  have hrate : 2*rate=1-4*gain^2 := by dsimp [rate];ring
  have hz : 0<2*rate := by positivity
  have hfactor : 1≤2*gain^2*(rate+2) := by
    by_contra hnot
    have hlt : 2*gain^2*(rate+2)<1 := lt_of_not_ge hnot
    have hm := mul_lt_mul_of_pos_left hlt hr
    nlinarith
  nlinarith

theorem actual_half_is_the_least_induced_energy_gain_over_all_admitted_ac_pairs :
    IsLeast actualEnergyGainBounds (1/2:ℝ) ∧ sInf actualEnergyGainBounds=1/2 := by
  have hleast : IsLeast actualEnergyGainBounds (1/2:ℝ) := by
    refine ⟨actual_half_bounds_every_admitted_ac_input_output_pair,?_⟩
    intro gain hg
    by_contra h
    have hl : gain<(1/2:ℝ) := lt_of_not_ge h
    obtain ⟨rate,hr,hne,hfail⟩ :=
      actual_every_smaller_nonnegative_gain_is_disproved_by_a_true_finite_energy_pulse gain hg.1 hl
    have hlocal : ∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval (pulseState rate) 0 horizon := by
      intro horizon _
      apply ContDiffOn.absolutelyContinuousOnInterval
      unfold pulseState
      fun_prop
    have hode : ∀ᵐtime ∂volume,time∈Ici (0:ℝ)→
        HasDerivAt (pulseState rate) (-2*pulseState rate time+pulseInput rate time) time :=
      Filter.Eventually.of_forall (fun time _=>
        (actual_exponential_pulse_has_the_true_zero_initial_ode rate hne).2 time)
    have hb := hg.2 (pulseState rate) (pulseInput rate) hlocal hode
      (actual_exponential_pulse_has_the_true_zero_initial_ode rate hne).1
      (actual_exponential_pulse_input_and_output_have_finite_energy rate hr).1
    linarith
  exact ⟨hleast,hleast.csInf_eq⟩

end SafeLearning.CompleteAppliedScalarEnergyGain
