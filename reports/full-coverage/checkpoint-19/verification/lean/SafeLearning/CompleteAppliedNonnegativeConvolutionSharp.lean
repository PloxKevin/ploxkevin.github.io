import SafeLearning.CompleteAppliedNonnegativeConvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedNonnegativeConvolutionSharp
open CompleteAppliedNonnegativeConvolution

def finitePulse (N n : ℕ) : ℝ := if n<N then 1 else 0

theorem actual_finite_pulse_has_true_square_sum (N : ℕ) :
    Summable (fun n=>(finitePulse N n)^2) ∧
      (∑' n, (finitePulse N n)^2)=(N:ℝ) := by
  have hz (n : ℕ) (hn : n∉Finset.range N) : (finitePulse N n)^2=0 := by
    simp only [Finset.mem_range] at hn
    simp [finitePulse,hn]
  refine ⟨summable_of_ne_finset_zero hz,?_⟩
  rw [tsum_eq_sum hz]
  have he : (∑ n ∈ Finset.range N, (finitePulse N n)^2)=
      ∑ n ∈ Finset.range N, (1:ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [finitePulse,Finset.mem_range.mp hn]
  rw [he]
  simp

theorem actual_finite_pulse_output_prefix_is_the_impulse_partial_sum
    (h : ℕ → ℝ) (N n : ℕ) (hn : n<N) :
    causalOutput h (finitePulse N) n=∑ k ∈ Finset.range (n+1), h k := by
  unfold causalOutput
  apply Finset.sum_congr rfl
  intro k _
  have ht : n-k<N := (Nat.sub_le n k).trans_lt hn
  simp [finitePulse,ht]

theorem actual_long_pulse_output_energy_has_the_generic_prefix_lower_bound
    (h : ℕ → ℝ) (hh : ∀ k, 0≤h k) (hs : Summable h)
    (M N : ℕ) (hMN : M≤N) :
    ((N:ℝ)-(M:ℝ))*(∑ k ∈ Finset.range M, h k)^2 ≤
      ∑' n, (causalOutput h (finitePulse N) n)^2 := by
  have ho := actual_every_square_summable_input_has_a_square_summable_output h (finitePulse N)
    hh hs (actual_finite_pulse_has_true_square_sum N).1
  have hp0 : 0≤∑ k ∈ Finset.range M, h k := Finset.sum_nonneg (fun k _=>hh k)
  have hlow : (∑ n ∈ Finset.Ico M N, (∑ k ∈ Finset.range M, h k)^2) ≤
      ∑ n ∈ Finset.Ico M N, (causalOutput h (finitePulse N) n)^2 := by
    apply Finset.sum_le_sum
    intro n hn
    have hns := Finset.mem_Ico.mp hn
    rw [actual_finite_pulse_output_prefix_is_the_impulse_partial_sum h N n hns.2]
    have hpartial : (∑ k ∈ Finset.range M, h k) ≤
        ∑ k ∈ Finset.range (n+1), h k :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega : M≤n+1)) (fun k _ _=>hh k)
    have ht0 : 0≤∑ k ∈ Finset.range (n+1), h k := Finset.sum_nonneg (fun k _=>hh k)
    nlinarith
  have he : (∑ n ∈ Finset.Ico M N, (∑ k ∈ Finset.range M, h k)^2)=
      ((N:ℝ)-(M:ℝ))*(∑ k ∈ Finset.range M, h k)^2 := by
    simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul,Nat.cast_sub hMN]
  rw [he] at hlow
  exact hlow.trans (ho.1.sum_le_tsum (Finset.Ico M N) (fun n _=>sq_nonneg _))

theorem actual_every_gain_below_DC_fails_on_a_genuine_finite_pulse
    (h : ℕ → ℝ) (hh : ∀ k, 0≤h k) (hs : Summable h)
    (gain : ℝ) (hg0 : 0≤gain) (hg : gain<dcGain h) :
    ∃ N : ℕ,
      Summable (fun n=>(finitePulse N n)^2) ∧
      Summable (fun n=>(causalOutput h (finitePulse N) n)^2) ∧
      gain^2*(∑'n,(finitePulse N n)^2)<
        ∑'n,(causalOutput h (finitePulse N) n)^2 := by
  have ht : Tendsto (fun M=>∑ k ∈ Finset.range M, h k) atTop (𝓝 (dcGain h)) :=
    hs.hasSum.tendsto_sum_nat
  obtain ⟨M,hM⟩ := (ht.eventually (lt_mem_nhds hg)).exists
  let a : ℝ := ∑ k ∈ Finset.range M, h k
  have ha : gain<a := hM
  have ha0 : 0≤a := hg0.trans ha.le
  have hd : 0<a^2-gain^2 := by nlinarith
  obtain ⟨N,hN⟩ := exists_nat_gt (max (M:ℝ) ((M:ℝ)*a^2/(a^2-gain^2)))
  have hNM : (M:ℝ)<N := (le_max_left _ _).trans_lt hN
  have hMN : M≤N := by exact_mod_cast hNM.le
  have hratio : (M:ℝ)*a^2/(a^2-gain^2)<N := (le_max_right _ _).trans_lt hN
  have hlin := (div_lt_iff₀ hd).mp hratio
  have hlo := actual_long_pulse_output_energy_has_the_generic_prefix_lower_bound h hh hs M N hMN
  have hi := actual_finite_pulse_has_true_square_sum N
  have ho := actual_every_square_summable_input_has_a_square_summable_output h (finitePulse N)
    hh hs hi.1
  refine ⟨N,hi.1,ho.1,?_⟩
  rw [hi.2]
  change ((N:ℝ)-(M:ℝ))*a^2 ≤ _ at hlo
  nlinarith

theorem actual_nonnegative_summable_impulse_response_has_least_energy_gain_DC
    (h : ℕ → ℝ) (hh : ∀ k, 0≤h k) (hs : Summable h) :
    IsLeast (energyGains h) (dcGain h) := by
  refine ⟨⟨tsum_nonneg hh,fun u hu=>
    actual_every_square_summable_input_has_a_square_summable_output h u hh hs hu⟩,?_⟩
  intro gain hg
  by_contra hn
  have hsmall : gain<dcGain h := lt_of_not_ge hn
  obtain ⟨N,hi,_,hv⟩ := actual_every_gain_below_DC_fails_on_a_genuine_finite_pulse
    h hh hs gain hg.1 hsmall
  exact not_lt_of_ge (hg.2 (finitePulse N) hi).2 hv

theorem actual_generic_peak_and_energy_gains_coincide_with_DC
    (h : ℕ → ℝ) (hh : ∀ k, 0≤h k) (hs : Summable h) :
    IsLeast (peakGains h) (dcGain h) ∧ IsLeast (energyGains h) (dcGain h) :=
  ⟨actual_nonnegative_summable_impulse_response_has_least_peak_gain_DC h hh hs,
    actual_nonnegative_summable_impulse_response_has_least_energy_gain_DC h hh hs⟩

theorem actual_generic_energy_gain_is_a_true_square_root_norm_bound
    (h u : ℕ → ℝ) (hh : ∀ k, 0≤h k) (hs : Summable h)
    (hu : Summable (fun n=>(u n)^2)) :
    Real.sqrt (∑'n,(causalOutput h u n)^2) ≤
      dcGain h*Real.sqrt (∑'n,(u n)^2) := by
  have hb := (actual_every_square_summable_input_has_a_square_summable_output h u hh hs hu).2
  have hH : 0≤dcGain h := tsum_nonneg hh
  have hE : 0≤∑'n,(u n)^2 := tsum_nonneg (fun n=>sq_nonneg _)
  have hh' := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hH] at hh'
  exact hh'

end SafeLearning.CompleteAppliedNonnegativeConvolutionSharp
