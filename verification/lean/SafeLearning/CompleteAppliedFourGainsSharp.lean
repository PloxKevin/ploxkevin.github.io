import SafeLearning.CompleteAppliedFourGains

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedFourGainsSharp
open CompleteAppliedFourGains

def pulseInput (length time : ℕ) : ℝ := if time < length then 1 else 0

theorem actual_square_pulse_has_the_full_prefix_state_formula (length time : ℕ)
    (h : time ≤ length) :
    actualState (pulseInput length) time=5*(1-(4/5:ℝ)^time) := by
  induction time with
  | zero => simp [actualState]
  | succ time ih =>
    have ht : time < length := by omega
    rw [actualState,ih (by omega),pulseInput,ite_eq_left ht,pow_succ]
    ring

theorem actual_square_pulse_has_the_true_input_square_sum (length : ℕ) :
    Summable (fun n => (pulseInput length n)^2) ∧
      (∑' n, (pulseInput length n)^2)=(length:ℝ) := by
  have hz (n : ℕ) (hn : n ∉ Finset.range length) : (pulseInput length n)^2=0 := by
    have hh : ¬n < length := by simpa only [Finset.mem_range] using hn
    simp [pulseInput,hh]
  refine ⟨summable_of_ne_finset_zero hz,?_⟩
  rw [tsum_eq_sum hz]
  have he : (∑ n ∈ Finset.range length, (pulseInput length n)^2)=
      ∑ n ∈ Finset.range length, (1:ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [pulseInput,Finset.mem_range.mp hn]
  rw [he]
  simp

theorem actual_square_pulse_output_energy_has_the_linear_prefix_lower_bound
    (length : ℕ) :
    9*(length:ℝ)-90 ≤
      ∑ n ∈ Finset.range length, (actualOutput (pulseInput length) n)^2 := by
  have hsum : (∑ n ∈ Finset.range length, (9-18*(4/5:ℝ)^n)) ≤
      ∑ n ∈ Finset.range length, (actualOutput (pulseInput length) n)^2 := by
    apply Finset.sum_le_sum
    intro n hn
    have he := actual_square_pulse_has_the_full_prefix_state_formula length n
      (Finset.mem_range.mp hn).le
    rw [actualOutput,he]
    nlinarith [sq_nonneg ((4/5:ℝ)^n)]
  have hg := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤4/5)
    (by norm_num : (4/5:ℝ)<1)
  have hgeo := hg.summable.sum_le_tsum (Finset.range length)
    (fun n hn => pow_nonneg (by norm_num : (0:ℝ)≤4/5) n)
  rw [hg.tsum_eq] at hgeo
  norm_num at hgeo
  have he : (∑ n ∈ Finset.range length, (9-18*(4/5:ℝ)^n))=
      9*(length:ℝ)-18*(∑ n ∈ Finset.range length, (4/5:ℝ)^n) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
      ←Finset.mul_sum]
    ring
  rw [he] at hsum
  linarith

theorem actual_every_smaller_nonnegative_gain_fails_on_a_genuine_square_pulse
    (gain : ℝ) (hgain : 0 ≤ gain) (hsmall : gain < 3) :
    ∃ length : ℕ,
      Summable (fun n => (pulseInput length n)^2) ∧
      Summable (fun n => (actualOutput (pulseInput length) n)^2) ∧
      gain^2*(∑' n, (pulseInput length n)^2) <
        ∑' n, (actualOutput (pulseInput length) n)^2 := by
  have hd : 0 < 9-gain^2 := by nlinarith
  obtain ⟨length,hlength⟩ := exists_nat_gt (90/(9-gain^2))
  have hlin : 90 < (9-gain^2)*(length:ℝ) := by
    have hh := (div_lt_iff₀ hd).mp hlength
    nlinarith
  have hi := actual_square_pulse_has_the_true_input_square_sum length
  have ho := actual_every_square_summable_input_has_a_square_summable_output_with_gain_three
    (pulseInput length) hi.1
  refine ⟨length,hi.1,ho.1,?_⟩
  have hprefix := actual_square_pulse_output_energy_has_the_linear_prefix_lower_bound length
  have hfull := ho.1.sum_le_tsum (Finset.range length) (fun n hn => sq_nonneg _)
  rw [hi.2]
  nlinarith

theorem actual_source_energy_gain_three_is_the_least_gain :
    IsLeast {gain : ℝ | 0 ≤ gain ∧ ∀ input : ℕ → ℝ,
      Summable (fun n => (input n)^2) →
        (∑' n, (actualOutput input n)^2) ≤ gain^2*(∑' n, (input n)^2)} (3:ℝ) := by
  refine ⟨⟨by norm_num,?_⟩,?_⟩
  · intro input hi
    simpa [show (3:ℝ)^2=9 by norm_num] using
      (actual_every_square_summable_input_has_a_square_summable_output_with_gain_three input hi).2
  · rintro gain ⟨hg,hbound⟩
    by_contra hn
    obtain ⟨length,hi,ho,hstrict⟩ :=
      actual_every_smaller_nonnegative_gain_fails_on_a_genuine_square_pulse gain hg (lt_of_not_ge hn)
    exact (not_lt_of_ge (hbound (pulseInput length) hi)) hstrict

theorem actual_every_smaller_nonnegative_signal_norm_gain_is_violated
    (gain : ℝ) (hgain : 0 ≤ gain) (hsmall : gain < 3) :
    ∃ input : ℕ → ℝ, Summable (fun n => (input n)^2) ∧
      Summable (fun n => (actualOutput input n)^2) ∧
      gain*Real.sqrt (∑' n, (input n)^2) <
        Real.sqrt (∑' n, (actualOutput input n)^2) := by
  obtain ⟨length,hi,ho,hstrict⟩ :=
    actual_every_smaller_nonnegative_gain_fails_on_a_genuine_square_pulse gain hgain hsmall
  refine ⟨pulseInput length,hi,ho,?_⟩
  have hnon : 0 ≤ gain^2*(∑' n, (pulseInput length n)^2) :=
    mul_nonneg (sq_nonneg gain) (tsum_nonneg (fun n => sq_nonneg _))
  have h := Real.sqrt_lt_sqrt hnon hstrict
  rw [Real.sqrt_mul (sq_nonneg gain),Real.sqrt_sq hgain] at h
  exact h

theorem actual_every_unit_bounded_input_has_peak_output_at_most_three
    (input : ℕ → ℝ) (hinput : ∀ n, |input n| ≤ 1) :
    ∀ n, |actualOutput input n| ≤ 3 := by
  have hs (n : ℕ) : |actualState input n| ≤ 5 := by
    induction n with
    | zero => simp [actualState]
    | succ n ih =>
      rw [actualState]
      have h := abs_add_le ((4/5)*actualState input n) (input n)
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4/5)] at h
      linarith [hinput n]
  intro n
  rw [actualOutput,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3/5)]
  linarith [hs n]

theorem actual_unit_constant_input_output_tends_to_three :
    Tendsto (actualOutput (fun _ => 1)) atTop (𝓝 (3:ℝ)) := by
  have hs (n : ℕ) : actualState (fun _ => 1) n=5*(1-(4/5:ℝ)^n) := by
    induction n with
    | zero => simp [actualState]
    | succ n ih => rw [actualState,ih,pow_succ]; ring
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤4/5)
    (by norm_num : (4/5:ℝ)<1)
  have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (hc.sub hp).const_mul (3:ℝ)
  convert h using 1
  · ext n
    rw [actualOutput,hs]
    ring
  · norm_num

theorem actual_peak_gain_three_is_the_least_unit_input_bound :
    IsLeast {gain : ℝ | ∀ input : ℕ → ℝ, (∀ n, |input n| ≤ 1) →
      ∀ n, |actualOutput input n| ≤ gain} (3:ℝ) := by
  refine ⟨actual_every_unit_bounded_input_has_peak_output_at_most_three,?_⟩
  intro gain hg
  apply le_of_tendsto actual_unit_constant_input_output_tends_to_three
  exact Filter.Eventually.of_forall (fun n =>
    (le_abs_self _).trans (hg (fun _ => 1) (fun n => by norm_num) n))

end SafeLearning.CompleteAppliedFourGainsSharp
