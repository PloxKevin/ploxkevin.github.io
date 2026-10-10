import SafeLearning.CompleteFoundationsFourPowerBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset Filter Set
open scoped Topology
namespace SafeLearning.CompleteFoundationsFourPowerBlockLimits
open CompleteFoundationsFourPowerBlocks

def zeroEndpoint (k : ℕ) : ℕ := 4^(k+1)-1
def oneEndpoint (k : ℕ) : ℕ := 2*4^k-1

theorem actual_average_is_the_one_based_first_T_step_average (T : ℕ) :
    average T = (∑ i ∈ Finset.range T, (reward (i+1):ℝ)) / (T:ℝ) := by
  unfold average countBefore
  rw [Finset.sum_range_succ']
  simp only [actual_zero_reward,add_zero,Nat.cast_sum]

theorem actual_both_block_endpoint_sequences_go_to_infinity :
    Tendsto zeroEndpoint atTop atTop ∧ Tendsto oneEndpoint atTop atTop := by
  constructor <;> apply tendsto_atTop.mpr <;> intro N <;>
    apply eventually_atTop.mpr <;> refine ⟨N,?_⟩ <;> intro k hk
  · have hp := Nat.lt_pow_self (by norm_num : 1 < (4:ℕ)) (n:=k+1)
    dsimp [zeroEndpoint]
    omega
  · have hp := Nat.lt_pow_self (by norm_num : 1 < (4:ℕ)) (n:=k)
    dsimp [oneEndpoint]
    omega

theorem actual_every_zero_block_endpoint_average_is_one_third (k : ℕ) :
    average (zeroEndpoint k) = (1/3:ℝ) := by
  have hp : 1 < (4:ℕ)^(k+1) := by
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have he : zeroEndpoint k+1=4^(k+1) := by dsimp [zeroEndpoint];omega
  have hc := actual_zero_block_endpoint_count k
  have hh : 3*(countBefore (zeroEndpoint k+1):ℝ) = (zeroEndpoint k:ℝ) := by
    rw [he]
    exact_mod_cast hc
  have ht : (0:ℝ)<(zeroEndpoint k:ℝ) := by dsimp [zeroEndpoint];exact_mod_cast (show 0<4^(k+1)-1 by omega)
  unfold average
  apply (div_eq_iff ht.ne').mpr
  linarith

theorem actual_every_one_block_endpoint_average (k : ℕ) :
    average (oneEndpoint k) = 2/3 + 1/(3*(oneEndpoint k:ℝ)) := by
  have hp : 0 < (4:ℕ)^k := pow_pos (by norm_num) _
  have he : oneEndpoint k+1=2*4^k := by dsimp [oneEndpoint];omega
  have hc := actual_one_block_endpoint_count k
  rw [pow_succ] at hc
  have hh : 3*(countBefore (oneEndpoint k+1):ℝ)=2*(oneEndpoint k:ℝ)+1 := by
    rw [he]
    have ht : 3*countBefore (2*4^k)=2*(2*4^k-1)+1 := by omega
    dsimp [oneEndpoint]
    exact_mod_cast ht
  have ht : (0:ℝ)<(oneEndpoint k:ℝ) := by dsimp [oneEndpoint];exact_mod_cast (show 0<2*4^k-1 by omega)
  unfold average
  apply (div_eq_iff ht.ne').mpr
  field_simp
  nlinarith

theorem actual_one_over_three_horizon_tends_to_zero :
    Tendsto (fun T : ℕ => 1/(3*(T:ℝ))) atTop (𝓝 (0:ℝ)) := by
  have ht : Tendsto (fun T : ℕ => 3*(T:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<3)
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp ht

theorem actual_two_block_endpoint_average_limits :
    Tendsto (average ∘ zeroEndpoint) atTop (𝓝 (1/3:ℝ)) ∧
      Tendsto (average ∘ oneEndpoint) atTop (𝓝 (2/3:ℝ)) := by
  constructor
  · simpa only [Function.comp_def,actual_every_zero_block_endpoint_average_is_one_third]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/3:ℝ)) atTop (𝓝 (1/3:ℝ)))
  · have hz := actual_one_over_three_horizon_tends_to_zero.comp
      actual_both_block_endpoint_sequences_go_to_infinity.2
    simpa only [Function.comp_def,actual_every_one_block_endpoint_average,add_zero]
      using (tendsto_const_nhds.add hz : Tendsto
        (fun k : ℕ => (2/3:ℝ)+1/(3*(oneEndpoint k:ℝ))) atTop (𝓝 ((2/3:ℝ)+0)))

theorem actual_four_power_block_average_liminf_and_limsup :
    liminf (fun T => (average T:EReal)) atTop = ((1/3:ℝ):EReal) ∧
      limsup (fun T => (average T:EReal)) atTop = ((2/3:ℝ):EReal) := by
  have hlow := EReal.tendsto_coe.mpr actual_two_block_endpoint_average_limits.1
  have hhigh := EReal.tendsto_coe.mpr actual_two_block_endpoint_average_limits.2
  have hcompLow := actual_both_block_endpoint_sequences_go_to_infinity.1.liminf_le_liminf_comp
      (u:=fun T => (average T:EReal))
  have hcompHigh := actual_both_block_endpoint_sequences_go_to_infinity.2.limsup_comp_le_limsup
      (u:=fun T => (average T:EReal))
  have hlower : ((1/3:ℝ):EReal) ≤ liminf (fun T => (average T:EReal)) atTop := by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    apply eventually_atTop.mpr
    refine ⟨1,?_⟩
    intro T hT
    exact EReal.coe_le_coe_iff.mpr (actual_all_horizon_average_bounds T (by omega)).1
  have hupper : limsup (fun T => (average T:EReal)) atTop ≤ ((2/3:ℝ):EReal) := by
    have hc : Tendsto (fun T : ℕ => (2/3:ℝ)+1/(3*(T:ℝ))) atTop (𝓝 (2/3:ℝ)) := by
      simpa only [add_zero] using tendsto_const_nhds.add actual_one_over_three_horizon_tends_to_zero
    have hce := EReal.tendsto_coe.mpr hc
    have hb : ∀ᶠ T : ℕ in atTop,
        (average T:EReal) ≤ (((2/3:ℝ)+1/(3*(T:ℝ))):EReal) := by
      apply eventually_atTop.mpr
      refine ⟨1,?_⟩
      intro T hT
      exact EReal.coe_le_coe_iff.mpr (actual_all_horizon_average_bounds T (by omega)).2
    exact (limsup_le_limsup hb).trans_eq hce.limsup_eq
  constructor
  · exact le_antisymm (hcompLow.trans_eq hlow.liminf_eq) hlower
  · exact le_antisymm hupper (hhigh.limsup_eq ▸ hcompHigh)

theorem actual_four_power_block_average_has_no_ordinary_limit :
    ¬ ∃ l : ℝ, Tendsto average atTop (𝓝 l) := by
  rintro ⟨l,hl⟩
  have h1 := tendsto_nhds_unique
    (hl.comp actual_both_block_endpoint_sequences_go_to_infinity.1)
    actual_two_block_endpoint_average_limits.1
  have h2 := tendsto_nhds_unique
    (hl.comp actual_both_block_endpoint_sequences_go_to_infinity.2)
    actual_two_block_endpoint_average_limits.2
  linarith

end SafeLearning.CompleteFoundationsFourPowerBlockLimits
