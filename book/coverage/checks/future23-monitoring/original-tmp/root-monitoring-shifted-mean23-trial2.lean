import SafeLearning.CompleteMonitoringDeterministicPath23
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteMonitoringShiftedMean23
open Filter Finset SafeLearning.CompleteMonitoringDualTrajectory23
open scoped Topology

theorem actual_fixed_shift_preserves_any_convergent_time_average (u : ℕ → ℝ)
    (K : ℕ) (L : ℝ) (hu : Tendsto (fun N => average u N) atTop (𝓝 L)) :
    Tendsto (fun N => average (fun n => u (n+K)) N) atTop (𝓝 L) := by
  let C : ℝ := ∑ n ∈ range K,u n
  have ha := hu.comp (tendsto_add_atTop_nat K)
  have hk : Tendsto (fun N : ℕ => (K:ℝ)/(N:ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=(K:ℝ))).mul (tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ))
  have hc : Tendsto (fun N : ℕ => C/(N:ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=C)).mul (tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ))
  have ht : Tendsto (fun N : ℕ => (1+(K:ℝ)/(N:ℝ))*average u (N+K)-C/(N:ℝ)) atTop (𝓝 L) := by
    convert ((tendsto_const_nhds (x:=(1:ℝ))).add hk).mul ha |>.sub hc using 1 <;> simp
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hn : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  have hnk : ((N+K:ℕ):ℝ)≠0 := by exact_mod_cast (by omega : N+K≠0)
  have hs : (∑ n ∈ range (N+K),u n)=C+∑ n ∈ range N,u (n+K) := by
    rw [Nat.add_comm N K,sum_range_add]
    dsimp [C]
    simp_rw [Nat.add_comm K]
  unfold average
  rw [hs]
  push_cast
  field_simp
  ring

theorem actual_arbitrary_fixed_prefix_followed_by_the_same_shifted_tail
    (u v : ℕ → ℝ) (K : ℕ) (h : ∀ n, u (n+K)=v n) (L : ℝ) :
    Tendsto (fun N => average u N) atTop (𝓝 L) ↔
      Tendsto (fun N => average v N) atTop (𝓝 L) := by
  constructor
  · intro hu
    have ht := actual_fixed_shift_preserves_any_convergent_time_average u K L hu
    simpa only [h] using ht
  · intro hv
    let w : ℕ → ℝ := fun n => if n < K then 0 else v (n-K)
    have hwshift : ∀ n, w (n+K)=v n := by intro n; simp [w]
    have hw : Tendsto (fun N => average w N) atTop (𝓝 L) := by
      let C : ℝ := ∑ n ∈ range K,w n
      have hc : Tendsto (fun N : ℕ => C/(N:ℝ)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=C)).mul (tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ))
      have hk : Tendsto (fun N : ℕ => (K:ℝ)/(N:ℝ)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=(K:ℝ))).mul (tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ))
      have hn : Tendsto (fun N : ℕ => N-K) atTop atTop := tendsto_sub_atTop_nat K
      have ht := hc.add (((tendsto_const_nhds (x:=(1:ℝ))).sub hk).mul (hv.comp hn))
      have : Tendsto (fun N : ℕ => C/(N:ℝ)+(1-(K:ℝ)/(N:ℝ))*average v (N-K)) atTop (𝓝 L) := by simpa using ht
      apply this.congr'
      filter_upwards [eventually_ge_atTop (K+1)] with N hN
      have hle : K≤N := by omega
      have hn0 : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
      have hnk : ((N-K:ℕ):ℝ)≠0 := by exact_mod_cast (by omega : N-K≠0)
      have hs : (∑ n ∈ range N,w n)=C+∑ n ∈ range (N-K),v n := by
        calc
          (∑ n ∈ range N,w n) = ∑ n ∈ range (K+(N-K)),w n := by congr 1; omega
          _ = C+∑ n ∈ range (N-K),v n := by
            rw [sum_range_add]
            dsimp [C]
            simp_rw [Nat.add_comm K,hwshift]
      unfold average
      rw [hs]
      rw [Nat.cast_sub hle]
      have hnk' : (N:ℝ)-(K:ℝ)≠0 := by simpa only [Nat.cast_sub hle] using hnk
      field_simp [hn0,hnk']
      ring
    exact (actual_any_fixed_finite_prefix_change_preserves_time_average_limits u w K
      (fun n hn => by obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le hn; simpa [w,Nat.add_comm] using h j) L).mpr hw
end SafeLearning.CompleteMonitoringShiftedMean23
