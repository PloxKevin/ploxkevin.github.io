import SafeLearning.CompleteModulesMonitoringBlocks22

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
namespace SafeLearning.CompleteModulesMonitoringBlockLimits22
open SafeLearning.CompleteModulesMonitoringBlocks22

theorem actual_stage_index_tends_to_infinity : Tendsto stageIndex atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (elapsed n)] with T hT
  obtain ⟨_,hu⟩:=actual_every_horizon_has_the_actual_stage_bounds T
  by_contra h
  have hn : stageIndex T+1≤n := by omega
  have hm : elapsed (stageIndex T+1)≤elapsed n := by
    unfold elapsed
    exact Nat.mul_le_mul hn (Nat.add_le_add_right hn 3)
  omega

private theorem actual_stage_successor_is_admitted (n r : ℕ) (hr : r+1<2*n+4) :
    ∃ a : Bool, SafeLearning.CompleteMonitoringMeans22.model.transition
      (stageState n r) a (stageState n (r+1))=1 := by
  unfold stageState
  split_ifs <;> try omega
  all_goals first
    | solve | refine ⟨false,?_⟩;simp [SafeLearning.CompleteMonitoringMeans22.model]
    | solve | refine ⟨true,?_⟩;simp [SafeLearning.CompleteMonitoringMeans22.model]

theorem actual_source_growing_block_path_is_admitted :
    path 0=0 ∧ ∀ t, ∃ a : Bool,
      SafeLearning.CompleteMonitoringMeans22.model.transition (path t) a (path (t+1))=1 := by
  constructor
  · have h:=actual_path_at_every_round_offset 0 0 (by omega)
    simpa [elapsed,stageState] using h
  intro t
  let n:=stageIndex t
  let r:=t-elapsed n
  obtain ⟨hl,hu⟩:=actual_every_horizon_has_the_actual_stage_bounds t
  have ht : t=elapsed n+r := by dsimp [n,r];omega
  have hr : r<2*n+4 := by rw [actual_elapsed_successor] at hu;dsimp [r,n];omega
  rw [ht,actual_path_at_every_round_offset n r hr]
  by_cases hi : r+1<2*n+4
  · rw [show elapsed n+r+1=elapsed n+(r+1) by omega,
      actual_path_at_every_round_offset n (r+1) hi]
    exact actual_stage_successor_is_admitted n r hi
  · have he : r=2*n+3 := by omega
    have hn : elapsed n+r+1=elapsed (n+1) := by rw [actual_elapsed_successor];omega
    rw [hn]
    have hp:=actual_path_at_every_round_offset (n+1) 0 (by omega)
    simp only [Nat.add_zero] at hp
    rw [hp]
    have hlast : stageState n r=2 := by
      unfold stageState
      rw [if_neg (by omega),if_neg (by omega)]
    rw [hlast]
    exact ⟨false,by simp [stageState,SafeLearning.CompleteMonitoringMeans22.model]⟩

theorem actual_transit_count_at_every_horizon (T : ℕ) :
    (visits T 0 : ℝ) ≤ 2*Real.sqrt (T : ℝ)+2 := by
  have hl:= (actual_every_horizon_has_the_actual_stage_bounds T).1
  have hc:=(actual_all_horizon_count_enclosures T).2.1
  have hsq : (stageIndex T : ℝ)^2 ≤ (T : ℝ) := by
    have hh : stageIndex T*stageIndex T≤T := by
      unfold elapsed at hl
      nlinarith
    simpa only [pow_two] using (show (stageIndex T : ℝ)*(stageIndex T : ℝ)≤(T : ℝ) by exact_mod_cast hh)
  have hn : (stageIndex T : ℝ)≤Real.sqrt (T : ℝ) := by
    exact (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hsq
  have hv : (visits T 0 : ℝ)≤2*((stageIndex T : ℝ)+1) := by exact_mod_cast hc
  linarith

def fraction (T : ℕ) (s : Fin 3) : ℝ := (visits T s : ℝ)/(T : ℝ)

theorem actual_every_partial_horizon_fraction_error (T : ℕ) (hn : 1 ≤ stageIndex T) :
    |fraction T 0|≤4/(stageIndex T : ℝ) ∧
    |fraction T 1-1/2|≤4/(stageIndex T : ℝ) ∧
    |fraction T 2-1/2|≤4/(stageIndex T : ℝ) := by
  let n : ℝ := stageIndex T
  have hn0 : 0<n := by dsimp [n];exact_mod_cast (show 0<stageIndex T by omega)
  have hn1 : 1≤n := by dsimp [n];exact_mod_cast hn
  obtain ⟨hl,hu⟩:=actual_every_horizon_has_the_actual_stage_bounds T
  obtain ⟨_,hz,ha,hb,hc,hd⟩:=actual_all_horizon_count_enclosures T
  have hlo : n*(n+3)≤(T : ℝ) := by dsimp [n];exact_mod_cast hl
  have hup : (T : ℝ)≤(n+1)*(n+4) := by
    have h := Nat.le_of_lt hu
    dsimp [n]
    exact_mod_cast h
  have hz' : (visits T 0 : ℝ)≤2*(n+1) := by dsimp [n];exact_mod_cast hz
  have ha' : n*(n+1)≤2*(visits T 1 : ℝ) := by dsimp [n];exact_mod_cast ha
  have hb' : 2*(visits T 1 : ℝ)≤(n+1)*(n+2) := by dsimp [n];exact_mod_cast hb
  have hc' : n*(n+1)≤2*(visits T 2 : ℝ) := by dsimp [n];exact_mod_cast hc
  have hd' : 2*(visits T 2 : ℝ)≤(n+1)*(n+2) := by dsimp [n];exact_mod_cast hd
  have hT : 0<(T : ℝ) := by nlinarith
  have herr (v : ℝ) (hlo' : n*(n+1)≤2*v) (hup' : 2*v≤(n+1)*(n+2)) :
      |v/(T : ℝ)-1/2|≤4/n := by
    have hlow : ((T : ℝ)-2*v)*n≤8*(T : ℝ) := by
      calc
        ((T : ℝ)-2*v)*n ≤ (4*n+4)*n :=
          mul_le_mul_of_nonneg_right (by nlinarith) hn0.le
        _ ≤ 8*(T : ℝ) := by nlinarith
    have hupp : (2*v-(T : ℝ))*n≤8*(T : ℝ) := by
      calc
        (2*v-(T : ℝ))*n ≤ 2*n :=
          mul_le_mul_of_nonneg_right (by nlinarith) hn0.le
        _ ≤ 8*(T : ℝ) := by nlinarith
    have hid : v/(T : ℝ)-1/2+4/n =
        (2*v*n-(T : ℝ)*n+8*(T : ℝ))/(2*(T : ℝ)*n) := by
      field_simp
      <;> ring
    have hjd : 4/n-(v/(T : ℝ)-1/2) =
        ((T : ℝ)*n-2*v*n+8*(T : ℝ))/(2*(T : ℝ)*n) := by
      field_simp
      <;> ring
    have hp : 0<2*(T : ℝ)*n := by positivity
    have hleft : 0≤v/(T : ℝ)-1/2+4/n := by
      rw [hid];apply div_nonneg _ hp.le;nlinarith
    have hright : 0≤4/n-(v/(T : ℝ)-1/2) := by
      rw [hjd];apply div_nonneg _ hp.le;nlinarith
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  refine ⟨?_,herr _ ha' hb',herr _ hc' hd'⟩
  unfold fraction
  rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hT))]
  apply (div_le_div_iff₀ hT hn0).2
  nlinarith

theorem actual_all_horizon_fraction_limits :
    Tendsto (fun T => fraction T 0) atTop (𝓝 0) ∧
    Tendsto (fun T => fraction T 1) atTop (𝓝 (1/2)) ∧
    Tendsto (fun T => fraction T 2) atTop (𝓝 (1/2)) := by
  have hs : Tendsto (fun T => (stageIndex T : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp actual_stage_index_tends_to_infinity
  have hb : Tendsto (fun T => 4/(stageIndex T : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hs)
  have hev : ∀ᶠ T in atTop, 1 ≤ stageIndex T :=
    actual_stage_index_tends_to_infinity.eventually_ge_atTop 1
  have hz : Tendsto (fun T => |fraction T 0|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      (hev.mono fun T h => (actual_every_partial_horizon_fraction_error T h).1) hb
  have ha : Tendsto (fun T => |fraction T 1-1/2|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      (hev.mono fun T h => (actual_every_partial_horizon_fraction_error T h).2.1) hb
  have hc : Tendsto (fun T => |fraction T 2-1/2|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      (hev.mono fun T h => (actual_every_partial_horizon_fraction_error T h).2.2) hb
  exact ⟨(tendsto_zero_iff_abs_tendsto_zero _).mpr hz,
    (tendsto_iff_dist_tendsto_zero).mpr (by simpa [Real.dist_eq] using ha),
    (tendsto_iff_dist_tendsto_zero).mpr (by simpa [Real.dist_eq] using hc)⟩

theorem actual_transit_count_is_bigO_sqrt :
    (fun T : ℕ => (visits T 0 : ℝ)) =O[atTop] (fun T => Real.sqrt (T : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨4,?_⟩
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hsq : 1≤Real.sqrt (T : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
    exact_mod_cast hT
  have hv:=actual_transit_count_at_every_horizon T
  change |(visits T 0 : ℝ)| ≤ 4*|Real.sqrt (T : ℝ)|
  rw [abs_of_nonneg (Nat.cast_nonneg (visits T 0) : (0 : ℝ)≤_),
    abs_of_nonneg (Real.sqrt_nonneg (T : ℝ))]
  linarith


end SafeLearning.CompleteModulesMonitoringBlockLimits22
