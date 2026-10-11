import SafeLearning.CompleteModulesMonitoringBlockLimitsClosed22

set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace SafeLearning.CompleteModulesMonitoringBlockScale22
open SafeLearning.CompleteModulesMonitoringBlocksClosed22
open SafeLearning.CompleteModulesMonitoringBlockLimitsClosed22

private theorem stage_bounds (T : ℕ) (hn : 1 ≤ stageIndex T) :
    let n : ℝ := stageIndex T
    n^2≤(T : ℝ) ∧ (T : ℝ)≤(n+1)*(n+4) ∧ 0<n := by
  dsimp only
  obtain ⟨hl,hu⟩:=actual_every_horizon_has_the_actual_stage_bounds T
  have hnn : stageIndex T*stageIndex T≤T := by unfold elapsed at hl;nlinarith
  have ha : (stageIndex T : ℝ)^2≤(T : ℝ) := by exact_mod_cast hnn
  have hb : (T : ℝ)≤((stageIndex T : ℝ)+1)*((stageIndex T : ℝ)+4) := by
    exact_mod_cast Nat.le_of_lt hu
  exact ⟨ha,hb,by exact_mod_cast (show 0<stageIndex T by omega)⟩

theorem actual_all_horizon_time_stage_scale_error (T : ℕ) (hn : 1 ≤ stageIndex T) :
    |(T : ℝ)/(stageIndex T : ℝ)^2-1|≤9/(stageIndex T : ℝ) := by
  let n : ℝ := stageIndex T
  obtain ⟨ha,hb,hpos⟩:=stage_bounds T hn
  have hn1 : 1≤n := by dsimp [n];exact_mod_cast hn
  have he : (T : ℝ)/n^2-1=((T : ℝ)-n^2)/n^2 := by field_simp;ring
  change |(T : ℝ)/n^2-1|≤9/n
  rw [he,abs_of_nonneg (div_nonneg (sub_nonneg.mpr ha) (sq_nonneg n))]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpos) hpos).mpr
  have hdiff : (T : ℝ)-n^2≤9*n := by nlinarith
  have hh:=mul_le_mul_of_nonneg_right hdiff hpos.le
  nlinarith

theorem actual_all_horizon_transit_sqrt_scale_error (T : ℕ) (hn : 1 ≤ stageIndex T) :
    |(visits T 0 : ℝ)/Real.sqrt (T : ℝ)-2|≤6/(stageIndex T : ℝ) := by
  let n : ℝ := stageIndex T
  obtain ⟨ha,hb,hpos⟩:=stage_bounds T hn
  have hx : n≤Real.sqrt (T : ℝ) := (Real.le_sqrt hpos.le (Nat.cast_nonneg _)).mpr ha
  have hy : Real.sqrt (T : ℝ)≤n+3 := by
    apply (Real.sqrt_le_left (by dsimp [n];positivity)).mpr
    nlinarith
  obtain ⟨hlo,hup,_⟩:=actual_all_horizon_count_enclosures T
  have hl : 2*n≤(visits T 0 : ℝ) := by dsimp [n];exact_mod_cast hlo
  have hu : (visits T 0 : ℝ)≤2*(n+1) := by dsimp [n];exact_mod_cast hup
  have herr : |(visits T 0 : ℝ)-2*Real.sqrt (T : ℝ)|≤6 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  have hxp : 0<Real.sqrt (T : ℝ) := lt_of_lt_of_le hpos hx
  have he : (visits T 0 : ℝ)/Real.sqrt (T : ℝ)-2=
      ((visits T 0 : ℝ)-2*Real.sqrt (T : ℝ))/Real.sqrt (T : ℝ) := by field_simp;ring
  rw [he,abs_div,abs_of_pos hxp]
  calc
    _ ≤ 6/Real.sqrt (T : ℝ) := div_le_div_of_nonneg_right herr hxp.le
    _ ≤ 6/(stageIndex T : ℝ) := div_le_div_of_nonneg_left (by norm_num) hpos hx

theorem actual_time_div_stage_squared_tends_to_one :
    Tendsto (fun T : ℕ => (T : ℝ)/(stageIndex T : ℝ)^2) atTop (𝓝 1) := by
  have hs : Tendsto (fun T => (stageIndex T : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp actual_stage_index_tends_to_infinity
  have hbound : Tendsto (fun T => 9/(stageIndex T : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hs)
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
    ((actual_stage_index_tends_to_infinity.eventually_ge_atTop 1).mono
      fun T h => actual_all_horizon_time_stage_scale_error T h) hbound

theorem actual_transit_visits_div_sqrt_tends_to_two :
    Tendsto (fun T : ℕ => (visits T 0 : ℝ)/Real.sqrt (T : ℝ)) atTop (𝓝 2) := by
  have hs : Tendsto (fun T => (stageIndex T : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp actual_stage_index_tends_to_infinity
  have hbound : Tendsto (fun T => 6/(stageIndex T : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hs)
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
    ((actual_stage_index_tends_to_infinity.eventually_ge_atTop 1).mono
      fun T h => actual_all_horizon_transit_sqrt_scale_error T h) hbound

end SafeLearning.CompleteModulesMonitoringBlockScale22
