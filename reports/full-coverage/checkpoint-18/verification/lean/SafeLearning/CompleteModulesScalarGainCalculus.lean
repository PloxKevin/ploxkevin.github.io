import SafeLearning.CompleteModulesScalarBoundedReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
open scoped Topology
namespace SafeLearning.CompleteModulesScalarGainCalculus
open CompleteModulesScalarBoundedReal

theorem actual_required_scalar_gain_has_source_derivative (storage : ℝ)
    (hden : 3*storage-4≠0) :
    HasDerivAt actualScalarRequiredGainSquared
      (1+(3*storage^2-8*storage)/(3*storage-4)^2) storage := by
  have hid := hasDerivAt_id storage
  have h := hid.add ((hid.pow 2).div ((hid.const_mul 3).sub_const 4) hden)
  convert h using 1
  · funext p
    rfl
  · dsimp
    norm_num
    field_simp [hden]
    ring

theorem actual_required_scalar_gain_stationary_point_in_domain_is_unique (storage : ℝ)
    (hstorage : (4/3:ℝ) < storage) :
    (1+(3*storage^2-8*storage)/(3*storage-4)^2=0) ↔ storage=2 := by
  have hden : 3*storage-4≠0 := by linarith
  constructor
  · intro h
    have hm := congrArg (fun value : ℝ => value*(3*storage-4)^2) h
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hden)] at hm
    have hf : (3*storage-2)*(storage-2)=0 := by nlinarith
    rcases mul_eq_zero.mp hf with hf|hf
    · exfalso
      linarith
    · linarith
  · intro h
    norm_num [h]

theorem actual_required_scalar_gain_tends_to_positive_infinity_at_finite_domain_boundary :
    Tendsto actualScalarRequiredGainSquared (𝓝[>] (4/3:ℝ)) atTop := by
  apply tendsto_atTop.2
  intro bound
  have hpositive : 0 < 3*(|bound|+1) := by positivity
  have hupper : (4/3:ℝ) < 4/3+1/(3*(|bound|+1)) := by
    have hp : 0 < 1/(3*(|bound|+1)) := by positivity
    linarith
  have heventual : ∀ᶠ storage in 𝓝[>] (4/3:ℝ),storage < 4/3+1/(3*(|bound|+1)) :=
    (eventually_lt_nhds hupper).filter_mono inf_le_left
  have hlower : ∀ᶠ storage in 𝓝[>] (4/3:ℝ),(4/3:ℝ) < storage := self_mem_nhdsWithin
  filter_upwards [heventual,hlower] with storage hs hl
  have hdelta : storage-4/3 < 1/(3*(|bound|+1)) := by linarith
  have hmul := (lt_div_iff₀ hpositive).mp hdelta
  have hden : 0 < 3*storage-4 := by linarith
  have hnum : |bound| *(3*storage-4) < storage^2 := by nlinarith [abs_nonneg bound]
  have hquotient := (lt_div_iff₀ hden).mpr hnum
  unfold actualScalarRequiredGainSquared
  linarith [le_abs_self bound]

theorem actual_required_scalar_gain_tends_to_positive_infinity_at_infinity :
    Tendsto actualScalarRequiredGainSquared atTop atTop := by
  apply tendsto_atTop.2
  intro bound
  filter_upwards [eventually_ge_atTop (max bound (2:ℝ))] with storage hs
  have hden : 0 < 3*storage-4 := by linarith [le_max_right bound (2:ℝ)]
  have hnonnegative : 0 ≤ storage^2/(3*storage-4) := by positivity
  unfold actualScalarRequiredGainSquared
  linarith [le_max_left bound (2:ℝ)]

end SafeLearning.CompleteModulesScalarGainCalculus
