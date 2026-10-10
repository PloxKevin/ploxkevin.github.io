import SafeLearning.CompleteAppliedACImproperFTC

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedScalarEnergyBound

theorem actual_every_ac_zero_initial_trajectory_has_the_finite_energy_bound
    (state input : ℝ→ℝ)
    (hlocal : ∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval state 0 horizon)
    (hode : ∀ᵐtime ∂volume,time∈Ici (0:ℝ)→HasDerivAt state (-2*state time+input time) time)
    (hinitial : state 0=0)
    (hinput : MemLp input 2 (volume.restrict (Ioi (0:ℝ))))
    (horizon : ℝ) (hhorizon : 0≤horizon) :
    2*state horizon^2+4*(∫time in (0:ℝ)..horizon,state time^2)≤
      ∫time in (0:ℝ)..horizon,input time^2 := by
  have hs : AbsolutelyContinuousOnInterval (fun time=>2*state time^2) 0 horizon := by
    simpa only [pow_two,Pi.mul_apply] using
      AbsolutelyContinuousOnInterval.const_mul 2 ((hlocal horizon hhorizon).mul (hlocal horizon hhorizon))
  have hx : IntervalIntegrable (fun time=>state time^2) volume 0 horizon := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hhorizon,Pi.pow_apply] using (hlocal horizon hhorizon).continuousOn.fun_pow 2
  have hu : IntervalIntegrable (fun time=>input time^2) volume 0 horizon :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hhorizon).mpr
      ((show IntegrableOn (fun time=>input time^2) (Ioi (0:ℝ)) volume from hinput.integrable_sq).mono_set Ioc_subset_Ioi_self)
  have hd : (deriv (fun time=>2*state time^2))≤ᵐ[volume.restrict (Icc (0:ℝ) horizon)]
      (fun time=>input time^2-4*state time^2) := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hode] with time ht htime
    have hderiv : HasDerivAt (fun point=>2*state point^2)
        (4*state time*(-2*state time+input time)) time := by
      convert ((ht htime.1).pow 2).const_mul 2 using 1 <;> ring
    rw [hderiv.deriv]
    nlinarith [sq_nonneg (input time-2*state time)]
  have hbound := intervalIntegral.integral_mono_ae_restrict hhorizon
    hs.intervalIntegrable_deriv (hu.sub (hx.const_mul 4)) hd
  rw [hs.integral_deriv_eq_sub,hinitial,intervalIntegral.integral_sub hu (hx.const_mul 4),
    intervalIntegral.integral_const_mul] at hbound
  norm_num at hbound
  linarith

theorem actual_every_square_integrable_input_has_a_square_integrable_output_and_half_energy_gain
    (state input : ℝ→ℝ)
    (hlocal : ∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval state 0 horizon)
    (hode : ∀ᵐtime ∂volume,time∈Ici (0:ℝ)→HasDerivAt state (-2*state time+input time) time)
    (hinitial : state 0=0)
    (hinput : MemLp input 2 (volume.restrict (Ioi (0:ℝ)))) :
    IntegrableOn (fun time=>state time^2) (Ioi (0:ℝ)) ∧
      (∫time in Ioi (0:ℝ),state time^2)≤(1/4:ℝ)*(∫time in Ioi (0:ℝ),input time^2) ∧
      Real.sqrt (∫time in Ioi (0:ℝ),state time^2)≤
        (1/2:ℝ)*Real.sqrt (∫time in Ioi (0:ℝ),input time^2) := by
  have hinputBound (horizon : ℝ) (hhorizon : 0≤horizon) :
      (∫time in (0:ℝ)..horizon,input time^2)≤∫time in Ioi (0:ℝ),input time^2 := by
    rw [intervalIntegral.integral_of_le hhorizon]
    apply setIntegral_mono_set hinput.integrable_sq
      (Filter.Eventually.of_forall (fun time=>sq_nonneg (input time)))
    exact Filter.Eventually.of_forall (fun _ htime=>htime.1)
  have hprefix (horizon : ℝ) (hhorizon : 0≤horizon) :
      (∫time in (0:ℝ)..horizon,state time^2)≤
        (1/4:ℝ)*(∫time in Ioi (0:ℝ),input time^2) := by
    have h := actual_every_ac_zero_initial_trajectory_has_the_finite_energy_bound
      state input hlocal hode hinitial hinput horizon hhorizon
    have hu := hinputBound horizon hhorizon
    nlinarith [sq_nonneg (state horizon)]
  have hfinite (horizon : ℝ) : IntegrableOn (fun time=>state time^2) (Ioc (0:ℝ) horizon) := by
    by_cases hhorizon : 0≤horizon
    · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hhorizon).mp
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le hhorizon,Pi.pow_apply] using (hlocal horizon hhorizon).continuousOn.fun_pow 2
    · have he : Ioc (0:ℝ) horizon=∅ := Ioc_eq_empty_of_le (le_of_not_ge hhorizon)
      simp [he]
  have hsi : IntegrableOn (fun time=>state time^2) (Ioi (0:ℝ)) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded
      ((1/4:ℝ)*(∫time in Ioi (0:ℝ),input time^2)) 0 hfinite tendsto_id
    filter_upwards [eventually_ge_atTop (0:ℝ)] with horizon hhorizon
    have habs : ∀time:ℝ,|state time^2|=state time^2 := fun time=>abs_of_nonneg (sq_nonneg (state time))
    simpa only [Real.norm_eq_abs,habs] using hprefix horizon hhorizon
  have hlim := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hsi tendsto_id
  have henergy := le_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with horizon hhorizon
    exact hprefix horizon hhorizon)
  refine ⟨hsi,henergy,?_⟩
  have ho : 0≤∫time in Ioi (0:ℝ),state time^2 := integral_nonneg (fun _=>sq_nonneg _)
  have hi : 0≤∫time in Ioi (0:ℝ),input time^2 := integral_nonneg (fun _=>sq_nonneg _)
  have hso := Real.sq_sqrt ho
  have hsu := Real.sq_sqrt hi
  nlinarith [Real.sqrt_nonneg (∫time in Ioi (0:ℝ),state time^2),
    Real.sqrt_nonneg (∫time in Ioi (0:ℝ),input time^2)]

end SafeLearning.CompleteAppliedScalarEnergyBound
