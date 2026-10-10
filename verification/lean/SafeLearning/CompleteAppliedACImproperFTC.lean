import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedACImproperFTC

theorem actual_locally_absolutely_continuous_ae_derivative_integral_reconstructs_every_value
    (value derivative : ℝ→ℝ)
    (hlocal : ∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval value 0 horizon)
    (hderivative : ∀ᵐtime ∂volume,time∈Ici (0:ℝ)→HasDerivAt value (derivative time) time)
    (time : ℝ) (htime : 0≤time) :
    (∫point in (0:ℝ)..time,derivative point)=value time-value 0 := by
  have he : (∫point in (0:ℝ)..time,derivative point)=
      (∫point in (0:ℝ)..time,deriv value point) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderivative] with point hd hp
    rw [uIoc_of_le htime] at hp
    exact (hd (show point∈Ici (0:ℝ) from hp.1.le)).deriv.symm
  rw [he,(hlocal time htime).integral_deriv_eq_sub]

theorem actual_locally_absolutely_continuous_integrable_function_and_ae_derivative_have_zero_limit
    (value derivative : ℝ→ℝ)
    (hlocal : ∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval value 0 horizon)
    (hderivative : ∀ᵐtime ∂volume,time∈Ici (0:ℝ)→HasDerivAt value (derivative time) time)
    (hdi : IntegrableOn derivative (Ioi (0:ℝ)))
    (hvi : IntegrableOn value (Ioi (0:ℝ))) :
    Tendsto value atTop (𝓝 0) ∧
      (∫time in Ioi (0:ℝ),derivative time)= -value 0 := by
  let limit : ℝ := value 0+(∫time in Ioi (0:ℝ),derivative time)
  have hi := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hdi tendsto_id
  have hv : Tendsto value atTop (𝓝 limit) := by
    apply (tendsto_const_nhds.add hi).congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with time ht
    have he := actual_locally_absolutely_continuous_ae_derivative_integral_reconstructs_every_value
      value derivative hlocal hderivative time ht
    change value 0+(∫point in (0:ℝ)..time,derivative point)=value time
    linarith
  have hzero : limit=0 := by
    have hfilter : IntegrableAtFilter value atTop := ⟨Ioi (0:ℝ),Ioi_mem_atTop _,hvi⟩
    apply hfilter.eq_zero_of_tendsto _ hv
    intro s hs
    rcases mem_atTop_sets.1 hs with ⟨bound,hbound⟩
    rw [←top_le_iff,←Real.volume_Ici (a:=bound)]
    exact measure_mono hbound
  refine ⟨hzero ▸ hv,?_⟩
  dsimp [limit] at hzero
  linarith

end SafeLearning.CompleteAppliedACImproperFTC
