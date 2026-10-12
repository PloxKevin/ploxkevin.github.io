import SafeLearning.CompleteAppliedScalarEnergyGain

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedScalarConvolutionOutput
open CompleteAppliedScalarEnergyBound CompleteAppliedACImproperFTC

def weightedInput (input : ℝ→ℝ) (time : ℝ) : ℝ :=
  Real.exp (2*time)*(Ioi (0:ℝ)).indicator input time

def actualOutput (input : ℝ→ℝ) (time : ℝ) : ℝ :=
  Real.exp (-2*time)*(∫point in (0:ℝ)..time,weightedInput input point)

theorem actual_square_integrable_input_has_locally_integrable_weighted_input
    (input : ℝ→ℝ) (hinput : MemLp input 2 (volume.restrict (Ioi (0:ℝ)))) :
    LocallyIntegrable (weightedInput input) volume := by
  have hi : MemLp ((Ioi (0:ℝ)).indicator input) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioi).mpr hinput
  exact LocallyIntegrable.continuous_mul (by fun_prop) (hi.locallyIntegrable (by norm_num))

theorem actual_convolution_output_exists_for_every_square_integrable_input
    (input : ℝ→ℝ) (hinput : MemLp input 2 (volume.restrict (Ioi (0:ℝ)))) :
    actualOutput input 0=0 ∧
      (∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval (actualOutput input) 0 horizon) ∧
      (∀ᵐtime ∂volume,time∈Ici (0:ℝ)→
        HasDerivAt (actualOutput input) (-2*actualOutput input time+input time) time) := by
  have hw := actual_square_integrable_input_has_locally_integrable_weighted_input input hinput
  refine ⟨by simp [actualOutput],?_,?_⟩
  · intro horizon hh
    have hi : IntervalIntegrable (weightedInput input) volume 0 horizon :=
      intervalIntegrable_iff.mpr ((hw.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
    have hac := hi.absolutelyContinuousOnInterval_intervalIntegral
      (show (0:ℝ)∈uIcc 0 horizon by rw [uIcc_of_le hh];exact ⟨le_rfl,hh⟩)
    have hexp : AbsolutelyContinuousOnInterval (fun time:ℝ=>Real.exp (-2*time)) 0 horizon :=
      ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
    apply (hexp.mul hac).congr
    intro time _
    rfl
  · have hd := _root_.LocallyIntegrable.ae_hasDerivAt_integral hw
    have hn : ∀ᵐtime:ℝ ∂volume,time≠0 := by simp [ae_iff,measure_singleton]
    filter_upwards [hd,hn] with time ht hn htime
    have hp : 0<time := lt_of_le_of_ne htime hn.symm
    have he : weightedInput input time=Real.exp (2*time)*input time := by
      simp [weightedInput,hp]
    have hexp := ((hasDerivAt_id time).const_mul (-2)).exp
    have hout := hexp.mul (ht 0)
    rw [he] at hout
    change HasDerivAt (fun point:ℝ=>Real.exp (-2*point)*(∫s in (0:ℝ)..point,weightedInput input s)) _ time
    convert hout using 1
    · rfl
    · simp only [id_eq,mul_one,actualOutput]
      have cancel : Real.exp (-2*time)*Real.exp (2*time)=1 := by rw [←Real.exp_add];simp
      have hc : Real.exp (-2*time)*(Real.exp (2*time)*input time)=input time := by
        rw [←mul_assoc,cancel,one_mul]
      rw [hc]
      ring

theorem actual_every_existing_ac_zero_initial_solution_equals_the_constructed_output
    (state input : ℝ→ℝ)
    (hinput : MemLp input 2 (volume.restrict (Ioi (0:ℝ))))
    (hlocal : ∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval state 0 horizon)
    (hode : ∀ᵐtime ∂volume,time∈Ici (0:ℝ)→HasDerivAt state (-2*state time+input time) time)
    (hinitial : state 0=0) :
    ∀time:ℝ,0≤time→state time=actualOutput input time := by
  have ho := actual_convolution_output_exists_for_every_square_integrable_input input hinput
  let difference : ℝ→ℝ := fun time=>(state time-actualOutput input time)*Real.exp (2*time)
  have hac : ∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval difference 0 horizon := by
    intro horizon hh
    have hexp : AbsolutelyContinuousOnInterval (fun time:ℝ=>Real.exp (2*time)) 0 horizon :=
      ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
    apply (((hlocal horizon hh).sub (ho.2.1 horizon hh)).mul hexp).congr
    intro time _
    rfl
  have hd : ∀ᵐtime ∂volume,time∈Ici (0:ℝ)→HasDerivAt difference 0 time := by
    filter_upwards [hode,ho.2.2] with time hs hu htime
    have he := ((hasDerivAt_id time).const_mul 2).exp
    have h := ((hs htime).sub (hu htime)).mul he
    change HasDerivAt ((state-actualOutput input)*(fun point:ℝ=>Real.exp (2*point))) 0 time
    convert h using 1
    · rfl
    · simp only [id_eq,Pi.sub_apply,mul_one]
      ring
  intro time ht
  have hint := actual_locally_absolutely_continuous_ae_derivative_integral_reconstructs_every_value
    difference (fun _:ℝ=>0) hac hd time ht
  have hzero : difference 0=0 := by simp [difference,hinitial,ho.1]
  simp only [intervalIntegral.integral_zero,hzero,sub_zero] at hint
  have hx : (state time-actualOutput input time)*Real.exp (2*time)=0 := hint.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right (Real.exp_pos _).ne')

theorem actual_L2_input_output_map_is_defined_unique_and_has_the_half_gain
    (input : ℝ→ℝ) (hinput : MemLp input 2 (volume.restrict (Ioi (0:ℝ)))) :
    (actualOutput input 0=0) ∧
    (∀horizon:ℝ,0≤horizon→AbsolutelyContinuousOnInterval (actualOutput input) 0 horizon) ∧
    (∀ᵐtime ∂volume,time∈Ici (0:ℝ)→HasDerivAt (actualOutput input)
      (-2*actualOutput input time+input time) time) ∧
    IntegrableOn (fun time=>actualOutput input time^2) (Ioi (0:ℝ)) ∧
    Real.sqrt (∫time in Ioi (0:ℝ),actualOutput input time^2)≤
      (1/2:ℝ)*Real.sqrt (∫time in Ioi (0:ℝ),input time^2) := by
  have ho := actual_convolution_output_exists_for_every_square_integrable_input input hinput
  have he := actual_every_square_integrable_input_has_a_square_integrable_output_and_half_energy_gain
    (actualOutput input) input ho.2.1 ho.2.2 ho.1 hinput
  exact ⟨ho.1,ho.2.1,ho.2.2,he.1,he.2.2⟩

end SafeLearning.CompleteAppliedScalarConvolutionOutput
