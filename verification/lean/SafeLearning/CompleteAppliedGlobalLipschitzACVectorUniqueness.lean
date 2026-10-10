import SafeLearning.CompleteAppliedGlobalLipschitzPicard

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedGlobalLipschitzACVectorUniqueness
open SafeLearning.CompleteAppliedGlobalLipschitzPicard

variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem actual_ac_a_e_autonomous_solution_has_the_true_integral_equation
    (field:E→E) (K:ℝ≥0) (hf:LipschitzWith K field)
    (x:ℝ→E) (T:ℝ) (hT:0≤T)
    (hc:AbsolutelyContinuousOnInterval x 0 T)
    (hd:∀ᵐ t ∂volume,t∈Icc 0 T → HasDerivAt x (field (x t)) t)
    (t:ℝ) (ht:t∈Icc 0 T) :
    x t=x 0+∫ s in (0:ℝ)..t,field (x s) := by
  have hct : AbsolutelyContinuousOnInterval x 0 t := hc.mono (by
    rw [uIcc_of_le ht.1,uIcc_of_le hT]
    exact Icc_subset_Icc_right ht.2)
  have hcx : ContinuousOn x (Icc 0 t) := by simpa only [uIcc_of_le ht.1] using hct.continuousOn
  have hfi : IntervalIntegrable (fun s=>field (x s)) volume 0 t :=
    (hf.continuous.comp_continuousOn hcx).intervalIntegrable_of_Icc ht.1
  apply (SeparatingDual.eq_iff_forall_dual_eq (R:=ℝ)).mpr
  intro L
  have hL : AbsolutelyContinuousOnInterval (fun s=>L (x s)) 0 t :=
    L.lipschitz.comp_absolutelyContinuousOnInterval hct
  have he : (∫ s in (0:ℝ)..t,deriv (fun s=>L (x s)) s)=
      (∫ s in (0:ℝ)..t,L (field (x s))) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with s hs hst
    rw [uIoc_of_le ht.1] at hst
    exact ((L.hasFDerivAt).comp_hasDerivAt s (hs ⟨hst.1.le,hst.2.trans ht.2⟩)).deriv
  have hi:=hL.integral_deriv_eq_sub
  rw [he,L.intervalIntegral_comp_comm hfi] at hi
  rw [map_add]
  exact (eq_add_of_sub_eq hi.symm).trans (add_comm _ _)

theorem actual_ac_a_e_solution_has_the_true_right_ode_at_every_time
    (field:E→E) (K:ℝ≥0) (hf:LipschitzWith K field)
    (x:ℝ→E) (T:ℝ) (hT:0≤T)
    (hc:AbsolutelyContinuousOnInterval x 0 T)
    (hd:∀ᵐ t ∂volume,t∈Icc 0 T → HasDerivAt x (field (x t)) t)
    (t:ℝ) (ht:t∈Ico 0 T) :
    HasDerivWithinAt x (field (x t)) (Ici t) t := by
  have hcx : ContinuousOn x (Icc 0 T) := by simpa only [uIcc_of_le hT] using hc.continuousOn
  let origin:Icc (0:ℝ) T:=⟨0,⟨le_rfl,hT⟩⟩
  let path:C(Icc (0:ℝ) T,E):=⟨fun s=>x s.1,hcx.domRestrict⟩
  let extension : ℝ→E := extendPath origin path
  have hec:Continuous extension:=extendPath_continuous origin path
  have heq (s:ℝ) (hs:s∈Icc 0 T) : extension s=x s := by
    exact extendPath_of_mem origin path s hs
  have hfc:Continuous (fun s=>field (extension s)):=hf.continuous.comp hec
  have hi : HasDerivAt (fun s=>x 0+∫ u in (0:ℝ)..s,field (extension u))
      (field (x t)) t := by
    rw [←heq t ⟨ht.1,ht.2.le⟩]
    exact (intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable 0 t)
      hfc.stronglyMeasurable.stronglyMeasurableAtFilter hfc.continuousAt).const_add (x 0)
  have hEq (s:ℝ) (hs:s∈Icc 0 T) :
      x s=x 0+∫ u in (0:ℝ)..s,field (extension u) := by
    rw [actual_ac_a_e_autonomous_solution_has_the_true_integral_equation field K hf x T hT hc hd s hs]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs.1] at hu
    change field (x u)=field (extension u)
    rw [heq u ⟨hu.1,hu.2.trans hs.2⟩]
  apply hi.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds] with s hs hsT
    exact hEq s ⟨ht.1.trans hs,hsT.le⟩
  · exact hEq t ⟨ht.1,ht.2.le⟩

theorem actual_globally_lipschitz_vector_field_has_unique_existing_ac_a_e_solutions
    (field:E→E) (K:ℝ≥0) (hf:LipschitzWith K field)
    (x y:ℝ→E) (T:ℝ) (hT:0≤T)
    (hxc:AbsolutelyContinuousOnInterval x 0 T)
    (hyc:AbsolutelyContinuousOnInterval y 0 T)
    (hxd:∀ᵐ t ∂volume,t∈Icc 0 T → HasDerivAt x (field (x t)) t)
    (hyd:∀ᵐ t ∂volume,t∈Icc 0 T → HasDerivAt y (field (y t)) t)
    (hzero:x 0=y 0) : EqOn x y (Icc 0 T) := by
  exact ODE_solution_unique_of_mem_Icc_right (K:=K) (v:=fun _=>field) (s:=fun _=>univ)
    (fun _ _=>hf.lipschitzOnWith) (by simpa only [uIcc_of_le hT] using hxc.continuousOn)
    (fun t ht=>actual_ac_a_e_solution_has_the_true_right_ode_at_every_time field K hf x T hT hxc hxd t ht)
    (fun _ _=>mem_univ _) (by simpa only [uIcc_of_le hT] using hyc.continuousOn)
    (fun t ht=>actual_ac_a_e_solution_has_the_true_right_ode_at_every_time field K hf y T hT hyc hyd t ht)
    (fun _ _=>mem_univ _) hzero

end SafeLearning.CompleteAppliedGlobalLipschitzACVectorUniqueness
