import SafeLearning.CompleteModulesTanhRefinement
import SafeLearning.CompleteModulesTanhSharpBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesTanhFTCRefinement
open CompleteModulesTheory CompleteModulesTanhChords CompleteModulesTanhSharpBounds
open CompleteModulesTanhRefinement CompleteModulesDiagonalQC CompleteModulesLipSDP

theorem actual_tanh_is_the_integral_of_its_literal_derivative (radius : ℝ) :
    (∫ point in (0:ℝ)..radius, 1-(Real.tanh point)^2) = Real.tanh radius := by
  have hc : Continuous (fun point : ℝ => 1-(Real.tanh point)^2) :=
    continuous_const.sub (tanh_lipschitz.continuous.pow 2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun point _ => (actual_tanh_has_the_literal_strictly_positive_bounded_derivative point).1)
    (hc.intervalIntegrable (0:ℝ) radius)
  simpa only [Real.tanh_zero,sub_zero] using h

theorem actual_origin_sector_ratio_is_the_printed_derivative_integral_mean
    (radius : ℝ) (hr : 0 < radius) :
    Real.tanh radius/radius = (1/radius)*(∫ point in (0:ℝ)..radius, deriv Real.tanh point) := by
  have he : deriv Real.tanh = fun point : ℝ => 1-(Real.tanh point)^2 := by
    funext point
    exact (actual_tanh_has_the_literal_strictly_positive_bounded_derivative point).1.deriv
  rw [he,actual_tanh_is_the_integral_of_its_literal_derivative]
  ring

theorem actual_strictly_larger_lower_slope_strictly_shrinks_the_qc_abstraction
    (small large : ℝ) (hs : 0 ≤ small) (hgap : small < large) (hu : large ≤ 1) :
    actualAllowedQCPairs large ⊆ actualAllowedQCPairs small ∧
      (1,small) ∈ actualAllowedQCPairs small ∧
      (1,small) ∉ actualAllowedQCPairs large := by
  have hsmall : small < 1 := hgap.trans_le hu
  refine ⟨?_,?_,?_⟩
  · intro pair hp
    obtain ⟨slope,hlower,hupper,he⟩ :=
      (scalar_qc_iff_admissible_chord large 1 pair.1 pair.2 hu).mp hp
    apply (scalar_qc_iff_admissible_chord small 1 pair.1 pair.2 hsmall.le).mpr
    exact ⟨slope,hgap.le.trans hlower,hupper,he⟩
  · simp [actualAllowedQCPairs,scalarQC]; ring_nf; simp
  · simp only [actualAllowedQCPairs,Set.mem_ofPred_eq,scalarQC]
    have hpos : 0 < (large-small)*(1-small) := mul_pos (sub_pos.mpr hgap) (sub_pos.mpr hsmall)
    nlinarith

theorem actual_local_derivative_bound_admits_a_pair_excluded_by_the_origin_sector
    (radius : ℝ) (hr : 0 < radius) :
    actualAllowedQCPairs (Real.tanh radius/radius) ⊆
      actualAllowedQCPairs (1-(Real.tanh radius)^2) ∧
    (1,1-(Real.tanh radius)^2) ∈ actualAllowedQCPairs (1-(Real.tanh radius)^2) ∧
    (1,1-(Real.tanh radius)^2) ∉ actualAllowedQCPairs (Real.tanh radius/radius) := by
  have h := actual_origin_ratio_is_strictly_between_the_endpoint_derivative_and_one radius hr
  exact actual_strictly_larger_lower_slope_strictly_shrinks_the_qc_abstraction
    (1-(Real.tanh radius)^2) (Real.tanh radius/radius)
    (actual_tanh_has_the_literal_strictly_positive_bounded_derivative radius).2.1.le h.1 h.2.le

end SafeLearning.CompleteModulesTanhFTCRefinement
