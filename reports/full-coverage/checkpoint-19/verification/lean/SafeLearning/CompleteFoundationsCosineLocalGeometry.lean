import SafeLearning.CompleteFoundationsCosineIterates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace SafeLearning.CompleteFoundationsCosineLocalGeometry
open Set
open SafeLearning.CompleteFoundationsCosineContraction
open SafeLearning.CompleteFoundationsCosineNumerics
open SafeLearning.CompleteFoundationsCosineIterates

theorem actual_ordered_mean_value_witness (x y : ℝ) (hx : x∈sourceInterval)
    (hy : y∈sourceInterval) (hxy : x<y) :
    ∃ c∈sourceInterval,|Real.cos x-Real.cos y|=|Real.sin c| *|x-y| := by
  obtain ⟨c,hc,hd⟩ := exists_deriv_eq_slope Real.cos hxy
    Real.continuous_cos.continuousOn Real.differentiable_cos.differentiableOn
  rw [(Real.hasDerivAt_cos c).deriv] at hd
  have hm := (eq_div_iff (sub_ne_zero.mpr hxy.ne')).mp hd
  have ha := congrArg abs hm
  rw [abs_mul,abs_neg] at ha
  refine ⟨c,⟨hx.1.trans hc.1.le,hc.2.le.trans hy.2⟩,?_⟩
  rw [abs_sub_comm x y,abs_sub_comm (Real.cos x) (Real.cos y)]
  exact ha.symm

theorem actual_mean_value_witness_including_identical_points (x y : ℝ)
    (hx : x∈sourceInterval) (hy : y∈sourceInterval) :
    ∃ c∈sourceInterval,|Real.cos x-Real.cos y|=|Real.sin c| *|x-y| ∧
      |Real.sin c| *|x-y|≤Real.sin 1*|x-y| := by
  have hex : ∃ c∈sourceInterval,|Real.cos x-Real.cos y|=|Real.sin c| *|x-y| := by
    rcases lt_trichotomy x y with hxy|he|hyx
    · exact actual_ordered_mean_value_witness x y hx hy hxy
    · exact ⟨x,hx,by simp [he]⟩
    · obtain ⟨c,hc,hd⟩ := actual_ordered_mean_value_witness y x hy hx hyx
      exact ⟨c,hc,by simpa [abs_sub_comm] using hd⟩
  obtain ⟨c,hc,hd⟩ := hex
  refine ⟨c,hc,hd,mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)⟩
  have hb := actual_interval_derivative_bound c hc
  have hbr := NNReal.coe_le_coe.mp hb
  change ‖-Real.sin c‖≤Real.sin 1 at hbr
  simpa only [norm_neg,Real.norm_eq_abs] using hbr

theorem actual_fixed_point_sine_certified_enclosure :
    (67361202/100000000:ℝ)<Real.sin (sourceFixedPoint:ℝ) ∧
      Real.sin (sourceFixedPoint:ℝ)<67361204/100000000 := by
  have hf := actual_fixed_point_certified_enclosure
  have hl := abs_le.mp (actual_real_sine_degree_thirteen_remainder (7390851331/10000000000) (by norm_num))
  have hu := abs_le.mp (actual_real_sine_degree_thirteen_remainder (7390851333/10000000000) (by norm_num))
  have hsl := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_gt_three] : -(Real.pi/2)≤(7390851331/10000000000:ℝ))
    (sourceFixedPoint.prop.2.trans (by linarith [Real.pi_gt_three])) hf.1.le
  have hsu := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hf.1,Real.pi_gt_three] : -(Real.pi/2)≤(sourceFixedPoint:ℝ))
    (by linarith [Real.pi_gt_three] : (7390851333/10000000000:ℝ)≤Real.pi/2) hf.2.le
  norm_num [sinPoly] at hl hu
  constructor <;> linarith [hl.1,hu.2]

theorem actual_source_image_endpoints_constant_and_initial_gap_roundings :
    |Real.cos 1-(5403/10000:ℝ)|<1/20000 ∧
      |Real.cos (Real.cos 1)-(8576/10000:ℝ)|<1/20000 ∧
      |Real.sin 1-(8415/10000:ℝ)|<1/20000 ∧
      |(1-Real.sin 1)-(1585/10000:ℝ)|<1/20000 ∧
      |(1-Real.cos 1)-(4597/10000:ℝ)|<1/20000 ∧
      |Real.sin (sourceFixedPoint:ℝ)-(674/1000:ℝ)|<1/2000 ∧
      |(|1-(sourceFixedPoint:ℝ)|)-(261/1000:ℝ)|<1/2000 := by
  have h := actual_sine_one_and_cosine_one_certified_enclosures
  have h2 := actual_source_first_thirty_two_iterations_enclosed 2 (by omega)
  have hf := actual_fixed_point_certified_enclosure
  have hs := actual_fixed_point_sine_certified_enclosure
  norm_num [lowerBound,upperBound,sourceTable] at h2
  have hf1 : 0≤1-(sourceFixedPoint:ℝ) := by linarith [hf.2]
  rw [abs_of_nonneg hf1]
  constructor
  · rw [abs_lt];constructor <;> linarith [h.2.2.1,h.2.2.2]
  constructor
  · rw [abs_lt];constructor <;> linarith [h2.1,h2.2]
  constructor
  · rw [abs_lt];constructor <;> linarith [h.1,h.2.1]
  constructor
  · rw [abs_lt];constructor <;> linarith [h.1,h.2.1]
  constructor
  · rw [abs_lt];constructor <;> linarith [h.2.2.1,h.2.2.2]
  constructor
  · rw [abs_lt];constructor <;> linarith [hs.1,hs.2]
  · rw [abs_lt];constructor <;> linarith [hf.1,hf.2]

theorem actual_printed_cosine_decimal_equalities_are_false :
    Real.cos 1≠(5403/10000:ℝ) ∧ Real.sin 1≠(8415/10000:ℝ) ∧
      (sourceFixedPoint:ℝ)≠(739085/1000000:ℝ) := by
  have h := actual_sine_one_and_cosine_one_certified_enclosures
  have hf := actual_fixed_point_certified_enclosure
  constructor
  · intro he;rw [he] at h;norm_num at h
  constructor
  · intro he;rw [he] at h;norm_num at h
  · intro he;rw [he] at hf;norm_num at hf

end SafeLearning.CompleteFoundationsCosineLocalGeometry
