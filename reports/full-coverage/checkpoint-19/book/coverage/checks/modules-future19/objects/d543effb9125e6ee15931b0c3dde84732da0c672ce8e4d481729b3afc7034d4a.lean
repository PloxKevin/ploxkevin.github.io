import SafeLearning.CompleteModulesLoSBOGaussianNoise
import SafeLearning.CompleteModulesLoSBOGaussianHorizon
import SafeLearning.CompleteModulesMatrixGP
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology NNReal ENNReal
namespace SafeLearning.CompleteModulesGPGaussianCoverageFailure
open CompleteModulesMatrixGP CompleteModulesLoSBOGaussianNoise
open CompleteAppliedGaussianCDF

def originalWidth (R delta lambda c : ℝ) : ℝ :=
  R*Real.sqrt (Real.log (1+c)-2*Real.log delta)*Real.sqrt (c*lambda/(1+lambda))

def actualCoverage (R : ℝ≥0) (delta lambda c : ℝ) : ℝ :=
  (gaussianReal 0 (R^2)).real {epsilon | |epsilon/(1+lambda)| ≤ originalWidth R delta lambda c}

theorem actual_one_observation_mean_and_variance_are_the_printed_formulas
    (lambda c epsilon : ℝ) (hlambda : 0 < lambda) (hc : 0 < c) :
    posteriorMean (fun _ _ : Fin 1 => c) (fun _ => c) (fun _ => epsilon) (c*lambda)=
      epsilon/(1+lambda) ∧
    posteriorVariance (fun _ _ : Fin 1 => c) (fun _ => c) c (c*lambda)=
      c*lambda/(1+lambda) := by
  have hd : c+c*lambda ≠ 0 := by positivity
  have he : 1+lambda ≠ 0 := by positivity
  constructor <;>
    simp [posteriorMean,posteriorVariance,ridgeMatrix,Matrix.inv_subsingleton,
      Ring.inverse_eq_inv',Matrix.mulVec,dotProduct,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,
      CStarMatrix.add_apply,CStarMatrix.smul_apply,CStarMatrix.one_apply,
      Pi.add_apply,Pi.smul_apply,Pi.one_apply]
  · field_simp
    <;> ring
  · field_simp
    <;> ring

theorem actual_gaussian_coverage_of_zero_is_the_true_two_sided_cdf
    (R : ℝ≥0) (hR : R ≠ 0) (lambda w : ℝ) (hlambda : 0 < lambda) (hw : 0 ≤ w) :
    (gaussianReal 0 (R^2)).real {epsilon | |epsilon/(1+lambda)| ≤ w}=
      2*standardCDF ((1+lambda)*w/(R:ℝ))-1 := by
  have hd : 0 < 1+lambda := by positivity
  have he : {epsilon : ℝ | |epsilon/(1+lambda)| ≤ w}=
      actualBoundEvent ((1+lambda)*w) := by
    ext epsilon
    simp only [mem_setOf_eq,actualBoundEvent,abs_div,abs_of_pos hd]
    rw [div_le_iff₀ hd]
    rw [mul_comm w]
  rw [he]
  exact actual_source_gaussian_interval_probability_is_the_scaled_two_sided_cdf
    _ (mul_nonneg hd.le hw) R hR

theorem actual_gaussian_noise_in_this_counterexample_is_subgaussian
    (R : ℝ≥0) : HasSubgaussianMGF id (R^2) (gaussianReal 0 (R^2)) :=
  CompleteModulesLoSBOGaussianHorizon.actual_centered_gaussian_law_has_its_genuine_subgaussian_mgf
    _ id _ ⟨measurable_id.aemeasurable,by simp⟩

theorem actual_original_counterexample_half_width_tends_to_zero
    (R delta lambda : ℝ) :
    Tendsto (originalWidth R delta lambda) (𝓝 0) (𝓝 0) := by
  have hi : Tendsto (fun c : ℝ => 1+c) (𝓝 0) (𝓝 1) := by
    simpa using (tendsto_id : Tendsto (fun c : ℝ => c) (𝓝 0) (𝓝 0)).const_add 1
  have hl : Tendsto (fun c : ℝ => Real.log (1+c)) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def,Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hi
  have hfirst := (hl.sub (tendsto_const_nhds (x:=2*Real.log delta))).sqrt.const_mul R
  have hsecond : Tendsto (fun c : ℝ => Real.sqrt (c*lambda/(1+lambda))) (𝓝 0) (𝓝 0) := by
    simpa using (((tendsto_id : Tendsto (fun c : ℝ => c) (𝓝 0) (𝓝 0)).mul_const lambda).div_const
      (1+lambda)).sqrt
  convert hfirst.mul hsecond using 1 <;> first | rfl | simp [originalWidth]

theorem actual_original_counterexample_coverage_probability_tends_to_zero
    (R : ℝ≥0) (hR : R ≠ 0) (delta lambda : ℝ) (hlambda : 0 < lambda) :
    Tendsto (actualCoverage R delta lambda) (𝓝 0) (𝓝 0) := by
  have hRpos : 0 < (R:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hR)
  have he : actualCoverage R delta lambda =
      (fun c => 2*standardCDF ((1+lambda)*originalWidth R delta lambda c/(R:ℝ))-1) := by
    funext c
    exact actual_gaussian_coverage_of_zero_is_the_true_two_sided_cdf R hR lambda _ hlambda
      (mul_nonneg (mul_nonneg hRpos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  rw [he]
  have hz : Tendsto (fun c => (1+lambda)*originalWidth R delta lambda c/(R:ℝ))
      (𝓝 0) (𝓝 0) := by
    simpa using ((actual_original_counterexample_half_width_tends_to_zero R delta lambda).const_mul
      (1+lambda)).div_const (R:ℝ)
  have hc := CompleteAppliedGaussianQuantile.actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.1
  have hp := (hc.continuousAt.tendsto.comp hz).const_mul 2
  simpa [actual_standard_gaussian_symmetry_and_half_mass] using hp.sub_const 1

theorem actual_valid_small_scaled_regularizer_has_coverage_below_the_claimed_level
    (R : ℝ≥0) (hR : R ≠ 0) (delta lambda : ℝ)
    (hd : 0 < delta) (hd1 : delta < 1) (hlambda : 0 < lambda) :
    ∃ c : ℝ, 0 < c ∧ c*lambda ≤ 1 ∧ actualCoverage R delta lambda c < 1-delta := by
  have he := (actual_original_counterexample_coverage_probability_tends_to_zero
    R hR delta lambda hlambda).eventually (gt_mem_nhds (by linarith : (0:ℝ)<1-delta))
  obtain ⟨epsilon,hepsilon,he⟩ := Metric.eventually_nhds_iff.mp he
  let c := min (epsilon/2) (1/(2*lambda))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c,hc,?_,he ?_⟩
  · have hb : c ≤ 1/(2*lambda) := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_right hb hlambda.le
    have hh : (1/(2*lambda))*lambda=(1/2:ℝ) := by field_simp
    rw [hh] at hm
    linarith
  · rw [Real.dist_eq,sub_zero,abs_of_pos hc]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

end SafeLearning.CompleteModulesGPGaussianCoverageFailure
