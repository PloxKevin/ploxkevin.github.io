import SafeLearning.CompleteAppliedProbability
import SafeLearning.CompleteAppliedIndependenceDefinitions
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace SafeLearning.CompleteAppliedIndependencePitfalls
open CompleteAppliedProbability CompleteAppliedIndependenceDefinitions

theorem actual_sign_law_integrals_and_true_covariance_are_zero_as_printed :
    (∫ i,signValue i ∂uniformSigns.toMeasure)=0 ∧
    (∫ i,signSquared i ∂uniformSigns.toMeasure)=2/3 ∧
    (∫ i,(signValue i)^3 ∂uniformSigns.toMeasure)=0 ∧
    cov[signValue,signSquared;uniformSigns.toMeasure]=0 := by
  have h1 : (∫ i,signValue i ∂uniformSigns.toMeasure)=0 := by
    norm_num [PMF.integral_eq_sum,uniformSigns,signValue,Fin.sum_univ_succ]
  have h2 : (∫ i,signSquared i ∂uniformSigns.toMeasure)=2/3 := by
    norm_num [PMF.integral_eq_sum,uniformSigns,signValue,signSquared,Fin.sum_univ_succ]
  have h3 : (∫ i,(signValue i)^3 ∂uniformSigns.toMeasure)=0 := by
    norm_num [PMF.integral_eq_sum,uniformSigns,signValue,Fin.sum_univ_succ]
  refine ⟨h1,h2,h3,?_⟩
  unfold covariance
  rw [h1,h2]
  norm_num [PMF.integral_eq_sum,uniformSigns,signValue,signSquared,Fin.sum_univ_succ]

theorem actual_sign_and_its_square_are_not_independent_random_variables :
    ¬IndepFun signValue signSquared uniformSigns.toMeasure := by
  intro h
  have hh := (indepFun_iff_measure_inter_preimage_eq_mul.mp h)
    ({0}:Set ℝ) ({0}:Set ℝ) (measurableSet_singleton _) (measurableSet_singleton _)
  norm_num [PMF.toMeasure_apply_fintype,uniformSigns,signValue,signSquared,
    Fin.sum_univ_succ,Set.indicator] at hh
  have hhR := congrArg ENNReal.toReal hh
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv] at hhR

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem actual_general_positive_uniform_noise_has_the_literal_bias_and_hard_bound
    (X : Ω → ℝ) (sigma : ℝ) (hs : 0<sigma)
    (hu : pdf.IsUniform X (Icc 0 sigma) P) :
    (∀ᵐ ω ∂P,|X ω| ≤ sigma) ∧ (∫ω,X ω ∂P)=sigma/2 ∧ Integrable X P := by
  have hb : ∀ᵐ ω ∂P,X ω∈Icc 0 sigma := by
    apply (hu.ae_iff (measurableSet_setOfPred.mp measurableSet_Icc)).mpr
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  have hi : Integrable X P :=
    (memLp_of_bounded hb hu.aemeasurable.aestronglyMeasurable 2).integrable (by norm_num)
  have hm : (∫ω,X ω ∂P)=sigma/2 := by
    rw [hu.integral_eq,Real.volume_Icc]
    simp only [sub_zero,ENNReal.toReal_inv,ENNReal.toReal_ofReal hs.le]
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hs.le,integral_id]
    field_simp
    ring
  refine ⟨?_,hm,hi⟩
  filter_upwards [hb] with ω hω
  rw [abs_of_nonneg hω.1]
  exact hω.2

theorem actual_averaging_any_number_of_positive_uniform_samples_preserves_expected_bias
    (X : ℕ → Ω → ℝ) (sigma : ℝ) (hs : 0<sigma)
    (hu : ∀ i,pdf.IsUniform (X i) (Icc 0 sigma) P) (N : ℕ) (hN : 0<N) :
    (∫ω,(∑ i∈Finset.range N,X i ω)/(N:ℝ) ∂P)=sigma/2 := by
  have hi : ∀ i,Integrable (X i) P := fun i =>
    (actual_general_positive_uniform_noise_has_the_literal_bias_and_hard_bound (X i) sigma hs (hu i)).2.2
  rw [integral_div,integral_finsetSum _ (fun i _ => hi i)]
  have hm : ∀ i,(∫ω,X i ω ∂P)=sigma/2 := fun i =>
    (actual_general_positive_uniform_noise_has_the_literal_bias_and_hard_bound _ sigma hs (hu i)).2.1
  simp_rw [hm]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hn : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  field_simp [hn]

theorem actual_iid_uniform_sample_averages_converge_to_bias_and_not_zero
    (X : ℕ → Ω → ℝ) (sigma : ℝ) (hs : 0<sigma)
    (hu : ∀ i,pdf.IsUniform (X i) (Icc 0 sigma) P)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P)) :
    ∀ᵐ ω ∂P,Tendsto (fun n : ℕ => (∑ i∈Finset.range n,X i ω)/(n:ℝ)) atTop (𝓝 (sigma/2)) ∧
      ¬Tendsto (fun n : ℕ => (∑ i∈Finset.range n,X i ω)/(n:ℝ)) atTop (𝓝 (0:ℝ)) := by
  have hp := actual_general_positive_uniform_noise_has_the_literal_bias_and_hard_bound (X 0) sigma hs (hu 0)
  have hl := strong_law_ae_real X hp.2.2 hind (fun i => (hu i).identDistrib (hu 0))
  rw [hp.2.1] at hl
  filter_upwards [hl] with ω hω
  refine ⟨hω,?_⟩
  intro hz
  have he := tendsto_nhds_unique hω hz
  linarith

def episodeTrajectory (policy : ℝ → ℝ) (data : ℝ × (ℕ → ℝ)) : ℕ → ℝ
  | 0 => data.1
  | n+1 => episodeTrajectory policy data n+policy (episodeTrajectory policy data n)+data.2 n

theorem actual_fixed_controller_episode_trajectory_is_measurable
    (policy : ℝ → ℝ) (hp : Measurable policy) :
    Measurable (episodeTrajectory policy) := by
  apply measurable_pi_lambda
  intro n
  induction n with
  | zero => exact measurable_fst
  | succ n hn =>
    have hm := (hn.add (hp.comp hn)).add ((measurable_pi_apply n).comp measurable_snd)
    convert hm using 1
    ext c
    rfl

theorem actual_independently_drawn_initial_noise_data_give_independent_whole_fixed_controller_episodes
    (initialLaw : Measure ℝ) [IsProbabilityMeasure initialLaw] (noiseVariance : ℝ≥0)
    (policy : ℝ → ℝ) (hp : Measurable policy) :
    iIndepFun (fun episode : ℕ => fun sample : ℕ → ℝ × (ℕ → ℝ) =>
      episodeTrajectory policy (sample episode))
      (Measure.infinitePi (fun _ : ℕ => initialLaw.prod (actualGaussianNoiseLaw noiseVariance))) := by
  haveI : IsProbabilityMeasure (actualGaussianNoiseLaw noiseVariance) := by
    unfold actualGaussianNoiseLaw
    infer_instance
  exact iIndepFun_infinitePi (fun _ => actual_fixed_controller_episode_trajectory_is_measurable policy hp)

theorem actual_same_episode_states_share_noise_and_are_dependent_for_positive_gaussian_variance
    (variance : ℝ≥0) (hv : 0<variance) :
    cov[actualNoiseCoordinate 0,fun sample => actualNoiseCoordinate 0 sample+actualNoiseCoordinate 1 sample;
      actualGaussianNoiseLaw variance]=(variance:ℝ) ∧
    ¬IndepFun (actualNoiseCoordinate 0)
      (fun sample => actualNoiseCoordinate 0 sample+actualNoiseCoordinate 1 sample)
      (actualGaussianNoiseLaw variance) := by
  letI : IsProbabilityMeasure (actualGaussianNoiseLaw variance) := by
    unfold actualGaussianNoiseLaw
    infer_instance
  obtain ⟨hind,hlaw⟩ := actual_gaussian_noise_coordinates_are_mutually_independent_with_the_same_true_law variance
  have hm : ∀ n,MemLp (actualNoiseCoordinate n) 2 (actualGaussianNoiseLaw variance) := by
    intro n
    exact (hlaw n).memLp (memLp_id_gaussianReal 2)
  have hi : IndepFun (actualNoiseCoordinate 0) (actualNoiseCoordinate 1) (actualGaussianNoiseLaw variance) :=
    hind.indepFun (by norm_num)
  have hc : cov[actualNoiseCoordinate 0,fun sample => actualNoiseCoordinate 0 sample+actualNoiseCoordinate 1 sample;
      actualGaussianNoiseLaw variance]=(variance:ℝ) := by
    change cov[actualNoiseCoordinate 0,actualNoiseCoordinate 0+actualNoiseCoordinate 1;
      actualGaussianNoiseLaw variance]=(variance:ℝ)
    rw [covariance_add_right (hm 0) (hm 0) (hm 1),
      covariance_self (hlaw 0).aemeasurable,hi.covariance_eq_zero (hm 0) (hm 1),
      (hlaw 0).variance_eq,variance_id_gaussianReal,add_zero]
  refine ⟨hc,?_⟩
  intro h
  have hz := h.covariance_eq_zero (hm 0) ((hm 0).add (hm 1))
  rw [hc] at hz
  exact (ne_of_gt (show 0<(variance:ℝ) from hv)) hz

end SafeLearning.CompleteAppliedIndependencePitfalls
