import SafeLearning.CompleteModulesGPRepeatedBayes
import SafeLearning.CompleteAppliedGaussianBayesJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SafeLearning.CompleteModulesGPRepeatedJoint

def Readings : ℕ → Type
  | 0 => Unit
  | n+1 => Readings n × ℝ
instance readingsMeasurable : (n : ℕ) → MeasurableSpace (Readings n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n+1 => @Prod.instMeasurableSpace (Readings n) ℝ (readingsMeasurable n) inferInstance

def readingVolume : (n : ℕ) → Measure (Readings n)
  | 0 => Measure.dirac ()
  | n+1 => (readingVolume n).prod volume
instance readingVolume_sfinite (n : ℕ) : SFinite (readingVolume n) := by
  induction n with
  | zero => change SFinite (Measure.dirac ()); infer_instance
  | succ n ih => letI := ih; change SFinite ((readingVolume n).prod volume); infer_instance

def sourceKernel : (n : ℕ) → Kernel ℝ (Readings n)
  | 0 => Kernel.const ℝ (Measure.dirac ())
  | n+1 => (sourceKernel n).prod (CompleteAppliedGaussianBayesJoint.observationKernel 1)
instance sourceKernel_markov (n : ℕ) : IsMarkovKernel (sourceKernel n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.const ℝ (Measure.dirac ())); infer_instance
  | succ n ih => letI := ih; change IsMarkovKernel ((sourceKernel n).prod _); infer_instance

def readingSum : (n : ℕ) → Readings n → ℝ
  | 0, _ => 0
  | n+1, y => readingSum n y.1 + y.2
def readingMean (n : ℕ) (y : Readings n) : ℝ := readingSum n y / ((n : ℝ)+1)
def readingVariance (n : ℕ) : ℝ≥0 := CompleteModulesGPRepeatedBayes.prefixVariance n
def likelihood : (n : ℕ) → Readings n → ℝ → ℝ≥0∞
  | 0, _, _ => 1
  | n+1, y, latent => likelihood n y.1 latent * gaussianPDF latent 1 y.2
def evidence : (n : ℕ) → Readings n → ℝ≥0∞
  | 0, _ => 1
  | n+1, y => evidence n y.1 * CompleteAppliedGaussianBayesGeneral.evidence
      (readingMean n y.1) y.2 (readingVariance n) 1

lemma readingSum_measurable (n : ℕ) : Measurable (readingSum n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).add measurable_snd
lemma readingMean_measurable (n : ℕ) : Measurable (readingMean n) :=
  (readingSum_measurable n).div_const _
lemma likelihood_measurable (n : ℕ) :
    Measurable (fun pair : ℝ × Readings n => likelihood n pair.2 pair.1) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun pair : ℝ × (Readings n × ℝ) =>
      likelihood n pair.2.1 pair.1 * gaussianPDF pair.1 1 pair.2.2)
    exact (ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (by fun_prop)
lemma evidence_measurable (n : ℕ) : Measurable (evidence n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun y : Readings n × ℝ => evidence n y.1 *
      CompleteAppliedGaussianBayesGeneral.evidence (readingMean n y.1) y.2 (readingVariance n) 1)
    apply (ih.comp measurable_fst).mul
    unfold CompleteAppliedGaussianBayesGeneral.evidence
    have hm := (readingMean_measurable n).comp measurable_fst
    fun_prop
lemma likelihood_ne_top (n : ℕ) (y : Readings n) (latent : ℝ) : likelihood n y latent ≠ ⊤ := by
  induction n with
  | zero => simp [likelihood]
  | succ n ih => exact ENNReal.mul_ne_top (ih y.1) gaussianPDF_ne_top

def posteriorKernel (n : ℕ) : Kernel (Readings n) ℝ :=
  ⟨fun y => gaussianReal (readingMean n y) (readingVariance n), by
    have hm := readingMean_measurable n
    fun_prop⟩
instance posteriorKernel_markov (n : ℕ) : IsMarkovKernel (posteriorKernel n) :=
  ⟨fun _ => by change IsProbabilityMeasure (gaussianReal _ _); infer_instance⟩
def dataLaw (n : ℕ) : Measure (Readings n) := (readingVolume n).withDensity (evidence n)
instance dataLaw_sfinite (n : ℕ) : SFinite (dataLaw n) := by unfold dataLaw; infer_instance
def fullJoint (n : ℕ) : Measure (ℝ × Readings n) := gaussianReal 0 1 ⊗ₘ sourceKernel n
instance fullJoint_probability (n : ℕ) : IsProbabilityMeasure (fullJoint n) := by
  unfold fullJoint; infer_instance

theorem actual_any_finite_number_of_conditionally_independent_readings_has_the_true_product_density
    (n : ℕ) : sourceKernel n = (Kernel.const ℝ (readingVolume n)).withDensity
      (fun latent y => likelihood n y latent) := by
  induction n with
  | zero =>
    ext latent event hevent
    rw [Kernel.withDensity_apply' _ (likelihood_measurable 0), Kernel.const_apply]
    simp [sourceKernel, readingVolume, likelihood]
  | succ n ih =>
    ext latent event hevent
    rw [Kernel.withDensity_apply' _ (likelihood_measurable (n+1)), Kernel.const_apply]
    change ((sourceKernel n latent).prod (gaussianReal latent 1)) event = _
    rw [ih, Kernel.withDensity_apply _ (likelihood_measurable n), Kernel.const_apply,
      gaussianReal_of_var_ne_zero _ (by norm_num)]
    have hm : Measurable (likelihood n · latent) :=
      (likelihood_measurable n).comp (measurable_const.prodMk measurable_id)
    rw [prod_withDensity hm (by fun_prop), withDensity_apply _ hevent]
    rfl

theorem actual_repeated_reading_mean_and_variance_are_the_genuine_recursive_bayes_parameters
    (n : ℕ) (y : Readings (n+1)) :
    CompleteAppliedGaussianBayesGeneral.posteriorMean (readingMean n y.1) y.2 (readingVariance n) 1 =
      readingMean (n+1) y ∧
    CompleteAppliedGaussianBayesGeneral.posteriorVariance (readingVariance n) 1 = readingVariance (n+1) := by
  constructor
  · simp only [CompleteAppliedGaussianBayesGeneral.posteriorMean, readingMean, readingSum,
      readingVariance, CompleteModulesGPRepeatedBayes.prefixVariance,
      NNReal.coe_add, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  · exact (CompleteModulesGPRepeatedBayes.actual_each_source_repeated_measurement_precision_update_has_the_derived_parameters
      (fun _ => 0) n).2

theorem actual_full_repeated_product_likelihood_has_the_derived_bayes_factorization
    (n : ℕ) (y : Readings n) (latent : ℝ) :
    gaussianPDF 0 1 latent * likelihood n y latent =
      evidence n y * gaussianPDF (readingMean n y) (readingVariance n) latent := by
  induction n with
  | zero => simp [likelihood, evidence, readingMean, readingSum, readingVariance,
      CompleteModulesGPRepeatedBayes.prefixVariance]
  | succ n ih =>
    have hv : 0 < readingVariance n := by
      unfold readingVariance CompleteModulesGPRepeatedBayes.prefixVariance; positivity
    have hb := CompleteAppliedGaussianBayesGeneral.actual_general_extended_gaussian_bayes_factorization
      (readingMean n y.1) y.2 latent (readingVariance n) 1 hv (by norm_num)
    have hp := actual_repeated_reading_mean_and_variance_are_the_genuine_recursive_bayes_parameters n y
    simp only [hp.1, hp.2] at hb
    change gaussianPDF 0 1 latent * (likelihood n y.1 latent * gaussianPDF latent 1 y.2) = _
    rw [← mul_assoc, ih y.1, mul_assoc, hb]
    simp only [evidence, mul_assoc]

theorem actual_constructed_repeated_reading_joint_has_the_true_prior_likelihood_density
    (n : ℕ) : fullJoint n = (volume.prod (readingVolume n)).withDensity
      (fun pair => gaussianPDF 0 1 pair.1 * likelihood n pair.2 pair.1) := by
  haveI : IsSFiniteKernel ((Kernel.const ℝ (readingVolume n)).withDensity
      (fun latent y => likelihood n y latent)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun latent y => likelihood_ne_top n y latent)
  rw [fullJoint,
    actual_any_finite_number_of_conditionally_independent_readings_has_the_true_product_density,
    gaussianReal_of_var_ne_zero _ (by norm_num),
    Measure.withDensity_compProd_withDensity (by fun_prop) (likelihood_measurable n),
    Measure.compProd_const]

theorem actual_swap_of_any_repeated_reading_joint_density
    (n : ℕ) (density : ℝ × Readings n → ℝ≥0∞) (hd : Measurable density) :
    ((volume.prod (readingVolume n)).withDensity density).map Prod.swap =
      ((readingVolume n).prod volume).withDensity (fun pair => density pair.swap) := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_map htest measurable_swap]
  change (∫⁻ a, (test ∘ Prod.swap) a ∂(volume.prod (readingVolume n)).withDensity density) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hd (htest.comp measurable_swap)]
  change _ = (∫⁻ a, test a ∂((readingVolume n).prod volume).withDensity (density ∘ Prod.swap))
  rw [lintegral_withDensity_eq_lintegral_mul _ (hd.comp measurable_swap) htest]
  have ht : Measurable (fun pair : Readings n × ℝ => density pair.swap * test pair) :=
    (hd.comp measurable_swap).mul htest
  have h := lintegral_map ht measurable_swap (μ := volume.prod (readingVolume n))
  rw [Measure.prod_swap] at h
  simpa only [Prod.swap_swap, Function.comp_def, Pi.mul_apply] using h.symm

theorem actual_repeated_reading_posterior_kernel_has_its_derived_density
    (n : ℕ) : posteriorKernel n = (Kernel.const (Readings n) volume).withDensity
      (fun y latent => gaussianPDF (readingMean n y) (readingVariance n) latent) := by
  have hv : readingVariance n ≠ 0 := by
    unfold readingVariance CompleteModulesGPRepeatedBayes.prefixVariance; positivity
  ext y event hevent
  rw [Kernel.withDensity_apply' _ (by
    have hm := readingMean_measurable n
    fun_prop), Kernel.const_apply]
  change gaussianReal (readingMean n y) (readingVariance n) event = _
  rw [gaussianReal_of_var_ne_zero _ hv, withDensity_apply _ hevent]

theorem actual_full_repeated_reading_model_derives_the_data_conditional_gaussian_kernel
    (n : ℕ) : (fullJoint n).map Prod.swap = dataLaw n ⊗ₘ posteriorKernel n := by
  haveI : IsSFiniteKernel ((Kernel.const (Readings n) volume).withDensity
      (fun y latent => gaussianPDF (readingMean n y) (readingVariance n) latent)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => gaussianPDF_ne_top)
  rw [actual_constructed_repeated_reading_joint_has_the_true_prior_likelihood_density,
    actual_swap_of_any_repeated_reading_joint_density _ _ (by
      have hg : Measurable (fun pair : ℝ × Readings n => gaussianPDF 0 1 pair.1) := by fun_prop
      exact hg.mul (likelihood_measurable n)),
    dataLaw, actual_repeated_reading_posterior_kernel_has_its_derived_density,
    Measure.withDensity_compProd_withDensity (evidence_measurable n) (by
      change Measurable (fun pair : Readings n × ℝ => gaussianPDF (readingMean n pair.1) (readingVariance n) pair.2)
      have hm := (readingMean_measurable n).comp measurable_fst
      fun_prop), Measure.compProd_const]
  apply congrArg (fun density => ((readingVolume n).prod volume).withDensity density)
  funext pair
  exact actual_full_repeated_product_likelihood_has_the_derived_bayes_factorization n _ _

theorem actual_repeated_reading_data_law_is_the_true_probability_marginal
    (n : ℕ) : ((fullJoint n).map Prod.swap).fst = dataLaw n := by
  rw [actual_full_repeated_reading_model_derives_the_data_conditional_gaussian_kernel,
    Measure.fst_compProd]
instance dataLaw_probability (n : ℕ) : IsProbabilityMeasure (dataLaw n) := by
  rw [← actual_repeated_reading_data_law_is_the_true_probability_marginal]
  infer_instance

end SafeLearning.CompleteModulesGPRepeatedJoint
