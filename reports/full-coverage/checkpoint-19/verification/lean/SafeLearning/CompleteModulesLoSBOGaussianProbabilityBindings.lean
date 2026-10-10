import SafeLearning.CompleteModulesLoSBOGaussianNoise
import SafeLearning.CompleteModulesLoSBOGaussianNumerics
import SafeLearning.CompleteModulesLoSBOGaussianHorizon

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SafeLearning.CompleteModulesLoSBOGaussianProbabilityBindings
open CompleteAppliedGaussianCDF CompleteAppliedGaussianStandardization
open CompleteModulesLoSBOGaussianNoise CompleteModulesLoSBOGaussianNumerics
open CompleteModulesLoSBOGaussianHorizon

theorem actual_centered_gaussian_divided_by_its_standard_deviation_has_standard_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (sigma : ℝ≥0) (hs : 0 < sigma) (hlaw : HasLaw X (gaussianReal 0 (sigma^2)) P) :
    HasLaw (fun omega => X omega/(sigma:ℝ)) (gaussianReal 0 1) P := by
  have hz := gaussianReal_div_const hlaw (sigma:ℝ)
  have hm : NNReal.mk ((sigma:ℝ)^2) (sq_nonneg (sigma:ℝ))=sigma^2 := by ext;rfl
  rw [hm,div_self (pow_ne_zero 2 hs.ne')] at hz
  norm_num only [zero_div] at hz
  exact hz

theorem actual_arbitrary_gaussian_measurement_twice_sigma_exceedance_is_the_true_source_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (sigma : ℝ≥0) (hs : 0 < sigma) (hlaw : HasLaw X (gaussianReal 0 (sigma^2)) P) :
    P.real {omega | 2*(sigma:ℝ) < |X omega|}=actualSingleExceedanceProbability ∧
      P.real {omega | 2*(sigma:ℝ)<X omega}=standardCDF (-2) := by
  have hsp : 0 < (sigma:ℝ) := hs
  have hz := actual_centered_gaussian_divided_by_its_standard_deviation_has_standard_law P X sigma hs hlaw
  have hb := hz.measureReal_eq (p:=fun x:ℝ => 2 < |x|) (by measurability)
  have ho := hz.measureReal_eq (p:=fun x:ℝ => 2<x) (by measurability)
  have heb : {omega | 2 < |X omega/(sigma:ℝ)|}={omega | 2*(sigma:ℝ) < |X omega|} := by
    ext omega
    simp only [mem_setOf_eq,abs_div,abs_of_pos hsp]
    exact (lt_div_iff₀ hsp)
  have heo : {omega | 2<X omega/(sigma:ℝ)}={omega | 2*(sigma:ℝ)<X omega} := by
    ext omega
    simp only [mem_setOf_eq]
    exact (lt_div_iff₀ hsp)
  change P.real {omega | 2 < |X omega/(sigma:ℝ)|}=actualSingleExceedanceProbability at hb
  change P.real {omega | 2<X omega/(sigma:ℝ)}=(gaussianReal 0 1).real (Ioi 2) at ho
  rw [heb] at hb
  rw [heo] at ho
  have hc := measureReal_compl (μ:=gaussianReal 0 1) (s:=Iic (2:ℝ)) measurableSet_Iic
  have hu : (gaussianReal 0 1).real univ=1 := by simp
  simp only [compl_Iic,hu] at hc
  change (gaussianReal 0 1).real (Ioi 2)=1-standardCDF 2 at hc
  rw [hc,←actual_standard_gaussian_cdf_reflection] at ho
  exact ⟨hb,ho⟩

theorem actual_independent_twenty_five_gaussian_measurements_have_the_true_exceedance_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (noise : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (noise n)) (hind : iIndepFun noise P)
    (sigma : ℝ≥0) (hs : 0 < sigma) (hlaw : ∀ n, HasLaw (noise n) (gaussianReal 0 (sigma^2)) P) :
    P.real {omega | ∃ n<25, 2*(sigma:ℝ) < |noise n omega|}=1-(1-actualSingleExceedanceProbability)^25 ∧
      |P.real {omega | ∃ n<25, 2*(sigma:ℝ) < |noise n omega|}-(69/100:ℝ)|≤1/200 := by
  have hp := actual_independent_gaussian_first_T_noise_bounds_have_probability_p_power_T P noise hind
    (sigma^2) hlaw (2*(sigma:ℝ)) 25
  have hi := actual_source_gaussian_interval_probability_is_the_scaled_two_sided_cdf
    (2*(sigma:ℝ)) (by positivity) sigma hs.ne'
  have hdiv : 2*(sigma:ℝ)/(sigma:ℝ)=2 := by field_simp
  rw [hdiv] at hi
  have he : (gaussianReal 0 (sigma^2)).real (actualBoundEvent (2*(sigma:ℝ)))=1-actualSingleExceedanceProbability := by
    have hprob := actual_single_exceedance_equals_the_literal_reflected_cdf_and_rounds_to_point0455
    have hsym := actual_standard_gaussian_cdf_reflection 2
    linarith [hi,hprob.1]
  rw [he] at hp
  have hm : MeasurableSet {omega | ∀ n<25, |noise n omega|≤2*(sigma:ℝ)} := by
    have he : {omega | ∀ n<25, |noise n omega|≤2*(sigma:ℝ)}=
        ⋂ n∈Finset.range 25, {omega | |noise n omega|≤2*(sigma:ℝ)} := by ext omega;simp only [mem_iInter,Finset.mem_range,mem_setOf_eq]
    rw [he]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun _ =>
      measurableSet_le ((hmeas n).abs) measurable_const))
  have hc := probReal_add_probReal_compl (μ:=P) hm
  have hs' : {omega | ∀ n<25, |noise n omega|≤2*(sigma:ℝ)}ᶜ=
      {omega | ∃ n<25, 2*(sigma:ℝ) < |noise n omega|} := by ext omega;simp only [mem_compl_iff,mem_setOf_eq,not_forall,not_imp,not_le,exists_prop]
  rw [hs',hp] at hc
  have hevent : P.real {omega | ∃ n<25, 2*(sigma:ℝ) < |noise n omega|}=1-(1-actualSingleExceedanceProbability)^25 := by linarith
  refine ⟨hevent,?_⟩
  rw [hevent]
  exact actual_one_sided_probability_and_twenty_five_exceedance_probabilities_have_the_source_roundings.2.1

theorem actual_source_horizon_twenty_five_delta_point_zero_one_radius_and_scaled_rounding
    (sigma : ℝ≥0) :
    actualHorizonRadius sigma 25 (1/100)=(sigma:ℝ)*Real.sqrt (2*Real.log 5000) ∧
      |actualHorizonRadius sigma 25 (1/100)-(413/100:ℝ)*(sigma:ℝ)|≤(sigma:ℝ)/200 := by
  have he : actualHorizonRadius sigma 25 (1/100)=(sigma:ℝ)*Real.sqrt (2*Real.log 5000) := by
    norm_num [actualHorizonRadius]
  refine ⟨he,?_⟩
  rw [he]
  have hb := actual_gaussian_horizon_multiplier_rounds_to_four_point_one_three.1
  have hm := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ (sigma:ℝ) by positivity)
  have hf : (sigma:ℝ)*Real.sqrt (2*Real.log 5000)-(413/100:ℝ)*(sigma:ℝ)=
      (sigma:ℝ)*(Real.sqrt (2*Real.log 5000)-(413/100:ℝ)) := by ring
  rw [hf,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ (sigma:ℝ) by positivity)]
  convert hm using 1 <;> ring

end SafeLearning.CompleteModulesLoSBOGaussianProbabilityBindings
