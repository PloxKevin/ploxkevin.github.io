import SafeLearning.CompleteAppliedZeroConfidence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteAppliedMonteCarloEstimate

def empiricalRate {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) (omega : Ω) : ℝ :=
  (1/(n:ℝ))*∑ i,X i omega
def plugInStandardError (p : ℝ) (n : ℕ) : ℝ := Real.sqrt (p*(1-p)/(n:ℝ))

theorem actual_bernoulli_indicator_has_mean_and_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (p : unitInterval)
    (hLaw : HasLaw X (bernoulliMeasure (1:ℝ) 0 p) μ) :
    (∫ omega,X omega ∂μ)=(p:ℝ) ∧
    variance X μ=(p:ℝ)*(1-(p:ℝ)) := by
  constructor
  · exact (SafeLearning.CompleteAppliedValidation.bernoulli_support_mean μ X p hLaw).2
  · rw [hLaw.variance_eq,variance_eq_integral aemeasurable_id]
    simp [integral_bernoulliMeasure]
    ring

theorem actual_independent_episode_average_has_the_source_mean_and_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : n≠0) (X : Fin n → Ω → ℝ) (p : unitInterval)
    (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    (∫ omega,empiricalRate n X omega ∂μ)=(p:ℝ) ∧
    variance (empiricalRate n X) μ=(p:ℝ)*(1-(p:ℝ))/(n:ℝ) := by
  have hsquare (i : Fin n) : MemLp (X i) 2 μ :=
    memLp_of_bounded (SafeLearning.CompleteAppliedValidation.bernoulli_support_mean
      μ (X i) p (hLaw i)).1 (hLaw i).aemeasurable.aestronglyMeasurable 2
  have hmean (i : Fin n) := (actual_bernoulli_indicator_has_mean_and_variance μ (X i) p (hLaw i)).1
  have hvariance (i : Fin n) := (actual_bernoulli_indicator_has_mean_and_variance μ (X i) p (hLaw i)).2
  have hnreal : (n:ℝ)≠0 := by exact_mod_cast hn
  constructor
  · unfold empiricalRate
    rw [integral_const_mul,integral_finsetSum _ (fun i _ => (hsquare i).integrable (by norm_num))]
    simp only [hmean,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  · have hv := IndepFun.variance_sum (fun i (_hi : i∈(Finset.univ : Finset (Fin n))) => hsquare i)
      (fun _i _hi _j _hj hij => hInd.indepFun hij)
    change variance (fun omega => (1/(n:ℝ))*(∑ i,X i omega)) μ=_
    rw [variance_const_mul]
    have hsum : variance (fun omega => ∑ i,X i omega) μ=
        (n:ℝ)*((p:ℝ)*(1-(p:ℝ))) := by
      calc
        variance (fun omega => ∑ i,X i omega) μ=variance (∑ i,X i) μ := by
          congr 1;ext omega;simp
        _=∑ i,variance (X i) μ := hv
        _=_ := by simp only [hvariance,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [hsum]
    field_simp

theorem actual_fourteen_failures_and_zero_failures_plug_in_the_literal_rates
    {Ω : Type*} (X : Fin 200 → Ω → ℝ) (omega : Ω) :
    ((∑ i,X i omega)=14 → empiricalRate 200 X omega=7/100) ∧
    ((∀ i,X i omega=0) → empiricalRate 200 X omega=0) ∧
    plugInStandardError (7/100) 200=Real.sqrt (651/2000000) ∧
    plugInStandardError 0 200=0 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h;norm_num [empiricalRate,h]
  · intro h
    have hz : (∑ i,X i omega)=0 := Finset.sum_eq_zero (fun i _ => h i)
    norm_num [empiricalRate,hz]
  · norm_num [plugInStandardError]
  · norm_num [plugInStandardError]

theorem actual_two_hundred_clean_episodes_have_the_exact_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 200 → Ω → ℝ) (p : unitInterval) (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    μ.real {omega | ∀ i,X i omega=0}=(1-(p:ℝ))^200 :=
  SafeLearning.CompleteAppliedValidation.zero_failure_probability μ 200 X p hInd hLaw

theorem actual_two_hundred_clean_probability_inverts_to_the_true_upper_limit (p : ℝ)
    (hp : p∈Set.Icc 0 1) :
    ((1-p)^200≤(1/20:ℝ) ↔
      SafeLearning.CompleteAppliedZeroConfidence.zeroUpperLimit 200 (1/20)≤p) ∧
    ((1-p)^200<(1/20:ℝ) ↔
      SafeLearning.CompleteAppliedZeroConfidence.zeroUpperLimit 200 (1/20)<p) ∧
    (1-SafeLearning.CompleteAppliedZeroConfidence.zeroUpperLimit 200 (1/20))^200=(1/20:ℝ) := by
  refine ⟨?_,?_,?_⟩
  · exact SafeLearning.CompleteAppliedZeroConfidence.zero_probability_inversion
      200 (by norm_num) (1/20) p (by norm_num) hp
  · exact SafeLearning.CompleteAppliedZeroConfidence.zero_probability_strict_inversion
      200 (by norm_num) (1/20) p (by norm_num) hp
  · exact SafeLearning.CompleteAppliedZeroConfidence.zero_upper_boundary_equation
      200 (by norm_num) (1/20) (by norm_num)

theorem actual_two_hundred_episode_zero_only_reporting_has_repeated_ninety_five_percent_confidence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 200 → Ω → ℝ) (p : unitInterval) (hInd : iIndepFun X μ)
    (hm : ∀ i,Measurable (X i))
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    19/20≤μ.real {omega | (p:ℝ)≤
      SafeLearning.CompleteAppliedZeroConfidence.zeroOnlyUpperReport 200 X (1/20) omega} := by
  convert SafeLearning.CompleteAppliedZeroConfidence.zero_report_confidence μ 200
    (by norm_num) X p (1/20) (by norm_num) hInd hm hLaw using 1;norm_num

theorem actual_clean_data_and_zero_plug_in_error_do_not_identify_zero_population
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 200 → Ω → ℝ) (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0
      SafeLearning.CompleteAppliedValidationTests.twoPercent) μ) :
    0<μ.real {omega | ∀ i,X i omega=0} ∧
    ∃ omega,(∀ i,X i omega=0) ∧
      (SafeLearning.CompleteAppliedValidationTests.twoPercent:ℝ)≠0 :=
  ⟨SafeLearning.CompleteAppliedValidationTests.positive_zero_failure_probability_at_two_percent
    μ 200 X hInd hLaw,
    SafeLearning.CompleteAppliedValidationTests.zero_failures_do_not_imply_zero_population
      μ 200 X hInd hLaw⟩

end SafeLearning.CompleteAppliedMonteCarloEstimate
