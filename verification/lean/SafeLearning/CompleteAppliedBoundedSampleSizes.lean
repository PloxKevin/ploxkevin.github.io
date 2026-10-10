import SafeLearning.CompleteAppliedMonteCarloEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open SafeLearning.CompleteAppliedMonteCarloEstimate
namespace SafeLearning.CompleteAppliedBoundedSampleSizes

theorem actual_bounded_independent_average_has_mean_and_worst_case_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0<n) (X : Fin n → Ω → ℝ) (m : ℝ)
    (hInd : iIndepFun X μ) (hm : ∀ i,Measurable (X i))
    (hb : ∀ i,∀ᵐ omega ∂μ,X i omega∈Set.Icc (0:ℝ) 1)
    (hmean : ∀ i,(∫ omega,X i omega ∂μ)=m) :
    (∫ omega,empiricalRate n X omega ∂μ)=m ∧
    variance (empiricalRate n X) μ≤1/(4*(n:ℝ)) ∧
    MemLp (empiricalRate n X) 2 μ := by
  have hsq (i : Fin n) : MemLp (X i) 2 μ :=
    memLp_of_bounded (hb i) (hm i).aestronglyMeasurable 2
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hmem : MemLp (fun omega => ∑ i,X i omega) 2 μ :=
    memLp_finsetSum _ (fun i _ => hsq i)
  have hvariance (i : Fin n) : variance (X i) μ≤(1/4:ℝ) := by
    convert variance_le_sq_of_bounded (hb i) (hm i).aemeasurable using 1;norm_num
  have hv := IndepFun.variance_sum (fun i (_ : i∈(Finset.univ:Finset (Fin n))) => hsq i)
    (fun _i _hi _j _hj hij => hInd.indepFun hij)
  have hsum : variance (fun omega => ∑ i,X i omega) μ=∑ i,variance (X i) μ := by
    convert hv using 1
    congr 1;ext omega;simp
  have hbound : (∑ i,variance (X i) μ)≤(n:ℝ)/4 := by
    calc
      _≤∑ _i:Fin n,(1/4:ℝ) := Finset.sum_le_sum (fun i _ => hvariance i)
      _=_ := by simp [div_eq_mul_inv]
  refine ⟨?_,?_,hmem.const_mul (1/(n:ℝ))⟩
  · unfold empiricalRate
    rw [integral_const_mul,integral_finsetSum _ (fun i _ => (hsq i).integrable (by norm_num))]
    simp only [hmean,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  · change variance (fun omega => (1/(n:ℝ))*(∑ i,X i omega)) μ≤_
    rw [variance_const_mul,hsum]
    calc
      _≤(1/(n:ℝ))^2*((n:ℝ)/4) := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
      _=_ := by field_simp

theorem actual_chebyshev_bound_is_for_the_strict_success_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0<n) (X : Fin n → Ω → ℝ) (m radius : ℝ) (hr : 0<radius)
    (hInd : iIndepFun X μ) (hm : ∀ i,Measurable (X i))
    (hb : ∀ i,∀ᵐ omega ∂μ,X i omega∈Set.Icc (0:ℝ) 1)
    (hmean : ∀ i,(∫ omega,X i omega ∂μ)=m) :
    1-1/(4*(n:ℝ)*radius^2)≤μ.real {omega | |empiricalRate n X omega-m|<radius} := by
  obtain ⟨haverage,hvariance,hsquare⟩ :=
    actual_bounded_independent_average_has_mean_and_worst_case_variance μ n hn X m hInd hm hb hmean
  have hcheb := meas_ge_le_variance_div_sq hsquare hr
  rw [haverage] at hcheb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hreal
  have htail : μ.real {omega | radius≤|empiricalRate n X omega-m|}≤1/(4*(n:ℝ)*radius^2) := by
    calc
      _≤variance (empiricalRate n X) μ/radius^2 := hreal
      _≤(1/(4*(n:ℝ)))/radius^2 := div_le_div_of_nonneg_right hvariance (sq_nonneg _)
      _=_ := by ring
  have hmeas : Measurable (empiricalRate n X) :=
    measurable_const.mul (Finset.measurable_fun_sum Finset.univ (fun i _ => hm i))
  have hbad : MeasurableSet {omega | radius≤|empiricalRate n X omega-m|} := by
    measurability
  have hcomp := probReal_compl_eq_one_sub (μ := μ) hbad
  have he : {omega | radius≤|empiricalRate n X omega-m|}ᶜ=
      {omega | |empiricalRate n X omega-m|<radius} := by ext omega;simp
  rw [he] at hcomp
  linarith

theorem actual_ten_thousand_samples_suffice_for_the_source_chebyshev_guarantee
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 10000 → Ω → ℝ) (m : ℝ) (hInd : iIndepFun X μ)
    (hm : ∀ i,Measurable (X i))
    (hb : ∀ i,∀ᵐ omega ∂μ,X i omega∈Set.Icc (0:ℝ) 1)
    (hmean : ∀ i,(∫ omega,X i omega ∂μ)=m) :
    99/100≤μ.real {omega | |empiricalRate 10000 X omega-m|<1/20} := by
  convert actual_chebyshev_bound_is_for_the_strict_success_event μ 10000 (by norm_num)
    X m (1/20) (by norm_num) hInd hm hb hmean using 1;norm_num

theorem actual_source_chebyshev_sufficient_sample_count_is_exact (n : ℝ) (hn : 0<n) :
    (1/4)/(n*(1/20)^2)≤(1/100:ℝ) ↔ 10000≤n := by
  rw [div_le_iff₀ (by positivity : 0<n*(1/20)^2)]
  constructor <;> intro h <;> nlinarith

theorem actual_source_hoeffding_sufficient_sample_count_is_the_exact_logarithmic_threshold (n : ℝ) :
    2*Real.exp (-2*n*(1/20)^2)≤(1/100:ℝ) ↔ 200*Real.log 200≤n := by
  have hlog : Real.log (1/200:ℝ)=-Real.log 200 := by
    rw [show (1/200:ℝ)=(200:ℝ)⁻¹ by norm_num,Real.log_inv]
  have he : 2*Real.exp (-2*n*(1/20)^2)≤(1/100:ℝ) ↔
      Real.exp (-n/200)≤(1/200:ℝ) := by
    have hx : -2*n*(1/20)^2=-n/200 := by ring
    rw [hx];constructor <;> intro h <;> linarith
  rw [he,←Real.exp_log (by norm_num : (0:ℝ)<1/200),Real.exp_le_exp,hlog]
  constructor <;> intro h <;> linarith

end SafeLearning.CompleteAppliedBoundedSampleSizes
