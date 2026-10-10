import SafeLearning.CompleteAppliedBoundedSampleSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open SafeLearning.CompleteAppliedMonteCarloEstimate
open SafeLearning.CompleteAppliedBoundedSampleSizes
namespace SafeLearning.CompleteAppliedBoundedSampleNumbers

theorem actual_log_two_hundred_has_a_rigorous_enclosure :
    (5298317/1000000:ℝ)<Real.log 200 ∧
    Real.log 200<(5298318/1000000:ℝ) := by
  have hb1 := Real.exp_bound (x := -(5298317/8000000:ℝ)) (by norm_num)
    (n := 16) (by norm_num)
  have hb2 := Real.exp_bound (x := -(5298318/8000000:ℝ)) (by norm_num)
    (n := 16) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hb1 hb2
  have hl : (51566929/100000000:ℝ)≤Real.exp (-(5298317/8000000:ℝ)) := by
    linarith [(abs_le.mp hb1).1]
  have hu : Real.exp (-(5298318/8000000:ℝ))≤(51566923/100000000:ℝ) := by
    linarith [(abs_le.mp hb2).2]
  have hpl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤51566929/100000000) hl 8
  have hpu := pow_le_pow_left₀ (Real.exp_nonneg _) hu 8
  have hel : Real.exp (-(5298317/1000000:ℝ))=
      (Real.exp (-(5298317/8000000:ℝ)))^8 := by
    rw [←Real.exp_nat_mul];congr 1;norm_num
  have heu : Real.exp (-(5298318/1000000:ℝ))=
      (Real.exp (-(5298318/8000000:ℝ)))^8 := by
    rw [←Real.exp_nat_mul];congr 1;norm_num
  have he : Real.exp (-Real.log (200:ℝ))=(1/200:ℝ) := by
    rw [Real.exp_neg,Real.exp_log (by norm_num)];norm_num
  have hlo : Real.exp (-Real.log (200:ℝ))<Real.exp (-(5298317/1000000:ℝ)) := by
    rw [he,hel];norm_num at hpl;linarith
  have hhi : Real.exp (-(5298318/1000000:ℝ))<Real.exp (-Real.log (200:ℝ)) := by
    rw [he,heu];norm_num at hpu;linarith
  have hlo' := Real.exp_lt_exp.mp hlo
  have hhi' := Real.exp_lt_exp.mp hhi
  constructor <;> linarith

theorem actual_hoeffding_real_sample_threshold_rounds_to_the_display_but_is_not_equal_to_it :
    |200*Real.log 200-(10597/10:ℝ)|≤1/20 ∧
    200*Real.log 200<(10597/10:ℝ) ∧
    (1059:ℝ)<200*Real.log 200 ∧ 200*Real.log 200<(1060:ℝ) := by
  obtain ⟨hl,hu⟩ := actual_log_two_hundred_has_a_rigorous_enclosure
  refine ⟨?_,?_,?_,?_⟩
  · rw [abs_le];constructor <;> linarith
  · linarith
  · linarith
  · linarith

theorem actual_hoeffding_integer_sufficient_count_is_exactly_ten_sixty (n : ℕ) :
    2*Real.exp (-2*(n:ℝ)*(1/20)^2)≤(1/100:ℝ) ↔ 1060≤n := by
  rw [actual_source_hoeffding_sufficient_sample_count_is_the_exact_logarithmic_threshold]
  obtain ⟨_,_,hl,hu⟩ := actual_hoeffding_real_sample_threshold_rounds_to_the_display_but_is_not_equal_to_it
  constructor
  · intro h
    by_contra hno
    have hn : n≤1059 := by omega
    have hnr : (n:ℝ)≤1059 := by exact_mod_cast hn
    linarith
  · intro hn
    have hnr : (1060:ℝ)≤n := by exact_mod_cast hn
    linarith

theorem actual_ten_sixty_samples_suffice_for_the_strict_source_hoeffding_guarantee
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 1060 → Ω → ℝ) (m : ℝ) (hInd : iIndepFun X μ)
    (hm : ∀ i,Measurable (X i))
    (hb : ∀ i,∀ᵐ omega ∂μ,X i omega∈Set.Icc (0:ℝ) 1)
    (hmean : ∀ i,(∫ omega,X i omega ∂μ)=m) :
    99/100≤μ.real {omega | |empiricalRate 1060 X omega-m|<1/20} := by
  have hbnd := SafeLearning.CompleteAppliedConcentration.bounded_independent_average_hoeffding
    μ 1060 (by norm_num) X m (1/20) (by norm_num) hInd
    (fun i => (hm i).aemeasurable) hb hmean
  have h1060 := (actual_hoeffding_integer_sufficient_count_is_exactly_ten_sixty 1060).mpr (by norm_num)
  have htail : μ.real {omega | (1/20:ℝ)≤|empiricalRate 1060 X omega-m|}≤1/100 :=
    hbnd.trans h1060
  have hmeas : Measurable (empiricalRate 1060 X) :=
    measurable_const.mul (Finset.measurable_fun_sum Finset.univ (fun i _ => hm i))
  have hbad : MeasurableSet {omega | (1/20:ℝ)≤|empiricalRate 1060 X omega-m|} := by
    measurability
  have hc := probReal_compl_eq_one_sub (μ := μ) hbad
  have he : {omega | (1/20:ℝ)≤|empiricalRate 1060 X omega-m|}ᶜ=
      {omega | |empiricalRate 1060 X omega-m|<1/20} := by ext omega;simp
  rw [he] at hc
  linarith

end SafeLearning.CompleteAppliedBoundedSampleNumbers
