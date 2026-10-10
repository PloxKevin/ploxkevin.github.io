import SafeLearning.CompleteAppliedValidation
import SafeLearning.CompleteModulesGPNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SafeLearning.CompleteModulesVerificationValidation20

theorem actual_one_sided_source_sample_rule (N : ℝ) :
    Real.exp (-N/50) ≤ (1/100 : ℝ) ↔ 50*Real.log 100 ≤ N := by
  rw [show (1/100 : ℝ) = Real.exp (-Real.log 100) by
    rw [Real.exp_neg,Real.exp_log (by norm_num)];norm_num,Real.exp_le_exp]
  constructor <;> intro h <;> linarith

theorem actual_logarithmic_sample_cutoff_rounds_to_two_thirty_point_two_five_eight_five_one :
    |50*Real.log 100-(23025851/100000 : ℝ)| < 1/200000 ∧
      (230 : ℝ) < 50*Real.log 100 ∧ 50*Real.log 100 < 231 := by
  have he : Real.log (100 : ℝ) = 2*Real.log 10 := by
    rw [show (100 : ℝ) = 10^2 by norm_num,Real.log_pow]; norm_num
  have h20 := CompleteModulesGPNumerics.log_twenty_enclosure
  have h2 := Real.log_two_near_10
  have he10 : Real.log (10 : ℝ) = Real.log 20-Real.log 2 := by
    rw [←Real.log_div (by norm_num : (20 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hl : (230258508/100000000 : ℝ) < Real.log 10 := by
    rw [he10];linarith [h20.1,(abs_le.mp h2).2]
  have hu : Real.log 10 < (230258510/100000000 : ℝ) := by
    rw [he10];linarith [h20.2,(abs_le.mp h2).1]
  rw [he,abs_lt]
  refine ⟨⟨?_,?_⟩,?_,?_⟩ <;> linarith

theorem actual_least_sufficient_integer_sample_count_is_two_thirty_one (n : ℕ) :
    Real.exp (-(n : ℝ)/50) ≤ (1/100 : ℝ) ↔ 231 ≤ n := by
  rw [actual_one_sided_source_sample_rule]
  obtain ⟨_,hl,hu⟩ := actual_logarithmic_sample_cutoff_rounds_to_two_thirty_point_two_five_eight_five_one
  constructor
  · intro hn
    have hn' : (230 : ℝ) < n := hl.trans_le hn
    exact_mod_cast (show (231 : ℕ) ≤ n by exact Nat.succ_le_iff.mpr (by exact_mod_cast hn'))
  · intro hn
    have hn' : (231 : ℝ) ≤ n := by exact_mod_cast hn
    exact hu.le.trans hn'

theorem actual_bounded_independent_average_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (m epsilon : ℝ)
    (he : 0 ≤ epsilon) (hInd : iIndepFun X P)
    (hm : ∀ i,AEMeasurable (X i) P)
    (hb : ∀ i,∀ᵐ w ∂P,X i w ∈ Icc (0 : ℝ) 1)
    (hmean : ∀ i,∫ w,X i w ∂P = m) :
    P.real {w | epsilon ≤ (1/(n : ℝ))*∑ i,X i w-m} ≤
      Real.exp (-2*(n : ℝ)*epsilon^2) := by
  let Y : Fin n → Ω → ℝ := fun i w => X i w-m
  have hi : iIndepFun Y P := hInd.comp (fun (_ : Fin n) (x : ℝ) => x-m)
    (fun _ => measurable_id.sub_const m)
  have hsg : ∀ i,HasSubgaussianMGF (Y i) (1/4) P := by
    intro i
    have h := CompleteAppliedConcentration.centered_unit_interval_subgaussian P (X i) (hm i) (hb i)
    simpa only [hmean i] using h
  have hs : HasSubgaussianMGF (fun w => ∑ i,Y i w) ((n : ℝ≥0)/4) P := by
    simpa [div_eq_mul_inv] using HasSubgaussianMGF.sum_of_iIndepFun hi
      (s := Finset.univ) (c := fun _ => (1/4 : ℝ≥0)) (fun i _ => hsg i)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have htail := hs.measure_ge_le (mul_nonneg hnreal.le he)
  have hset : {w | epsilon ≤ (1/(n : ℝ))*∑ i,X i w-m} =
      {w | (n : ℝ)*epsilon ≤ ∑ i,Y i w} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    have heq : (1/(n : ℝ))*∑ i,X i w-m = (1/(n : ℝ))*∑ i,Y i w := by
      simp only [Y,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul]
      field_simp
    rw [heq,one_div_mul_eq_div,le_div_iff₀ hnreal,mul_comm epsilon (n : ℝ)]
  have hexp : -((n : ℝ)*epsilon)^2/(2*((((n : ℝ≥0)/4) : ℝ≥0) : ℝ)) =
      -2*(n : ℝ)*epsilon^2 := by
    push_cast
    field_simp
    ring
  rw [hexp] at htail
  rw [hset]
  exact htail

theorem actual_source_independent_validation_has_point_nine_nine_population_lower_confidence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 231 ≤ n) (X : Fin n → Ω → ℝ) (populationSuccess : ℝ)
    (hInd : iIndepFun X P) (hm : ∀ i,Measurable (X i))
    (hb : ∀ i,∀ᵐ w ∂P,X i w ∈ Icc (0 : ℝ) 1)
    (hmean : ∀ i,∫ w,X i w ∂P = populationSuccess) :
    (99/100 : ℝ) ≤ P.real {w | (1/(n : ℝ))*∑ i,X i w-(1/10 : ℝ) ≤ populationSuccess} := by
  have htail := actual_bounded_independent_average_upper_tail P n (by omega) X populationSuccess
    (1/10) (by norm_num) hInd (fun i => (hm i).aemeasurable) hb hmean
  have hupper : Real.exp (-2*(n : ℝ)*(1/10)^2) ≤ (1/100 : ℝ) := by
    have h := (actual_least_sufficient_integer_sample_count_is_two_thirty_one n).mpr hn
    convert h using 1 <;> congr 1 <;> ring
  have hbadMeas : MeasurableSet {w | populationSuccess < (1/(n : ℝ))*∑ i,X i w-(1/10 : ℝ)} := by
    apply measurableSet_lt measurable_const
    exact (measurable_const.mul (Finset.measurable_sum Finset.univ (fun i _ => hm i))).sub_const _
  have hbad : P.real {w | populationSuccess < (1/(n : ℝ))*∑ i,X i w-(1/10 : ℝ)} ≤ (1/100 : ℝ) := by
    apply (measureReal_mono (μ := P) (show
      {w | populationSuccess < (1/(n : ℝ))*∑ i,X i w-(1/10 : ℝ)} ⊆
        {w | (1/10 : ℝ) ≤ (1/(n : ℝ))*∑ i,X i w-populationSuccess} by
        intro w hw;dsimp at hw ⊢;linarith)).trans
    exact htail.trans hupper
  have hc := probReal_compl_eq_one_sub (μ := P) hbadMeas
  have he : {w | populationSuccess < (1/(n : ℝ))*∑ i,X i w-(1/10 : ℝ)}ᶜ =
      {w | (1/(n : ℝ))*∑ i,X i w-(1/10 : ℝ) ≤ populationSuccess} := by
    ext w;simp
  rw [he] at hc
  linarith

theorem actual_observed_point_nine_eight_yields_point_eight_eight_on_the_confidence_event
    (populationSuccess : ℝ) (h : (49/50 : ℝ)-1/10 ≤ populationSuccess) :
    (49/50 : ℝ)-1/10 = 22/25 ∧ (22/25 : ℝ) ≤ populationSuccess := by
  constructor
  · norm_num
  · linarith

theorem actual_target_point_nine_five_requires_an_impossible_success_fraction
    (empirical : ℝ) (he : empirical ∈ Icc (0 : ℝ) 1) :
    (19/20 ≤ empirical-(1/10 : ℝ) ↔ 21/20 ≤ empirical) ∧
      ¬(19/20 ≤ empirical-(1/10 : ℝ)) := by
  constructor
  · constructor <;> intro h <;> linarith
  · intro h;linarith [he.2]

end SafeLearning.CompleteModulesVerificationValidation20
