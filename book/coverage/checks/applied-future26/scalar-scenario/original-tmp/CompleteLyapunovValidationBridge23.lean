import SafeLearning.CompleteAppliedValidation
import SafeLearning.CompleteAppliedDiscountedHorizons

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SafeLearning.CompleteLyapunovValidationBridge23

def empirical {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) (w : Ω) : ℝ :=
  (1/(n:ℝ))*∑ i,X i w

private theorem bounded_average_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0<n) (X : Fin n → Ω → ℝ) (m epsilon : ℝ)
    (he : 0≤epsilon) (hInd : iIndepFun X P)
    (hm : ∀ i,AEMeasurable (X i) P)
    (hb : ∀ i,∀ᵐ w ∂P,X i w∈Icc (0:ℝ) 1)
    (hmean : ∀ i,∫ w,X i w ∂P = m) :
    P.real {w | epsilon≤empirical n X w-m}≤Real.exp (-2*(n:ℝ)*epsilon^2) := by
  let Y : Fin n → Ω → ℝ := fun i w=>X i w-m
  have hi : iIndepFun Y P := hInd.comp (fun (_:Fin n) (x:ℝ)=>x-m)
    (fun _=>measurable_id.sub_const m)
  have hsg : ∀i,HasSubgaussianMGF (Y i) (1/4) P := by
    intro i
    have h := CompleteAppliedConcentration.centered_unit_interval_subgaussian P (X i) (hm i) (hb i)
    simpa only [hmean i] using h
  have hs : HasSubgaussianMGF (fun w=>∑i,Y i w) ((n:ℝ≥0)/4) P := by
    simpa [div_eq_mul_inv] using HasSubgaussianMGF.sum_of_iIndepFun hi
      (s:=Finset.univ) (c:=fun _=>(1/4:ℝ≥0)) (fun i _=>hsg i)
  have hnreal : (0:ℝ)<n := by exact_mod_cast hn
  have ht := hs.measure_ge_le (mul_nonneg hnreal.le he)
  have hset : {w | epsilon≤empirical n X w-m}=
      {w | (n:ℝ)*epsilon≤∑i,Y i w} := by
    ext w
    simp only [Set.mem_setOf_eq]
    have heq : empirical n X w-m=(1/(n:ℝ))*∑i,Y i w := by
      simp only [empirical,Y,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul]
      field_simp
    rw [heq,one_div_mul_eq_div,le_div_iff₀ hnreal,mul_comm epsilon (n:ℝ)]
  have hexp : -((n:ℝ)*epsilon)^2/(2*((((n:ℝ≥0)/4):ℝ≥0):ℝ))=
      -2*(n:ℝ)*epsilon^2 := by
    push_cast
    field_simp
    ring
  rw [hexp] at ht
  rw [hset]
  exact ht

theorem actual_corrected_validation_samples_certify_the_population_lower_mean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 5757≤n) (X : Fin n → Ω → ℝ) (m : ℝ)
    (hInd : iIndepFun X P) (hm : ∀i,Measurable (X i))
    (hb : ∀i,∀ᵐ w ∂P,X i w∈Icc (0:ℝ) 1)
    (hmean : ∀i,∫w,X i w ∂P = m) :
    (99/100:ℝ)≤P.real {w | empirical n X w-1/50≤ m} := by
  have ht := bounded_average_upper_tail P n (by omega) X m (1/50) (by norm_num)
    hInd (fun i=>(hm i).aemeasurable) hb hmean
  have he : Real.exp (-2*(n:ℝ)*(1/50)^2)≤1/100 := by
    obtain ⟨_,_,hl,hu⟩ :=
      CompleteAppliedDiscountedHorizons.actual_discount_log_enclosure_and_log_hundred_enclosure
    have hnreal : (5757:ℝ)≤n := by exact_mod_cast hn
    have hlog : Real.log 100≤2*(n:ℝ)*(1/50)^2 := by linarith
    rw [show (1/100:ℝ)=Real.exp (-Real.log 100) by
      rw [Real.exp_neg,Real.exp_log (by norm_num)];norm_num,Real.exp_le_exp]
    linarith
  have hbadMeas : MeasurableSet {w | m<empirical n X w-1/50} :=
    measurableSet_lt measurable_const
      ((measurable_const.mul (Finset.measurable_sum Finset.univ (fun i _=>hm i))).sub_const _)
  have hbad : P.real {w | m<empirical n X w-1/50}≤1/100 := by
    apply (measureReal_mono (μ:=P) (show {w | m<empirical n X w-1/50}⊆
      {w | (1/50:ℝ)≤empirical n X w-m} by intro w hw;dsimp at hw ⊢;linarith)).trans
    exact ht.trans he
  have hc := probReal_compl_eq_one_sub (μ:=P) hbadMeas
  have hset : {w | m<empirical n X w-1/50}ᶜ={w | empirical n X w-1/50≤ m} := by
    ext w;simp
  rw [hset] at hc
  linarith

theorem actual_accepted_fixed_validation_certifies_point_nine_three
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 5757≤n) (X : Fin n → Ω → ℝ) (m : ℝ)
    (hInd : iIndepFun X P) (hm : ∀i,Measurable (X i))
    (hb : ∀i,∀ᵐ w ∂P,X i w∈Icc (0:ℝ) 1)
    (hmean : ∀i,∫w,X i w ∂P = m) :
    (99/100:ℝ)≤P.real {w | (19/20≤empirical n X w)→93/100≤ m} := by
  have h := actual_corrected_validation_samples_certify_the_population_lower_mean
    P n hn X m hInd hm hb hmean
  exact h.trans (measureReal_mono (μ:=P) (by
    intro w hw hh;change empirical n X w-1/50≤ m at hw;linarith))

theorem actual_normalized_credible_region_transfers_stability_to_full_belief
    {Θ : Type*} [MeasurableSpace Θ] (posterior : Measure Θ) [IsProbabilityMeasure posterior]
    (credible stable : Set Θ) (hc : posterior.real credible=19/20)
    (hm : (93/100:ℝ)≤posterior.real (credible∩stable)/posterior.real credible) :
    (1767/2000:ℝ)≤posterior.real stable ∧ (22/25:ℝ)≤posterior.real stable := by
  have hm' : (1767/2000:ℝ)≤posterior.real (credible∩stable) := by
    rw [hc,le_div_iff₀ (by norm_num : (0:ℝ)<19/20)] at hm
    nlinarith
  have hs := measureReal_mono (μ:=posterior) (inter_subset_right : credible∩stable⊆stable)
  constructor
  · exact hm'.trans hs
  · linarith [hm'.trans hs]

theorem actual_independent_normalized_posterior_validation_has_point_eight_eight_confidence
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (posterior : Measure Θ) [IsProbabilityMeasure posterior]
    (credible stable : Set Θ) (hc : posterior.real credible=19/20)
    (n : ℕ) (hn : 5757≤n) (X : Fin n → Ω → ℝ) (p : unitInterval)
    (hp : (p:ℝ)=posterior.real (credible∩stable)/posterior.real credible)
    (hInd : iIndepFun X P) (hm : ∀i,Measurable (X i))
    (hLaw : ∀i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) P) :
    (99/100:ℝ)≤P.real {w | (19/20≤empirical n X w)→22/25≤posterior.real stable} := by
  have hs := actual_accepted_fixed_validation_certifies_point_nine_three
    P n hn X p hInd hm
    (fun i=>(CompleteAppliedValidation.bernoulli_support_mean P (X i) p (hLaw i)).1)
    (fun i=>(CompleteAppliedValidation.bernoulli_support_mean P (X i) p (hLaw i)).2)
  exact hs.trans (measureReal_mono (μ:=P) (by
    intro w hw hh
    have hpop := hw hh
    rw [hp] at hpop
    exact (actual_normalized_credible_region_transfers_stability_to_full_belief
      posterior credible stable hc hpop).2))

theorem actual_source_logarithm_roundings_and_strict_numerical_inequalities :
    |Real.log 1000-69078/10000|<1/20000 ∧
      |Real.log (20/19)-51293/1000000|<1/2000000 ∧
      Real.log 1000/Real.log (20/19)<1347/10 ∧
      Real.log 1000≠69078/10000 ∧
      Real.log (20/19)≠51293/1000000 ∧
      Real.log 1000/Real.log (20/19)≠1347/10 := by
  obtain ⟨hl,hu,h100l,h100u⟩ :=
    CompleteAppliedDiscountedHorizons.actual_discount_log_enclosure_and_log_hundred_enclosure
  have hlog : Real.log 1000=(3/2:ℝ)*Real.log 100 := by
    have h1 : Real.log 1000=3*Real.log 10 := by
      rw [show (1000:ℝ)=10^3 by norm_num,Real.log_pow];norm_num
    have h2 : Real.log 100=2*Real.log 10 := by
      rw [show (100:ℝ)=10^2 by norm_num,Real.log_pow];norm_num
    linarith
  have hd : 0<Real.log (20/19:ℝ) := by linarith
  have hr : Real.log 1000/Real.log (20/19)<1347/10 := by
    apply (div_lt_iff₀ hd).mpr
    rw [hlog]
    linarith
  refine ⟨?_,?_,hr,?_,?_,ne_of_lt hr⟩
  · rw [hlog,abs_lt];constructor <;> linarith
  · rw [abs_lt];constructor <;> linarith
  · rw [hlog];intro h;linarith
  · intro h;linarith

end SafeLearning.CompleteLyapunovValidationBridge23
