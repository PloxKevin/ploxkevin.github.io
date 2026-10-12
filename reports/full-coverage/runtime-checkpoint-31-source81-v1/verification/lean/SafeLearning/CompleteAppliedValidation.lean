import SafeLearning.CompleteAppliedGridConfidence
import SafeLearning.CoreAnalysis
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedValidation
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- A Bernoulli failure indicator has the actual support and expectation used by validation. -/
theorem bernoulli_support_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (p : unitInterval)
    (hX : HasLaw X (bernoulliMeasure (1:ℝ) 0 p) μ) :
    (∀ᵐ omega ∂μ,X omega ∈ Set.Icc (0:ℝ) 1) ∧ (∫ omega,X omega ∂μ)=(p:ℝ) := by
  constructor
  · apply (hX.ae_iff (measurableSet_Icc.mem : Measurable
      (fun x : ℝ => x ∈ Set.Icc (0:ℝ) 1))).mpr
    rw [bernoulliMeasure_def,ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure
    all_goals simp [ae_dirac_eq]
  · rw [hX.integral_eq]
    simp [integral_bernoulliMeasure]

theorem bounded_independent_average_lower_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0<n)
    (X : Fin n → Ω → ℝ) (m epsilon : ℝ) (he : 0≤epsilon)
    (hInd : iIndepFun X μ) (hm : ∀ i,AEMeasurable (X i) μ)
    (hb : ∀ i,∀ᵐ omega ∂μ,X i omega ∈ Set.Icc (0:ℝ) 1)
    (hmean : ∀ i,(∫ omega,X i omega ∂μ)=m) :
    μ.real {omega | epsilon ≤ m-(1/(n:ℝ))*∑ i,X i omega}≤
      Real.exp (-2*(n:ℝ)*epsilon^2) := by
  let Y : Fin n → Ω → ℝ := fun i omega => X i omega-m
  have hi : iIndepFun Y μ := hInd.comp (fun (_i : Fin n) (x : ℝ) => x-m)
    (fun _ => measurable_id.sub_const m)
  have hsg : ∀ i,HasSubgaussianMGF (Y i) (1/4) μ := by
    intro i
    have h := SafeLearning.CompleteAppliedConcentration.centered_unit_interval_subgaussian
      μ (X i) (hm i) (hb i)
    simpa only [hmean i] using h
  have hs : HasSubgaussianMGF (fun omega => ∑ i,Y i omega) ((n:ℝ≥0)/4) μ := by
    simpa [div_eq_mul_inv] using HasSubgaussianMGF.sum_of_iIndepFun hi
      (s := Finset.univ) (c := fun _ => (1/4:ℝ≥0)) (fun i _ => hsg i)
  have hnreal : (0:ℝ)<n := by exact_mod_cast hn
  have htail := hs.neg.measure_ge_le (mul_nonneg hnreal.le he)
  have hset : {omega | epsilon ≤ m-(1/(n:ℝ))*∑ i,X i omega}=
      {omega | (n:ℝ)*epsilon≤-(∑ i,Y i omega)} := by
    ext omega
    simp only [Set.mem_setOf_eq]
    have heq : m-(1/(n:ℝ))*∑ i,X i omega=(1/(n:ℝ))*(-∑ i,Y i omega) := by
      simp only [Y,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul]
      field_simp
      ring
    rw [heq,one_div_mul_eq_div,le_div_iff₀ hnreal,mul_comm epsilon (n:ℝ)]
  have hexp : -((n:ℝ)*epsilon)^2/(2*((((n:ℝ≥0)/4):ℝ≥0):ℝ))=
      -2*(n:ℝ)*epsilon^2 := by
    push_cast
    field_simp
    ring
  rw [hexp] at htail
  rw [hset]
  exact htail

/-- Repeated independent validation gives confidence for the unknown Bernoulli parameter. -/
theorem bernoulli_upper_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0<n)
    (X : Fin n → Ω → ℝ) (p : unitInterval) (epsilon : ℝ) (he : 0≤epsilon)
    (hInd : iIndepFun X μ) (hm : ∀ i,Measurable (X i))
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    1-Real.exp (-2*(n:ℝ)*epsilon^2)≤
      μ.real {omega | (p:ℝ)≤(1/(n:ℝ))*∑ i,X i omega+epsilon} := by
  have hsum : Measurable (fun omega => ∑ i,X i omega) :=
    Finset.measurable_sum Finset.univ (fun i _ => hm i)
  have hbadMeas : MeasurableSet {omega | (1/(n:ℝ))*∑ i,X i omega+epsilon<(p:ℝ)} :=
    measurableSet_lt ((measurable_const.mul hsum).add_const epsilon) measurable_const
  have ht := bounded_independent_average_lower_tail μ n hn X p epsilon he hInd
    (fun i => (hm i).aemeasurable)
    (fun i => (bernoulli_support_mean μ (X i) p (hLaw i)).1)
    (fun i => (bernoulli_support_mean μ (X i) p (hLaw i)).2)
  have hbad := (measureReal_mono (μ := μ) (show
      {omega | (1/(n:ℝ))*∑ i,X i omega+epsilon<(p:ℝ)}⊆
        {omega | epsilon≤(p:ℝ)-(1/(n:ℝ))*∑ i,X i omega} by
          intro omega h;dsimp at h ⊢;linarith)).trans ht
  have hc := probReal_compl_eq_one_sub (μ := μ) hbadMeas
  have heq : {omega | (1/(n:ℝ))*∑ i,X i omega+epsilon<(p:ℝ)}ᶜ=
      {omega | (p:ℝ)≤(1/(n:ℝ))*∑ i,X i omega+epsilon} := by
    ext omega;simp
  rw [heq] at hc
  linarith

theorem validation_1000_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 1000 → Ω → ℝ)
    (p : unitInterval) (hInd : iIndepFun X μ) (hm : ∀ i,Measurable (X i))
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    19/20≤μ.real {omega | (p:ℝ)≤(1/1000)*∑ i,X i omega+
      Real.sqrt (Real.log 20/2000)} := by
  have hl : 0≤Real.log (20:ℝ)/2000 := by positivity
  have hs := Real.sq_sqrt hl
  have ht := bernoulli_upper_confidence μ 1000 (by omega) X p
    (Real.sqrt (Real.log 20/2000)) (Real.sqrt_nonneg _) hInd hm hLaw
  norm_num only [Nat.cast_ofNat] at ht
  have hex : Real.exp (-2000*Real.sqrt (Real.log 20/2000)^2)=1/20 := by
    rw [hs]
    have heq : -(2000:ℝ)*(Real.log 20/2000)=-Real.log 20 := by ring
    rw [heq,Real.exp_neg,Real.exp_log (by norm_num)]
    norm_num
  rw [hex] at ht
  norm_num only [one_sub_div] at ht
  convert ht using 1 <;> norm_num

/-- Zero failures is a concrete event, whose probability is derived from independence and laws. -/
theorem zero_failure_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : Fin n → Ω → ℝ)
    (p : unitInterval) (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    μ.real {omega | ∀ i,X i omega=0}=(1-(p:ℝ))^n := by
  classical
  have hfactor : ∀ i,(μ {omega | X i omega=0}).toReal=1-(p:ℝ) := by
    intro i
    have hmap := Measure.map_apply_of_aemeasurable (hLaw i).aemeasurable
      (measurableSet_singleton (0:ℝ))
    rw [(hLaw i).map_eq] at hmap
    change (bernoulliMeasure (1:ℝ) 0 p) {0}=μ {omega | X i omega=0} at hmap
    rw [← hmap]
    change (bernoulliMeasure (1:ℝ) 0 p).real {0}=1-(p:ℝ)
    simp [bernoulliMeasure_real_apply p (measurableSet_singleton (0:ℝ)),
      unitInterval.coe_symm_eq]
  have hset : {omega | ∀ i,X i omega=0}=⋂ i,{omega | X i omega=0} := by
    ext omega;simp
  have hprod := hInd.meas_iInter (s := fun i => {omega | X i omega=0})
    (fun i => (measurableSet_singleton (0:ℝ)).preimage (comap_measurable (X i)))
  change (μ {omega | ∀ i,X i omega=0}).toReal=_
  rw [hset,hprod,ENNReal.toReal_prod]
  simp_rw [hfactor]
  simp

theorem zero_failure_null_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : Fin n → Ω → ℝ)
    (p : unitInterval) (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ)
    (hnull : (1/100:ℝ)≤p) :
    μ.real {omega | ∀ i,X i omega=0}≤(99/100:ℝ)^n := by
  rw [zero_failure_probability μ n X p hInd hLaw]
  exact pow_le_pow_left₀ (sub_nonneg.mpr p.2.2) (by linarith) n

theorem zero_failure_299_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 299 → Ω → ℝ)
    (p : unitInterval) (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ)
    (hnull : (1/100:ℝ)≤p) : μ.real {omega | ∀ i,X i omega=0}≤1/20 := by
  apply (zero_failure_null_bound μ 299 X p hInd hLaw hnull).trans
  have hq := (SafeLearning.CoreAnalysis.validation_single_minimal 299).mpr (by omega)
  have hr : (((99/100:ℚ)^299):ℝ)≤((1/20:ℚ):ℝ) := by exact_mod_cast hq
  push_cast at hr
  exact hr

/-- Twenty predeclared controllers may be dependent; only each controller's trials are independent. -/
theorem twenty_zero_failure_false_accept_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 20 → Fin 597 → Ω → ℝ)
    (p : Fin 20 → unitInterval) (hInd : ∀ k,iIndepFun (X k) μ)
    (hLaw : ∀ k i,HasLaw (X k i) (bernoulliMeasure (1:ℝ) 0 (p k)) μ) :
    μ.real (⋃ k,{omega | (1/100:ℝ)≤p k ∧ ∀ i,X k i omega=0})≤1/20 := by
  have hf : ∀ k,μ.real {omega | (1/100:ℝ)≤p k ∧ ∀ i,X k i omega=0}≤1/400 := by
    intro k
    by_cases hp : (1/100:ℝ)≤p k
    · have ht := zero_failure_null_bound μ 597 (X k) (p k) (hInd k) (hLaw k) hp
      have hn : (99/100:ℝ)^597≤1/400 := by
        have hq := (SafeLearning.CoreAnalysis.validation_twenty_minimal 597).mpr (by omega)
        have hr : (((99/100:ℚ)^597):ℝ)≤((1/400:ℚ):ℝ) := by exact_mod_cast hq
        push_cast at hr
        exact hr
      simpa only [hp,true_and] using ht.trans hn
    · have he : {omega | (1/100:ℝ)≤p k ∧ ∀ i,X k i omega=0}=(∅:Set Ω) := by
        ext omega;simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false];tauto
      rw [he]
      norm_num
  have ht := (measureReal_iUnion_fintype_le (μ := μ)
    (fun k => {omega | (1/100:ℝ)≤p k ∧ ∀ i,X k i omega=0})).trans
      (Finset.sum_le_sum (fun k _ => hf k))
  norm_num at ht
  exact ht

end SafeLearning.CompleteAppliedValidation
