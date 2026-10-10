import SafeLearning.CompleteAppliedProbabilityModel
import SafeLearning.CompleteAppliedConcentration
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedConfidence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

theorem finite_simultaneous_pass {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : I → Set Ω)
    (hm : ∀ i,MeasurableSet (failure i)) (budget : I → ℝ)
    (hb : ∀ i,μ.real (failure i)≤budget i) :
    1-(∑ i,budget i)≤μ.real (⋂ i,(failure i)ᶜ) := by
  have hu := (measureReal_iUnion_fintype_le (μ := μ) failure).trans
    (Finset.sum_le_sum (fun i _ => hb i))
  have hc := probReal_compl_eq_one_sub (μ := μ) (MeasurableSet.iUnion hm)
  rw [Set.compl_iUnion] at hc
  linarith

theorem three_checks_pass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : Fin 3 → Set Ω)
    (hm : ∀ i,MeasurableSet (failure i)) (hb : ∀ i,μ.real (failure i)≤1/100) :
    97/100≤μ.real (⋂ i,(failure i)ᶜ) := by
  have hh := finite_simultaneous_pass μ failure hm (fun _ => 1/100) hb
  norm_num at hh
  exact hh

def timeBudget (n : ℕ) : ℝ := (1/20)/(((n:ℝ)+1)*((n:ℝ)+2))

theorem time_budget_nonnegative (n : ℕ) : 0≤timeBudget n := by
  unfold timeBudget
  positivity

theorem time_budget_partial_sum (N : ℕ) :
    (∑ n ∈ Finset.range N,timeBudget n)=(1/20)*(1-1/((N:ℝ)+1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    unfold timeBudget
    push_cast
    have h1 : (N:ℝ)+1≠0 := by positivity
    have h2 : (N:ℝ)+2≠0 := by positivity
    field_simp
    ring

theorem time_budget_hasSum : HasSum timeBudget (1/20) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg time_budget_nonnegative (1/20)).mpr
  simp_rw [time_budget_partial_sum]
  have hh := (tendsto_const_nhds (x := (1:ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa using hh.const_mul (1/20:ℝ)

theorem all_time_failure_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : ℕ → Set Ω)
    (hb : ∀ n,μ (failure n)≤ENNReal.ofReal (timeBudget n)) :
    μ (⋃ n,failure n)≤(1/20:ℝ≥0∞) := by
  calc
    _≤∑' n : ℕ,μ (failure n) := measure_iUnion_le failure
    _≤∑' n : ℕ,ENNReal.ofReal (timeBudget n) := ENNReal.tsum_le_tsum hb
    _=ENNReal.ofReal (∑' n : ℕ,timeBudget n) :=
      (ENNReal.ofReal_tsum_of_nonneg time_budget_nonnegative time_budget_hasSum.summable).symm
    _=(1/20:ℝ≥0∞) := by
      rw [time_budget_hasSum.tsum_eq,ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num

theorem all_time_simultaneous_pass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : ℕ → Set Ω)
    (hm : ∀ n,MeasurableSet (failure n))
    (hb : ∀ n,μ (failure n)≤ENNReal.ofReal (timeBudget n)) :
    19/20≤μ.real (⋂ n,(failure n)ᶜ) := by
  have hh := ENNReal.toReal_mono (by norm_num : (1/20:ℝ≥0∞)≠∞)
    (all_time_failure_bound μ failure hb)
  change μ.real (⋃ n,failure n)≤(1/20:ℝ≥0∞).toReal at hh
  norm_num at hh
  have hc := probReal_compl_eq_one_sub (μ := μ) (MeasurableSet.iUnion hm)
  rw [Set.compl_iUnion] at hc
  linarith

theorem independent_fixed_failures_eventually {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : ℕ → Set Ω)
    (hm : ∀ n,MeasurableSet (failure n)) (hind : iIndepSet failure μ)
    (hp : ∀ n,μ.real (failure n)=1/20) : μ.real (⋃ n,failure n)=1 := by
  have hsmall : ∀ N : ℕ,μ.real (⋂ n,(failure n)ᶜ)≤(19/20:ℝ)^N := by
    intro N
    have hfinite := SafeLearning.CompleteAppliedProbabilityModel.independent_batch_failure μ N
      (fun i : Fin N => failure i.val) (1/20) (fun i => hm i.val)
      (hind.precomp Fin.val_injective) (fun i => hp i.val)
    have hc := probReal_compl_eq_one_sub (μ := μ)
      (MeasurableSet.iUnion (fun i : Fin N => hm i.val))
    rw [Set.compl_iUnion,hfinite] at hc
    have hs : (⋂ n,(failure n)ᶜ)⊆(⋂ i : Fin N,(failure i.val)ᶜ) := by
      intro omega h
      simp only [Set.mem_iInter] at h ⊢
      intro i
      exact h i.val
    have hh := measureReal_mono (μ := μ) hs
    rw [hc] at hh
    norm_num at hh
    exact hh
  have hz := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤19/20) (by norm_num : (19/20:ℝ)<1)
  have hzero : μ.real (⋂ n,(failure n)ᶜ)≤0 := ge_of_tendsto hz (Filter.Eventually.of_forall hsmall)
  have hc := probReal_compl_eq_one_sub (μ := μ) (MeasurableSet.iUnion hm)
  rw [Set.compl_iUnion] at hc
  linarith [measureReal_nonneg (μ := μ) (s := ⋂ n,(failure n)ᶜ)]

theorem exp_185_sample_bound : 2*Real.exp (-185/50:ℝ)≤1/20 := by
  have hb := Real.exp_bound (x := -(37/40:ℝ)) (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hb
  have hu : Real.exp (-(37/40:ℝ))≤39654/100000 := by linarith [(abs_le.mp hb).2]
  have hp := pow_le_pow_left₀ (Real.exp_nonneg (-(37/40:ℝ))) hu 4
  have he : Real.exp (-185/50:ℝ)=(Real.exp (-(37/40:ℝ)))^4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [he]
  norm_num at hp
  linarith

theorem exp_184_sample_failure : 1/20<2*Real.exp (-184/50:ℝ) := by
  have hb := Real.exp_bound (x := -(23/25:ℝ)) (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hb
  have hl : (39851/100000:ℝ)≤Real.exp (-(23/25:ℝ)) := by linarith [(abs_le.mp hb).1]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤39851/100000) hl 4
  have he : Real.exp (-184/50:ℝ)=(Real.exp (-(23/25:ℝ)))^4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [he]
  norm_num at hp
  linarith

theorem minimum_hoeffding_sample_count (N : ℕ) :
    2*Real.exp (-(N:ℝ)/50)≤1/20 ↔ 185≤N := by
  constructor
  · intro h
    by_contra hn
    have hn' : N≤184 := by omega
    have hnreal : (N:ℝ)≤184 := by exact_mod_cast hn'
    have he := Real.exp_le_exp.mpr (show (-184/50:ℝ)≤-(N:ℝ)/50 by linarith)
    linarith [exp_184_sample_failure]
  · intro h
    have hnreal : (185:ℝ)≤N := by exact_mod_cast h
    have he := Real.exp_le_exp.mpr (show -(N:ℝ)/50≤(-185/50:ℝ) by linarith)
    linarith [exp_185_sample_bound]

theorem hoeffding_185_actual_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 185 → Ω → ℝ) (m : ℝ)
    (hi : iIndepFun X μ) (hm : ∀ i,AEMeasurable (X i) μ)
    (hb : ∀ i,∀ᵐ omega ∂μ,X i omega ∈ Set.Icc (0:ℝ) 1)
    (hmean : ∀ i,(∫ omega,X i omega ∂μ)=m) :
    μ.real {omega | (1/10:ℝ)≤|(1/185)*∑ i,X i omega-m|}≤1/20 := by
  have hh := SafeLearning.CompleteAppliedConcentration.bounded_independent_average_hoeffding μ 185
    (by norm_num) X m (1/10) (by norm_num) hi hm hb hmean
  norm_num at hh
  have h185 := exp_185_sample_bound
  norm_num at h185
  exact hh.trans h185

theorem all_time_simultaneous_pass_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : ℕ → Set Ω)
    (hm : ∀ n,MeasurableSet (failure n)) (hb : ∀ n,μ.real (failure n)≤timeBudget n) :
    19/20≤μ.real (⋂ n,(failure n)ᶜ) := by
  apply all_time_simultaneous_pass μ failure hm
  intro n
  rw [← ENNReal.ofReal_toReal (by finiteness : μ (failure n)≠∞)]
  exact ENNReal.ofReal_le_ofReal (hb n)

theorem fixed_budget_sum (N : ℕ) : (∑ _n ∈ Finset.range N,(1/20:ℝ))=(N:ℝ)/20 := by
  simp [div_eq_mul_inv]

theorem fixed_budget_unbounded :
    Tendsto (fun N : ℕ => ∑ _n ∈ Finset.range N,(1/20:ℝ)) atTop atTop := by
  simp_rw [fixed_budget_sum,div_eq_mul_inv]
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (by norm_num)

theorem log40_enclosure : (36888794/10000000:ℝ)<Real.log 40 ∧
    Real.log 40<(36888795/10000000:ℝ) := by
  have hb1 := Real.exp_bound (x := -(36888794/40000000:ℝ)) (by norm_num)
    (n := 14) (by norm_num)
  have hb2 := Real.exp_bound (x := -(36888795/40000000:ℝ)) (by norm_num)
    (n := 14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hb1 hb2
  have hl : (397635368/1000000000:ℝ)≤Real.exp (-(36888794/40000000:ℝ)) := by
    linarith [(abs_le.mp hb1).1]
  have hu : Real.exp (-(36888795/40000000:ℝ))≤397635362/1000000000 := by
    linarith [(abs_le.mp hb2).2]
  have hpl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤397635368/1000000000) hl 4
  have hpu := pow_le_pow_left₀ (Real.exp_nonneg _) hu 4
  have hel : Real.exp (-(36888794/10000000:ℝ))=
      (Real.exp (-(36888794/40000000:ℝ)))^4 := by
    rw [← Real.exp_nat_mul];congr 1;norm_num
  have heu : Real.exp (-(36888795/10000000:ℝ))=
      (Real.exp (-(36888795/40000000:ℝ)))^4 := by
    rw [← Real.exp_nat_mul];congr 1;norm_num
  have hex : Real.exp (-Real.log (40:ℝ))=1/40 := by
    rw [Real.exp_neg,Real.exp_log (by norm_num)]
    norm_num
  have hllo : Real.exp (-Real.log (40:ℝ))<Real.exp (-(36888794/10000000:ℝ)) := by
    rw [hex,hel];norm_num at hpl;linarith
  have hupi : Real.exp (-(36888795/10000000:ℝ))<Real.exp (-Real.log (40:ℝ)) := by
    rw [hex,heu];norm_num at hpu;linarith
  have hlo := Real.exp_lt_exp.mp hllo
  have hhi := Real.exp_lt_exp.mp hupi
  constructor <;> linarith

theorem source_hoeffding_rounding :
    |50*Real.log (40:ℝ)-(18444397/100000:ℝ)|≤1/200000 := by
  obtain ⟨hl,hu⟩ := log40_enclosure
  rw [abs_le]
  constructor <;> linarith

end SafeLearning.CompleteAppliedConfidence
