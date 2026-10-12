import SafeLearning.CompleteAppliedConfidence
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedGridConfidence
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem grid_log_threshold (N : ℝ) :
    2*Real.exp (-N/50)≤1/200 ↔ 50*Real.log 400≤N := by
  have he : Real.exp (-Real.log (400:ℝ))=1/400 := by
    rw [Real.exp_neg,Real.exp_log (by norm_num)]
    norm_num
  have hh : 2*Real.exp (-N/50)≤1/200 ↔ Real.exp (-N/50)≤1/400 := by
    constructor <;> intro h <;> linarith
  rw [hh,← he,Real.exp_le_exp]
  constructor <;> intro h <;> linarith

theorem log400_enclosure : (5991464/1000000:ℝ)<Real.log 400 ∧
    Real.log 400<(5991465/1000000:ℝ) := by
  have hb1 := Real.exp_bound (x := -(5991464/8000000:ℝ)) (by norm_num)
    (n := 16) (by norm_num)
  have hb2 := Real.exp_bound (x := -(5991465/8000000:ℝ)) (by norm_num)
    (n := 16) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hb1 hb2
  have hl : (472870836/1000000000:ℝ)≤Real.exp (-(5991464/8000000:ℝ)) := by
    linarith [(abs_le.mp hb1).1]
  have hu : Real.exp (-(5991465/8000000:ℝ))≤472870778/1000000000 := by
    linarith [(abs_le.mp hb2).2]
  have hpl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤472870836/1000000000) hl 8
  have hpu := pow_le_pow_left₀ (Real.exp_nonneg _) hu 8
  have hel : Real.exp (-(5991464/1000000:ℝ))=
      (Real.exp (-(5991464/8000000:ℝ)))^8 := by
    rw [← Real.exp_nat_mul];congr 1;norm_num
  have heu : Real.exp (-(5991465/1000000:ℝ))=
      (Real.exp (-(5991465/8000000:ℝ)))^8 := by
    rw [← Real.exp_nat_mul];congr 1;norm_num
  have hex : Real.exp (-Real.log (400:ℝ))=1/400 := by
    rw [Real.exp_neg,Real.exp_log (by norm_num)]
    norm_num
  have hllo : Real.exp (-Real.log (400:ℝ))<Real.exp (-(5991464/1000000:ℝ)) := by
    rw [hex,hel];norm_num at hpl;linarith
  have hupi : Real.exp (-(5991465/1000000:ℝ))<Real.exp (-Real.log (400:ℝ)) := by
    rw [hex,heu];norm_num at hpu;linarith
  have hlo := Real.exp_lt_exp.mp hllo
  have hhi := Real.exp_lt_exp.mp hupi
  constructor <;> linarith

theorem grid_sample_minimum (N : ℕ) :
    2*Real.exp (-(N:ℝ)/50)≤1/200 ↔ 300≤N := by
  rw [grid_log_threshold]
  obtain ⟨hl,hu⟩ := log400_enclosure
  constructor
  · intro h
    by_contra hn
    have hn' : N≤299 := by omega
    have hnreal : (N:ℝ)≤299 := by exact_mod_cast hn'
    linarith
  · intro h
    have hnreal : (300:ℝ)≤N := by exact_mod_cast h
    linarith

theorem grid_rounding :
    |50*Real.log (400:ℝ)-(2995732/10000:ℝ)|≤1/20000 := by
  obtain ⟨hl,hu⟩ := log400_enclosure
  rw [abs_le]
  constructor <;> linarith

theorem ten_actual_mean_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 10 → Fin 300 → Ω → ℝ)
    (m : Fin 10 → ℝ) (hi : ∀ k,iIndepFun (X k) μ)
    (hm : ∀ k i,Measurable (X k i))
    (hb : ∀ k i,∀ᵐ omega ∂μ,X k i omega ∈ Set.Icc (0:ℝ) 1)
    (hmean : ∀ k i,(∫ omega,X k i omega ∂μ)=m k) :
    19/20≤μ.real (⋂ k,{omega | |(1/300)*∑ i,X k i omega-m k|<1/10}) := by
  let F : Fin 10 → Set Ω := fun k =>
    {omega | (1/10:ℝ)≤|(1/300)*∑ i,X k i omega-m k|}
  have hF : ∀ k,MeasurableSet (F k) := by
    intro k
    dsimp [F]
    apply measurableSet_le measurable_const
    have hsum : Measurable (fun omega => ∑ i,X k i omega) :=
      Finset.measurable_sum Finset.univ (fun i _ => hm k i)
    exact ((measurable_const.mul hsum).sub_const (m k)).abs
  have hfail : ∀ k,μ.real (F k)≤1/200 := by
    intro k
    have hh := SafeLearning.CompleteAppliedConcentration.bounded_independent_average_hoeffding
      μ 300 (by norm_num) (X k) (m k) (1/10) (by norm_num) (hi k) (fun i => (hm k i).aemeasurable) (hb k) (hmean k)
    have h300 := (grid_sample_minimum 300).mpr (by omega)
    norm_num at hh h300
    exact hh.trans h300
  have hpass := SafeLearning.CompleteAppliedConfidence.finite_simultaneous_pass
    μ F hF (fun _ => 1/200) hfail
  norm_num at hpass
  convert hpass using 1
  congr 1
  ext omega
  simp [F,not_le]

theorem ten_pointwise_only {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (failure : Fin 10 → Set Ω)
    (hm : ∀ k,MeasurableSet (failure k)) (hb : ∀ k,μ.real (failure k)≤1/20) :
    1/2≤μ.real (⋂ k,(failure k)ᶜ) := by
  have hh := SafeLearning.CompleteAppliedConfidence.finite_simultaneous_pass
    μ failure hm (fun _ => 1/20) hb
  norm_num at hh
  exact hh

end SafeLearning.CompleteAppliedGridConfidence
