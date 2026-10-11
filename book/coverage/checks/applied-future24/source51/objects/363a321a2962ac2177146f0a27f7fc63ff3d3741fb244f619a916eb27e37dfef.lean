import SafeLearning.CompleteAppliedValidation

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SafeLearning.CompleteLyapunovValidationConfidence

def radius (factor delta : ℝ) (n : ℕ) : ℝ := Real.sqrt (Real.log (factor/delta)/(2*n))
def average {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) (w : Ω) : ℝ := (1/(n:ℝ))*∑ i, X i w

theorem genuine_exact_hoeffding_exponent (factor delta : ℝ) (n : ℕ)
    (hn : 0 < n) (hd : 0 < delta) (hf : delta ≤ factor) :
    Real.exp (-2*(n:ℝ)*radius factor delta n ^ 2) = delta/factor := by
  have hfac : 0 < factor := hd.trans_le hf
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 1 ≤ factor/delta := (le_div_iff₀ hd).mpr (by simpa using hf)
  have hs : radius factor delta n ^ 2 = Real.log (factor/delta)/(2*n) :=
    Real.sq_sqrt (div_nonneg (Real.log_nonneg hq) (by positivity))
  rw [hs]
  have heq : -2*(n:ℝ)*(Real.log (factor/delta)/(2*n)) = -Real.log (factor/delta) := by
    field_simp
  rw [heq,Real.exp_neg,Real.exp_log (div_pos hfac hd)]
  field_simp

theorem genuine_one_sided_acceptance_guarantee {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0<n)
    (X : Fin n → Ω → ℝ) (p : unitInterval) (delta critical : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (hInd : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i))
    (hLaw : ∀ i, HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    1-delta ≤ μ.real {w | (average n X w + radius 1 delta n ≤ 1-critical) →
      critical ≤ 1-(p:ℝ)} := by
  have h := SafeLearning.CompleteAppliedValidation.bernoulli_upper_confidence
    μ n hn X p (radius 1 delta n) (Real.sqrt_nonneg _) hInd hm hLaw
  rw [genuine_exact_hoeffding_exponent 1 delta n hn hd hd1,div_one] at h
  exact h.trans (measureReal_mono (μ := μ) (by
    intro w hw hp
    change (p:ℝ) ≤ average n X w + radius 1 delta n at hw
    linarith))

theorem genuine_two_sided_acceptance_guarantee {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0<n)
    (X : Fin n → Ω → ℝ) (p : unitInterval) (delta critical : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (hInd : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i))
    (hLaw : ∀ i, HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    1-delta ≤ μ.real {w | (average n X w + radius 2 delta n ≤ 1-critical) →
      critical ≤ 1-(p:ℝ)} := by
  have ht := SafeLearning.CompleteAppliedConcentration.bounded_independent_average_hoeffding
    μ n hn X p (radius 2 delta n) (Real.sqrt_nonneg _) hInd (fun i => (hm i).aemeasurable)
    (fun i => (SafeLearning.CompleteAppliedValidation.bernoulli_support_mean μ (X i) p (hLaw i)).1)
    (fun i => (SafeLearning.CompleteAppliedValidation.bernoulli_support_mean μ (X i) p (hLaw i)).2)
  rw [genuine_exact_hoeffding_exponent 2 delta n hn hd (by linarith)] at ht
  have hsum : Measurable (average n X) := measurable_const.mul
    (Finset.measurable_sum Finset.univ (fun i _ => hm i))
  have hbad : MeasurableSet {w | radius 2 delta n ≤ |average n X w-(p:ℝ)|} :=
    measurableSet_le measurable_const ((hsum.sub_const p).abs)
  have hc := probReal_compl_eq_one_sub (μ := μ) hbad
  have hgood : 1-delta ≤ μ.real {w | |average n X w-(p:ℝ)| < radius 2 delta n} := by
    have heq : {w | radius 2 delta n ≤ |average n X w-(p:ℝ)|}ᶜ =
        {w | |average n X w-(p:ℝ)| < radius 2 delta n} := by ext w; simp
    rw [heq] at hc
    change μ.real {w | radius 2 delta n ≤ |average n X w-(p:ℝ)|} ≤ 2*(delta/2) at ht
    linarith
  exact hgood.trans (measureReal_mono (μ := μ) (by
    intro w hw hp
    change |average n X w-(p:ℝ)| < radius 2 delta n at hw
    have ha := (abs_lt.mp hw).1
    linarith))

theorem literal_source_one_and_two_sided_radii (n : ℕ) :
    radius 2 (1/100) n = Real.sqrt (Real.log 200/(2*n)) ∧
    radius 1 (1/100) n = Real.sqrt (Real.log 100/(2*n)) ∧
    radius 2 (1/500) n = Real.sqrt (Real.log 1000/(2*n)) := by
  norm_num [radius]

end SafeLearning.CompleteLyapunovValidationConfidence
