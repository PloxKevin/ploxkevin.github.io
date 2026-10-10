import SafeLearning.CompleteAppliedTailRisk
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedTailRiskSlopes
open MeasureTheory ProbabilityTheory Filter
open SafeLearning.CompleteAppliedTailRisk
open scoped Topology

theorem actual_tail_probability (nu : ℝ) :
    lossLaw.toMeasure.real {i | nu<lossValue i}=1-lossCDF nu := by
  have hm : MeasurableSet {i | lossValue i≤nu} :=
    measurableSet_Iic.preimage (measurable_of_finite lossValue)
  have he : {i | nu<lossValue i}={i | lossValue i≤nu}ᶜ := by
    ext i;simp
  rw [he,probReal_compl_eq_one_sub hm]
  rfl

theorem actual_tail_probabilities_on_intervals (nu : ℝ) :
    (nu<0 → lossLaw.toMeasure.real {i | nu<lossValue i}=1) ∧
    (nu ∈ Set.Ioo 0 10 → lossLaw.toMeasure.real {i | nu<lossValue i}=1/5) ∧
    (nu ∈ Set.Ioo 10 100 → lossLaw.toMeasure.real {i | nu<lossValue i}=1/20) ∧
    (100<nu → lossLaw.toMeasure.real {i | nu<lossValue i}=0) := by
  rw [actual_tail_probability,actual_loss_cdf]
  refine ⟨?_,?_,?_,?_⟩
  · intro h;simp [h]
  · intro h;norm_num [not_lt.mpr h.1.le,h.2]
  · intro h
    have h0 : ¬nu<0 := by linarith [h.1]
    norm_num [h0,not_lt.mpr h.1.le,h.2]
  · intro h
    have h0 : ¬nu<0 := by linarith
    have h10 : ¬nu<10 := by linarith
    have h100 : ¬nu<100 := by linarith
    simp [h0,h10,h100]

theorem actual_objective_derivative_below_zero (nu : ℝ) (hnu : nu<0) :
    HasDerivAt excessObjective (-9) nu := by
  have hd : HasDerivAt (fun z : ℝ => 65-9*z) (-9) nu := by
    convert ((hasDerivAt_id nu).const_mul (-9)).const_add 65 using 1
    · ext z;simp only [id_eq];ring
    · norm_num
  apply hd.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hnu] with z hz
  change z<0 at hz
  simp [actual_excess_objective_piecewise,le_of_lt hz]

theorem actual_objective_derivative_zero_ten (nu : ℝ) (hnu : nu ∈ Set.Ioo 0 10) :
    HasDerivAt excessObjective (-1) nu := by
  have hd : HasDerivAt (fun z : ℝ => 65-z) (-1) nu := by
    convert (hasDerivAt_id nu).neg.const_add 65 using 1
    all_goals first | rfl | norm_num | (ext z;simp only [id_eq,Pi.neg_apply];ring)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hnu.1 hnu.2] with z hz
  simp [actual_excess_objective_piecewise,not_le.mpr hz.1,le_of_lt hz.2]

theorem actual_objective_derivative_ten_hundred (nu : ℝ) (hnu : nu ∈ Set.Ioo 10 100) :
    HasDerivAt excessObjective (1/2) nu := by
  have hd : HasDerivAt (fun z : ℝ => 50+z/2) (1/2) nu := by
    exact ((hasDerivAt_id nu).div_const 2).const_add 50
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hnu.1 hnu.2] with z hz
  have h0 : ¬z≤0 := by linarith [hz.1]
  simp [actual_excess_objective_piecewise,h0,not_le.mpr hz.1,le_of_lt hz.2]

theorem actual_objective_derivative_above_hundred (nu : ℝ) (hnu : 100<nu) :
    HasDerivAt excessObjective 1 nu := by
  apply (hasDerivAt_id nu).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hnu] with z hz
  change (100:ℝ)<z at hz
  have h0 : ¬z≤0 := by linarith
  have h10 : ¬z≤10 := by linarith
  simp [actual_excess_objective_piecewise,h0,h10,not_le.mpr hz]

/-- The source derivative identity is established for the actual expectation away from atoms. -/
theorem actual_tail_derivative_identity (nu : ℝ) (h0 : nu≠0) (h10 : nu≠10) (h100 : nu≠100) :
    HasDerivAt excessObjective
      (1-10*lossLaw.toMeasure.real {i | nu<lossValue i}) nu := by
  obtain ⟨ht0,ht10,ht100,htAbove⟩ := actual_tail_probabilities_on_intervals nu
  by_cases hn0 : nu<0
  · rw [ht0 hn0]
    norm_num
    exact actual_objective_derivative_below_zero nu hn0
  · by_cases hn10 : nu<10
    · have hn : nu ∈ Set.Ioo 0 10 := ⟨lt_of_le_of_ne (le_of_not_gt hn0) h0.symm,hn10⟩
      rw [ht10 hn]
      norm_num
      exact actual_objective_derivative_zero_ten nu hn
    · by_cases hn100 : nu<100
      · have hn : nu ∈ Set.Ioo 10 100 := ⟨lt_of_le_of_ne (le_of_not_gt hn10) h10.symm,hn100⟩
        rw [ht100 hn]
        norm_num
        exact actual_objective_derivative_ten_hundred nu hn
      · have hn : 100<nu := lt_of_le_of_ne (le_of_not_gt hn100) h100.symm
        rw [htAbove hn]
        norm_num
        exact actual_objective_derivative_above_hundred nu hn

/-- The actual minimizer is a genuine nondifferentiable kink, with unequal one-sided derivatives. -/
theorem actual_objective_not_differentiable_at_minimum :
    ¬DifferentiableAt ℝ excessObjective 10 := by
  have hdL : HasDerivAt (fun z : ℝ => 65-z) (-1) 10 := by
    convert (hasDerivAt_id (10:ℝ)).neg.const_add 65 using 1
    all_goals first | rfl | norm_num | (ext z;simp only [id_eq,Pi.neg_apply];ring)
  have hdR : HasDerivAt (fun z : ℝ => 50+z/2) (1/2) 10 := by
    exact ((hasDerivAt_id (10:ℝ)).div_const 2).const_add 50
  have hL : HasDerivWithinAt excessObjective (-1) (Set.Iic 10) 10 := by
    apply hdL.hasDerivWithinAt.congr_of_eventuallyEq
    · have hp0 : ∀ᶠ z in 𝓝 (10:ℝ),0<z := Ioi_mem_nhds (by norm_num)
      have hp : ∀ᶠ z in 𝓝[Set.Iic (10:ℝ)] 10,0<z :=
        hp0.filter_mono nhdsWithin_le_nhds
      filter_upwards [hp,self_mem_nhdsWithin] with z hz0 hz10
      change z≤10 at hz10
      simp [actual_excess_objective_piecewise,not_le.mpr hz0,hz10]
    · norm_num [actual_excess_objective_piecewise]
  have hR : HasDerivWithinAt excessObjective (1/2) (Set.Ici 10) 10 := by
    apply hdR.hasDerivWithinAt.congr_of_eventuallyEq
    · have hp0 : ∀ᶠ z in 𝓝 (10:ℝ),z<100 := Iio_mem_nhds (by norm_num)
      have hp : ∀ᶠ z in 𝓝[Set.Ici (10:ℝ)] 10,z<100 :=
        hp0.filter_mono nhdsWithin_le_nhds
      filter_upwards [hp,self_mem_nhdsWithin] with z hz100 hz10
      change (10:ℝ)≤z at hz10
      by_cases heq : z=10
      · subst z;norm_num [actual_excess_objective_piecewise]
      · have h10' : ¬z≤10 := not_le.mpr (lt_of_le_of_ne hz10 (fun he => heq he.symm))
        have h0 : ¬z≤0 := by linarith
        simp [actual_excess_objective_piecewise,h0,h10',le_of_lt hz100]
    · norm_num [actual_excess_objective_piecewise]
  intro hd
  have heqL := (uniqueDiffWithinAt_Iic (10:ℝ)).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hL
  have heqR := (uniqueDiffWithinAt_Ici (10:ℝ)).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hR
  linarith

end SafeLearning.CompleteAppliedTailRiskSlopes
