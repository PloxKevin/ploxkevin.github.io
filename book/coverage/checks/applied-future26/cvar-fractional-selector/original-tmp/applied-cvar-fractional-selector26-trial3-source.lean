import SafeLearning.CompleteAppliedFractionalTailDual
import Mathlib.Probability.CDF

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedCVaRQuantileExistence26

/-- Every real probability law, including laws with atoms and gaps, has an
attained quantile whose lower and upper CDF values bracket each interior level. -/
theorem actual_arbitrary_real_probability_has_an_attained_fractional_tail_threshold
    (P : Measure ℝ) [IsProbabilityMeasure P] (alpha : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ threshold : ℝ,
      Function.leftLim (cdf P) threshold ≤ alpha ∧ alpha ≤ cdf P threshold := by
  let upper : Set ℝ := {x | alpha ≤ cdf P x}
  obtain ⟨above, habove⟩ := ((tendsto_cdf_atTop P).eventually (eventually_gt_nhds ha1)).exists
  obtain ⟨below, hbelow⟩ := ((tendsto_cdf_atBot P).eventually (eventually_lt_nhds ha0)).exists
  have hnonempty : upper.Nonempty := ⟨above, habove.le⟩
  have hbounded : BddBelow upper := by
    refine ⟨below, ?_⟩
    intro x hx
    by_contra h
    have horder : x ≤ below := le_of_lt (lt_of_not_ge h)
    have hcdf := (monotone_cdf P) horder
    exact (not_le_of_gt hbelow) ((show alpha ≤ cdf P x from hx).trans hcdf)
  let threshold : ℝ := sInf upper
  have haboveroot : ∀ x : Ioi threshold, alpha ≤ cdf P x := by
    intro x
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hnonempty x.property
    exact (show alpha ≤ cdf P y from hy).trans ((monotone_cdf P) hyx.le)
  have hroot : alpha ≤ cdf P threshold := by
    letI : Nonempty (Ioi threshold) := ⟨⟨threshold + 1, by simp⟩⟩
    rw [← (cdf P).iInf_Ioi_eq threshold]
    exact le_ciInf haboveroot
  have hbelowroot : ∀ x : ℝ, x < threshold → cdf P x < alpha := by
    intro x hx
    by_contra h
    have hmember : x ∈ upper := le_of_not_gt h
    exact (not_le_of_gt hx) (csInf_le hbounded hmember)
  have hleft : Function.leftLim (cdf P) threshold ≤ alpha := by
    rw [(monotone_cdf P).leftLim_eq_sSup]
    apply csSup_le
    · exact ⟨cdf P (threshold - 1), ⟨threshold - 1, by simp, rfl⟩⟩
    · rintro y ⟨x, hx, rfl⟩
      exact (hbelowroot x hx).le
  exact ⟨threshold, hleft, hroot⟩

end SafeLearning.CompleteAppliedCVaRQuantileExistence26

namespace SafeLearning.CompleteAppliedCVaRFractionalSelector26
open CompleteAppliedFractionalTailDual CompleteFoundationsCVaRQuotients
open CompleteFoundationsHingeExpectations CompleteAppliedCVaRQuantileExistence26

/-- The fractional selector includes every strict-tail loss, exactly the necessary
fraction of an atom at its threshold, and none of the lower losses. -/
def fractionalSelector {Ω : Type*} (loss : Ω→ℝ) (q r : ℝ) : Ω→ℝ :=
  fun w=>if q<loss w then 1 else if loss w=q then r else 0

/-- A quantile of the genuine loss law brackets the desired tail mass. -/
theorem actual_arbitrary_loss_has_a_tail_mass_bracketing_threshold
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (loss : Ω→ℝ) (hm : Measurable loss) (alpha : ℝ) (ha0 : 0<alpha) (ha1 : alpha<1) :
    ∃q : ℝ,P.real {w | q<loss w}≤1-alpha ∧
      1-alpha≤P.real {w | q<loss w}+P.real {w | loss w=q} := by
  let law:=P.map loss
  letI : IsProbabilityMeasure law :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  obtain ⟨q,hleft,hupper⟩ :=
    actual_arbitrary_real_probability_has_an_attained_fractional_tail_threshold law alpha ha0 ha1
  have htail : law.real (Ioi q)=1-cdf law q := by
    rw [show Ioi q=(Iic q)ᶜ by ext x;simp,
      probReal_compl_eq_one_sub measurableSet_Iic,←cdf_eq_real law q]
  have hpoint : law.real {q}=cdf law q-Function.leftLim (cdf law) q := by
    have hraw : law {q}=ENNReal.ofReal (cdf law q-Function.leftLim (cdf law) q) := by
      calc
        law {q}=(cdf law).measure {q} := by rw [measure_cdf law]
        _ = ENNReal.ofReal (cdf law q-Function.leftLim (cdf law) q) :=
          StieltjesFunction.measure_singleton (cdf law) q
    rw [measureReal_def,hraw]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr ((monotone_cdf law).leftLim_le le_rfl))
  have ht : law.real (Ioi q)=P.real {w | q<loss w} := by
    simpa only [measureReal_def,Set.preimage,Set.mem_Ioi] using
      congrArg ENNReal.toReal (Measure.map_apply (μ:=P) hm (measurableSet_Ioi (a:=q)))
  have hb : law.real {q}=P.real {w | loss w=q} := by
    simpa only [measureReal_def,Set.preimage,Set.mem_singleton_iff] using
      congrArg ENNReal.toReal (Measure.map_apply (μ:=P) hm (measurableSet_singleton q))
  refine ⟨q,?_,?_⟩
  · rw [←ht,htail];linarith
  · rw [←ht,←hb,htail,hpoint];linarith

/-- The boundary fraction is valid even with no atom: then its numerator is zero. -/
theorem actual_boundary_fraction_is_in_unit_interval_and_mass_matched
    (mass above boundary : ℝ) (hb : 0≤boundary)
    (hu : above≤ mass) (hut : mass≤above+boundary) :
    (mass-above)/boundary∈Icc (0:ℝ) 1 ∧
      above+((mass-above)/boundary)*boundary=mass := by
  have hnum : 0≤ mass-above := sub_nonneg.mpr hu
  by_cases hzero : boundary=0
  · have hnumzero : mass-above=0 := by linarith
    simp [hzero,hnumzero]
    linarith
  · have hpos : 0<boundary := lt_of_le_of_ne hb (Ne.symm hzero)
    refine ⟨⟨div_nonneg hnum hb,(div_le_one hpos).mpr (by linarith)⟩,?_⟩
    rw [div_mul_cancel₀ _ hzero]
    ring

/-- Measurability and actual pointwise range hold for the constructed selector. -/
theorem actual_fractional_threshold_selector_measurable_and_bounded
    {Ω : Type*} [MeasurableSpace Ω] (loss : Ω→ℝ) (hm : Measurable loss)
    (q r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
    Measurable (fractionalSelector loss q r) ∧
      (∀w,fractionalSelector loss q r w∈Icc (0:ℝ) 1) ∧
      (∀w,q<loss w→fractionalSelector loss q r w=1) ∧
      (∀w,loss w<q→fractionalSelector loss q r w=0) := by
  have ha : MeasurableSet {w | q<loss w} := measurableSet_lt measurable_const hm
  have he : MeasurableSet {w | loss w=q} := measurableSet_eq_fun hm measurable_const
  refine ⟨measurable_const.ite ha (measurable_const.ite he measurable_const),?_,?_,?_⟩
  · intro w
    by_cases hqa : q<loss w
    · simp [fractionalSelector,hqa]
    · by_cases hqe : loss w=q
      · simpa [fractionalSelector,hqa,hqe] using hr
      · simp [fractionalSelector,hqa,hqe]
  · intro w hw;simp [fractionalSelector,hw]
  · intro w hw
    have hqa : ¬q<loss w := not_lt_of_ge hw.le
    have hqe : loss w≠q := ne_of_lt hw
    simp [fractionalSelector,hqa,hqe]

/-- The selector's integral is computed from the actual strict-tail and atom masses. -/
theorem actual_fractional_selector_integral_is_above_mass_plus_fractional_atom
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (loss : Ω→ℝ) (hm : Measurable loss) (q r : ℝ) :
    (∫w,fractionalSelector loss q r w ∂P)=
      P.real {w | q<loss w}+r*P.real {w | loss w=q} := by
  have ha : MeasurableSet {w | q<loss w} := measurableSet_lt measurable_const hm
  have he : MeasurableSet {w | loss w=q} := measurableSet_eq_fun hm measurable_const
  have hfun : fractionalSelector loss q r=
      fun w=>({w | q<loss w}.indicator (fun _=>(1:ℝ)) w)+
        ({w | loss w=q}.indicator (fun _=>r) w) := by
    funext w
    by_cases hqa : q<loss w
    · have hqe : loss w≠q := ne_of_gt hqa
      simp [fractionalSelector,hqa,hqe]
    · by_cases hqe : loss w=q
      · simp [fractionalSelector,hqa,hqe]
      · simp [fractionalSelector,hqa,hqe]
  rw [hfun,integral_add ((integrable_const (1:ℝ)).indicator ha)
    ((integrable_const r).indicator he),integral_indicator_const (1:ℝ) ha,integral_indicator_const r he]
  simp only [smul_eq_mul,one_mul]
  ring

/-- No mass-matched selector is assumed: it is constructed from an attained quantile,
including atomic distributions and the no-atom zero-boundary case. -/
theorem actual_arbitrary_measurable_loss_has_a_constructed_fractional_tail_selector
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (loss : Ω→ℝ) (hm : Measurable loss) (alpha : ℝ) (ha0 : 0<alpha) (ha1 : alpha<1) :
    ∃q : ℝ,let r:=(1-alpha-P.real {w | q<loss w})/P.real {w | loss w=q}
      fractionalSelector loss q r∈admissibleSelectors P (1-alpha) ∧
      (∀w,q<loss w→fractionalSelector loss q r w=1) ∧
      (∀w,loss w<q→fractionalSelector loss q r w=0) := by
  obtain ⟨q,hq0,hq1⟩:=actual_arbitrary_loss_has_a_tail_mass_bracketing_threshold
    P loss hm alpha ha0 ha1
  let r:=(1-alpha-P.real {w | q<loss w})/P.real {w | loss w=q}
  have hr:=actual_boundary_fraction_is_in_unit_interval_and_mass_matched
    (1-alpha) (P.real {w | q<loss w}) (P.real {w | loss w=q})
    measureReal_nonneg hq0 hq1
  have hs:=actual_fractional_threshold_selector_measurable_and_bounded loss hm q r hr.1
  refine ⟨q,⟨hs.1,hs.2.1,?_⟩,hs.2.2.1,hs.2.2.2⟩
  rw [actual_fractional_selector_integral_is_above_mass_plus_fractional_atom P loss hm q r]
  simpa only [mul_comm,r] using hr.2

/-- Every integrable real loss has both a genuine greatest fractional tail and an
attained global minimum of the RU objective, with equal values. -/
theorem actual_arbitrary_integrable_loss_has_greatest_tail_and_attained_least_RU
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (loss : Ω→ℝ) (hm : Measurable loss) (hi : Integrable loss P)
    (alpha : ℝ) (ha0 : 0<alpha) (ha1 : alpha<1) :
    ∃q : ℝ,∃selector : Ω→ℝ,
      selector∈admissibleSelectors P (1-alpha) ∧
      IsGreatest ((fun other=>actualTailMean P loss other (1-alpha)) '' admissibleSelectors P (1-alpha))
        (actualTailMean P loss selector (1-alpha)) ∧
      IsLeast (Set.range (actualRUObjective P loss alpha)) (actualRUObjective P loss alpha q) ∧
      actualWorstTailMean P loss (1-alpha)=actualRUObjective P loss alpha q := by
  obtain ⟨q,hs,habove,hbelow⟩:=actual_arbitrary_measurable_loss_has_a_constructed_fractional_tail_selector
    P loss hm alpha ha0 ha1
  let selector:=fractionalSelector loss q
    ((1-alpha-P.real {w | q<loss w})/P.real {w | loss w=q})
  have ho:=actual_mass_matched_threshold_selector_is_greatest_tail_and_least_RU_objective
    loss hi alpha q ha1 selector hs habove hbelow
  exact ⟨q,selector,hs,ho⟩

/-- The source's strict worst-five-percent criterion is equivalent to the attained
RU certificate for arbitrary integrable laws, not only finite distributions. -/
theorem actual_arbitrary_loss_worst_five_percent_below_ten_iff_RU_certificate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (loss : Ω→ℝ) (hm : Measurable loss) (hi : Integrable loss P) :
    actualWorstTailMean P loss (1/20)<10 ↔
      ∃q : ℝ,q+20*(∫w,hinge (loss w) q ∂P)<10 := by
  obtain ⟨q,selector,hs,hgreatest,hleast,heq⟩:=
    actual_arbitrary_integrable_loss_has_greatest_tail_and_attained_least_RU
      P loss hm hi (19/20) (by norm_num) (by norm_num)
  have hmass : (1-(19/20):ℝ)=1/20 := by norm_num
  have hru : ∀t,actualRUObjective P loss (19/20) t=
      t+20*(∫w,hinge (loss w) t ∂P) := by
    intro t;unfold actualRUObjective;norm_num
  rw [hmass] at heq
  constructor
  · intro h
    exact ⟨q,by rw [←hru,←heq];exact h⟩
  · rintro ⟨t,ht⟩
    rw [heq]
    exact lt_of_le_of_lt (hleast.2 ⟨t,rfl⟩) (by rw [hru];exact ht)

end SafeLearning.CompleteAppliedCVaRFractionalSelector26
