import SafeLearning.CompleteAppliedCoverageContinuousTransform
import SafeLearning.CompleteFoundationsExponentialLesson

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SafeLearning.CompleteLyapunovScenarioContinuousRisk23

def sampleMaximum (n : ℕ) [NeZero n] (s : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty s

def violation (law : Measure ℝ) (x : ℝ) : ℝ := law.real (Ioi x)

theorem actual_lower_bound_scalar_program_has_unique_attained_optimizer
    (n : ℕ) [NeZero n] (s : Fin n → ℝ) :
    IsLeast {x : ℝ | ∀ i, s i ≤ x} (sampleMaximum n s) ∧
      ∀ x, IsLeast {x : ℝ | ∀ i, s i ≤ x} x → x=sampleMaximum n s := by
  classical
  have h : IsLeast {x : ℝ | ∀ i, s i ≤ x} (sampleMaximum n s) := by
    constructor
    · intro i
      exact Finset.le_sup' s (Finset.mem_univ i)
    · intro x hx
      exact (Finset.sup'_le_iff Finset.univ_nonempty s).mpr (fun i _=>hx i)
  exact ⟨h,fun x hx=>hx.unique h⟩

theorem actual_fresh_constraint_violation_is_one_minus_its_cdf
    (law : Measure ℝ) [IsProbabilityMeasure law] (x : ℝ) :
    violation law x=1-cdf law x := by
  rw [violation,show Ioi x=(Iic x)ᶜ by ext y;simp,
    probReal_compl_eq_one_sub measurableSet_Iic,←cdf_eq_real law x]

theorem actual_monotone_cdf_commutes_with_the_scalar_optimizer
    (law : Measure ℝ) (n : ℕ) [NeZero n] (s : Fin n → ℝ) :
    cdf law (sampleMaximum n s)=sampleMaximum n (fun i=>cdf law (s i)) := by
  classical
  unfold sampleMaximum
  exact Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty (cdf law)
    (fun x y=>(monotone_cdf law).map_sup x y)

theorem actual_optimized_violation_event_is_all_cdf_coordinates_below_threshold
    {Ω : Type*} (law : Measure ℝ) [IsProbabilityMeasure law]
    (n : ℕ) [NeZero n] (X : Fin n → Ω → ℝ) (epsilon : ℝ) :
    {w | epsilon<violation law (sampleMaximum n (fun i=>X i w))}=
      ⋂ i, {w | cdf law (X i w)<1-epsilon} := by
  classical
  ext w
  rw [Set.mem_setOf_eq,actual_fresh_constraint_violation_is_one_minus_its_cdf,
    actual_monotone_cdf_commutes_with_the_scalar_optimizer]
  have he : epsilon<1-sampleMaximum n (fun i=>cdf law (X i w)) ↔
      sampleMaximum n (fun i=>cdf law (X i w))<1-epsilon := by constructor <;> intro h <;> linarith
  rw [he]
  simp only [sampleMaximum,Finset.sup'_lt_iff,Set.mem_iInter,Set.mem_setOf_eq,
    Finset.mem_univ,forall_const]

theorem actual_iid_continuous_scalar_optimizer_has_exact_violation_tail_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (law : Measure ℝ) [IsProbabilityMeasure law] (hc : Continuous (cdf law))
    (n : ℕ) [NeZero n] (X : Fin n → Ω → ℝ)
    (hm : ∀ i,Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i,HasLaw (X i) law P) (epsilon : ℝ)
    (he : epsilon∈Icc (0:ℝ) 1) :
    P.real {w | epsilon<violation law (sampleMaximum n (fun i=>X i w))}=
      (1-epsilon)^n := by
  let Y : Fin n → Ω → ℝ := fun i w=>cdf law (X i w)
  have hpit:=CompleteAppliedCoverageContinuousTransform.actual_continuous_cdf_probability_integral_transform_has_the_true_uniform_law law hc
  have hi : iIndepFun Y P:=hind.comp (fun _=>cdf law) (fun _=>hc.measurable)
  have hl : ∀ i,HasLaw (Y i) (CompleteAppliedUniformDefinitions.actualUniformLaw 0 1) P:=
    fun i=>hpit.comp (hlaw i)
  have ht : 1-epsilon∈Icc (0:ℝ) 1 := by constructor <;> linarith [he.1,he.2]
  have hp : ∀ i,P.real {w | Y i w<1-epsilon}=1-epsilon := by
    intro i
    exact ((hl i).measureReal_eq measurableSet_Iio).trans
      (CompleteAppliedCoverageUniformLaw.actual_unit_uniform_strict_cdf (1-epsilon) ht)
  have hprod := hi.meas_iInter (s:=fun i=>{w | Y i w<1-epsilon})
    (fun i=>measurableSet_Iio.preimage (comap_measurable (Y i)))
  have hr:=congrArg ENNReal.toReal hprod
  simp only [ENNReal.toReal_prod] at hr
  change P.real (⋂ i,{w | Y i w<1-epsilon})=_ at hr
  simp_rw [←measureReal_def,hp] at hr
  rw [actual_optimized_violation_event_is_all_cdf_coordinates_below_threshold]
  simpa only [Y,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hr

theorem actual_continuous_scalar_scenario_budget_bounds_the_optimized_risk_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (law : Measure ℝ) [IsProbabilityMeasure law] (hc : Continuous (cdf law))
    (n : ℕ) [NeZero n] (X : Fin n → Ω → ℝ)
    (hm : ∀ i,Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i,HasLaw (X i) law P) (epsilon beta : ℝ)
    (he : epsilon∈Icc (0:ℝ) 1) (hb : (1-epsilon)^n≤beta) :
    P.real {w | epsilon<violation law (sampleMaximum n (fun i=>X i w))}≤beta ∧
      P.real {w | epsilon<violation law (sampleMaximum n (fun i=>X i w))}≤
        Real.exp (-epsilon*n) := by
  rw [actual_iid_continuous_scalar_optimizer_has_exact_violation_tail_probability
    P law hc n X hm hind hlaw epsilon he]
  exact ⟨hb,CompleteFoundationsExponentialLesson.actual_independent_miss_probability_expression_has_exponential_upper_bound
    epsilon he.1 he.2 n⟩

end SafeLearning.CompleteLyapunovScenarioContinuousRisk23
