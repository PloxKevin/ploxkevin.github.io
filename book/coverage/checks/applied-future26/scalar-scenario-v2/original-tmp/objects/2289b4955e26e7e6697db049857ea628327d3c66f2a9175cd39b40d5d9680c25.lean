import Mathlib
import SafeLearning.CompleteLyapunovScenarioContinuousRisk23

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteLyapunovConvexIntervalRisk26
open CompleteLyapunovScenarioContinuousRisk23

/-- The CDF of an arbitrary law, including atoms, is stochastically no smaller than uniform. -/
theorem actual_arbitrary_cdf_strict_lower_probability_bound
    (law : Measure ℝ) [IsProbabilityMeasure law] (t : ℝ) (ht : 0≤t) :
    law.real {x | cdf law x<t} ≤ t := by
  have hm : Measurable (cdf law) := (monotone_cdf law).measurable
  have hA : MeasurableSet {x | cdf law x<t} := measurableSet_lt hm measurable_const
  have hb : law {x | cdf law x<t} ≤ ENNReal.ofReal t := by
    rw [hA.measure_eq_iSup_isCompact law]
    refine iSup_le (fun K => iSup_le (fun hK => iSup_le (fun hcompact => ?_)))
    by_cases hn : K.Nonempty
    · obtain ⟨x,hmax⟩ := hcompact.exists_isGreatest hn
      have hx : cdf law x<t := hK hmax.1
      calc
        law K ≤ law (Iic x) := measure_mono (fun y hy => hmax.2 hy)
        _ = ENNReal.ofReal (cdf law x) := (ofReal_cdf law x).symm
        _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal hx.le
    · simp [Set.not_nonempty_iff_eq_empty.mp hn]
  have h := ENNReal.toReal_mono (by finiteness) hb
  simpa only [←measureReal_def,ENNReal.toReal_ofReal ht] using h

def actualSampledFeasible {Θ : Type*} (domain : Set ℝ) (C : Θ→Set ℝ)
    (n : ℕ) (s : Fin n→Θ) : Set ℝ := {x | x∈domain ∧ ∀i,x∈C (s i)}

def actualViolation {Θ : Type*} [MeasurableSpace Θ]
    (law : Measure Θ) (C : Θ→Set ℝ) (x : ℝ) : ℝ := law.real {t | x∉C t}

/-- General convex interval constraints, not just sampled lower-bound half-lines.
Attainment is required for the actual one-constraint programs; all augmented finite
instances are feasible, as supplied by the scenario-program domain assumptions. -/
theorem actual_general_interval_program_optimizer_is_the_maximum_single_optimizer
    {Θ : Type*} (domain : Set ℝ) (C : Θ→Set ℝ) (one : Θ→ℝ)
    (hconv : ∀t,Convex ℝ (C t))
    (hOne : ∀t,IsLeast (domain∩C t) (one t))
    (n : ℕ) [NeZero n]
    (hJoint : ∀(s : Fin n→Θ)(t : Θ),∃x∈domain,(∀i,x∈C (s i))∧x∈C t)
    (s : Fin n→Θ) :
    IsLeast (actualSampledFeasible domain C n s)
      (sampleMaximum n (fun i=>one (s i))) := by
  classical
  let m := sampleMaximum n (fun i=>one (s i))
  obtain ⟨z,hzd,hzs,_⟩ := hJoint s (s 0)
  have hmz : m≤z := by
    exact (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
      (fun i _ => (hOne (s i)).2 ⟨hzd,hzs i⟩)
  have hlow : ∀i,one (s i)≤ m := fun i=>Finset.le_sup' _ (Finset.mem_univ i)
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i=>one (s i))
  have him : m=one (s i) := hi
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [him];exact (hOne (s i)).1.1
  · intro j
    exact (hconv (s j)).ordConnected.out (hOne (s j)).1.2 (hzs j) ⟨hlow j,hmz⟩
  · intro x hx
    exact (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
      (fun j _=>(hOne (s j)).2 ⟨hx.1,hx.2 j⟩)

/-- Actual fresh-constraint violation is a strict lower-optimizer tail, even when
individual convex constraints have both an upper and a lower boundary. -/
theorem actual_general_interval_fresh_violation_iff_single_optimizer_above
    {Θ : Type*} (domain : Set ℝ) (C : Θ→Set ℝ) (one : Θ→ℝ)
    (hconv : ∀t,Convex ℝ (C t))
    (hOne : ∀t,IsLeast (domain∩C t) (one t))
    (n : ℕ) [NeZero n]
    (hJoint : ∀(s : Fin n→Θ)(t : Θ),∃x∈domain,(∀i,x∈C (s i))∧x∈C t)
    (s : Fin n→Θ) (t : Θ) :
    sampleMaximum n (fun i=>one (s i))∉C t ↔
      sampleMaximum n (fun i=>one (s i))<one t := by
  let m := sampleMaximum n (fun i=>one (s i))
  have hopt := actual_general_interval_program_optimizer_is_the_maximum_single_optimizer
    domain C one hconv hOne n hJoint s
  have hmd : m∈domain := hopt.1.1
  constructor
  · intro hnot
    by_contra hn
    have hlo : one t≤ m := le_of_not_gt hn
    obtain ⟨z,hzd,hzs,hzt⟩ := hJoint s t
    have hmz : m≤z := hopt.2 ⟨hzd,hzs⟩
    exact hnot ((hconv t).ordConnected.out (hOne t).1.2 hzt ⟨hlo,hmz⟩)
  · intro hlt hmem
    exact (not_le_of_gt hlt) ((hOne t).2 ⟨hmd,hmem⟩)

/-- The actual optimized convex program's risk is derived from its generated
single-constraint optimizer law, without a postulated risk distribution. -/
theorem actual_interval_optimized_risk_equals_the_cdf_tail
    {Θ : Type*} [MeasurableSpace Θ] (law : Measure Θ) [IsProbabilityMeasure law]
    (domain : Set ℝ) (C : Θ→Set ℝ) (one : Θ→ℝ) (hMeas : Measurable one)
    (hconv : ∀t,Convex ℝ (C t))
    (hOne : ∀t,IsLeast (domain∩C t) (one t))
    (n : ℕ) [NeZero n]
    (hJoint : ∀(s : Fin n→Θ)(t : Θ),∃x∈domain,(∀i,x∈C (s i))∧x∈C t)
    (s : Fin n→Θ) :
    actualViolation law C (sampleMaximum n (fun i=>one (s i)))=
      1-cdf (law.map one) (sampleMaximum n (fun i=>one (s i))) := by
  haveI : IsProbabilityMeasure (law.map one) := (Measure.isProbabilityMeasure_map_iff hMeas.aemeasurable).mpr inferInstance
  have he : {t | sampleMaximum n (fun i=>one (s i))∉C t}=
      one ⁻¹' Ioi (sampleMaximum n (fun i=>one (s i))) := by
    ext t
    exact actual_general_interval_fresh_violation_iff_single_optimizer_above
      domain C one hconv hOne n hJoint s t
  rw [actualViolation,he]
  have hmap := Measure.map_apply hMeas (measurableSet_Ioi (a:=sampleMaximum n (fun i=>one (s i))))
  change (law (one ⁻¹' Ioi (sampleMaximum n (fun i=>one (s i))))).toReal=_
  rw [←hmap]
  exact actual_fresh_constraint_violation_is_one_minus_its_cdf (law.map one) _

/-- The one-dimensional optimized scenario-risk bound for arbitrary common laws.
Atoms only improve the inequality; continuity is not assumed. -/
theorem actual_iid_general_convex_interval_optimizer_risk_bound
    {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (law : Measure Θ) [IsProbabilityMeasure law]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (domain : Set ℝ) (C : Θ→Set ℝ) (one : Θ→ℝ) (hMeas : Measurable one)
    (hconv : ∀t,Convex ℝ (C t))
    (hOne : ∀t,IsLeast (domain∩C t) (one t))
    (n : ℕ) [NeZero n]
    (hJoint : ∀(s : Fin n→Θ)(t : Θ),∃x∈domain,(∀i,x∈C (s i))∧x∈C t)
    (X : Fin n→Ω→Θ) (hm : ∀i,Measurable (X i))
    (hind : iIndepFun X P) (hlaw : ∀i,HasLaw (X i) law P)
    (epsilon : ℝ) (he : epsilon∈Icc (0:ℝ) 1) :
    P.real {w | epsilon<actualViolation law C
      (sampleMaximum n (fun i=>one (X i w)))} ≤ (1-epsilon)^n := by
  haveI : IsProbabilityMeasure (law.map one) := (Measure.isProbabilityMeasure_map_iff hMeas.aemeasurable).mpr inferInstance
  let Y : Fin n→Ω→ℝ := fun i w=>one (X i w)
  have hY : iIndepFun Y P := hind.comp (fun _=>one) (fun _=>hMeas)
  have hYL : ∀i,HasLaw (Y i) (law.map one) P := by
    intro i
    exact (show HasLaw one (law.map one) law from ⟨hMeas.aemeasurable,rfl⟩).comp (hlaw i)
  have hcdf : Measurable (cdf (law.map one)) := (monotone_cdf (law.map one)).measurable
  let Z : Fin n→Ω→ℝ := fun i w=>cdf (law.map one) (Y i w)
  have hZ : iIndepFun Z P := hY.comp (fun _=>cdf (law.map one)) (fun _=>hcdf)
  have hp : ∀i,P.real {w | Z i w<1-epsilon} ≤ 1-epsilon := by
    intro i
    have hl := ((show HasLaw (cdf (law.map one))
        ((law.map one).map (cdf (law.map one))) (law.map one) from
        ⟨hcdf.aemeasurable,rfl⟩).comp (hYL i)).measureReal_eq measurableSet_Iio
    change P.real {w | Z i w<1-epsilon}=
      ((law.map one).map (cdf (law.map one))).real (Iio (1-epsilon)) at hl
    rw [hl]
    have hmap := Measure.map_apply hcdf (measurableSet_Iio (a:=1-epsilon))
    change (((law.map one).map (cdf (law.map one))) (Iio (1-epsilon))).toReal≤_
    rw [hmap]
    exact actual_arbitrary_cdf_strict_lower_probability_bound (law.map one)
      (1-epsilon) (by linarith [he.2])
  have hevent : {w | epsilon<actualViolation law C
      (sampleMaximum n (fun i=>one (X i w)))}=⋂i,{w | Z i w<1-epsilon} := by
    have heq : {w | epsilon<actualViolation law C
        (sampleMaximum n (fun i=>one (X i w)))}=
        {w | epsilon<violation (law.map one) (sampleMaximum n (fun i=>Y i w))} := by
      ext w
      simp only [Set.mem_setOf_eq]
      rw [actual_interval_optimized_risk_equals_the_cdf_tail law domain C one hMeas
        hconv hOne n hJoint (fun i=>X i w),
        actual_fresh_constraint_violation_is_one_minus_its_cdf]
    rw [heq,actual_optimized_violation_event_is_all_cdf_coordinates_below_threshold]
  have hprod := hZ.meas_iInter (s:=fun i=>{w | Z i w<1-epsilon})
    (fun i=>measurableSet_Iio.preimage (comap_measurable (Z i)))
  have hr := congrArg ENNReal.toReal hprod
  simp only [ENNReal.toReal_prod] at hr
  change P.real (⋂i,{w | Z i w<1-epsilon})=∏i,P.real {w | Z i w<1-epsilon} at hr
  rw [hevent,hr]
  calc
    _ ≤ ∏_i : Fin n,(1-epsilon) := Finset.prod_le_prod₀
      (fun i _=>measureReal_nonneg) (fun i _=>hp i)
    _ = (1-epsilon)^n := by simp

end SafeLearning.CompleteLyapunovConvexIntervalRisk26
