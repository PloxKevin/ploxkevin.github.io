import Mathlib
import SafeLearning.CompleteLyapunovConvexIntervalRisk26

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteLyapunovScalarLinearScenarioRisk26
open CompleteLyapunovConvexIntervalRisk26 CompleteLyapunovScenarioContinuousRisk23

def orientedSet (a : ℝ) (S : Set ℝ) : Set ℝ := {y | y/a∈S}

/-- An invertible scalar objective transforms actual convex constraints to convex intervals. -/
theorem actual_linear_objective_constraint_orientation_preserves_convexity
    (a : ℝ) (S : Set ℝ) (hS : Convex ℝ S) : Convex ℝ (orientedSet a S) := by
  simpa [orientedSet,div_eq_mul_inv,mul_comm] using
    hS.linear_preimage (a⁻¹ • (LinearMap.id : ℝ→ₗ[ℝ]ℝ))

/-- An actual attained singleton linear-cost minimizer becomes an actual least scalar coordinate. -/
theorem actual_linear_objective_singleton_minimizer_becomes_least
    (a : ℝ) (ha : a≠0) (domain S : Set ℝ) (one : ℝ)
    (hmem : one∈domain∩S)
    (hmin : ∀x∈domain∩S,a*one≤a*x) :
    IsLeast (orientedSet a domain∩orientedSet a S) (a*one) := by
  constructor
  · simpa [orientedSet,ha] using hmem
  · intro y hy
    have h := hmin (y/a) ⟨hy.1,hy.2⟩
    simpa [ha] using h

/-- The actual optimizer of any nonzero scalar linear objective, with either sign,
    inherits the derived optimized scenario-risk law. -/
theorem actual_iid_nonzero_scalar_linear_convex_program_risk_bound
    {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (law : Measure Θ) [IsProbabilityMeasure law] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (ha : a≠0) (domain : Set ℝ) (C : Θ→Set ℝ) (one : Θ→ℝ)
    (hmeas : Measurable one) (hconv : ∀t,Convex ℝ (C t))
    (hmem : ∀t,one t∈domain∩C t)
    (hmin : ∀t,∀x∈domain∩C t,a*one t≤a*x)
    (n : ℕ) [NeZero n]
    (hJoint : ∀(s : Fin n→Θ)(t : Θ),∃x∈domain,(∀i,x∈C (s i))∧x∈C t)
    (X : Fin n→Ω→Θ) (hm : ∀i,Measurable (X i))
    (hind : iIndepFun X P) (hlaw : ∀i,HasLaw (X i) law P)
    (epsilon : ℝ) (he : epsilon∈Icc (0:ℝ) 1) :
    P.real {w | epsilon<actualViolation law C
      (sampleMaximum n (fun i=>a*one (X i w))/a)} ≤ (1-epsilon)^n := by
  have ho : ∀t,IsLeast (orientedSet a domain∩orientedSet a (C t)) (a*one t) :=
    fun t=>actual_linear_objective_singleton_minimizer_becomes_least a ha domain
      (C t) (one t) (hmem t) (hmin t)
  have hj : ∀(s : Fin n→Θ)(t : Θ),∃y∈orientedSet a domain,
      (∀i,y∈orientedSet a (C (s i)))∧y∈orientedSet a (C t) := by
    intro s t
    obtain ⟨x,hxd,hxs,hxt⟩:=hJoint s t
    exact ⟨a*x,by simpa [orientedSet,ha] using hxd,
      fun i=>by simpa [orientedSet,ha] using hxs i,
      by simpa [orientedSet,ha] using hxt⟩
  have hc : ∀t,Convex ℝ (orientedSet a (C t)) :=
    fun t=>actual_linear_objective_constraint_orientation_preserves_convexity a (C t) (hconv t)
  have hr:=actual_iid_general_convex_interval_optimizer_risk_bound law P
    (orientedSet a domain) (fun t=>orientedSet a (C t)) (fun t=>a*one t)
    (measurable_const.mul hmeas) hc ho n hj X hm hind hlaw epsilon he
  simpa only [actualViolation,orientedSet] using hr

/-- The normalized coordinate is genuinely a feasible global linear-cost optimizer. -/
theorem actual_scalar_linear_program_optimizer_feasible_and_global
    {Θ : Type*} (a : ℝ) (ha : a≠0) (domain : Set ℝ)
    (C : Θ→Set ℝ) (one : Θ→ℝ) (hconv : ∀t,Convex ℝ (C t))
    (hmem : ∀t,one t∈domain∩C t)
    (hmin : ∀t,∀x∈domain∩C t,a*one t≤a*x)
    (n : ℕ) [NeZero n]
    (hJoint : ∀(s : Fin n→Θ)(t : Θ),∃x∈domain,(∀i,x∈C (s i))∧x∈C t)
    (s : Fin n→Θ) :
    let opt := sampleMaximum n (fun i=>a*one (s i))/a
    opt∈actualSampledFeasible domain C n s ∧
      ∀x∈actualSampledFeasible domain C n s,a*opt≤a*x := by
  have ho : ∀t,IsLeast (orientedSet a domain∩orientedSet a (C t)) (a*one t) :=
    fun t=>actual_linear_objective_singleton_minimizer_becomes_least a ha domain
      (C t) (one t) (hmem t) (hmin t)
  have hj : ∀(s : Fin n→Θ)(t : Θ),∃y∈orientedSet a domain,
      (∀i,y∈orientedSet a (C (s i)))∧y∈orientedSet a (C t) := by
    intro s t
    obtain ⟨x,hxd,hxs,hxt⟩:=hJoint s t
    exact ⟨a*x,by simpa [orientedSet,ha] using hxd,
      fun i=>by simpa [orientedSet,ha] using hxs i,
      by simpa [orientedSet,ha] using hxt⟩
  have hp:=actual_general_interval_program_optimizer_is_the_maximum_single_optimizer
    (orientedSet a domain) (fun t=>orientedSet a (C t)) (fun t=>a*one t)
    (fun t=>actual_linear_objective_constraint_orientation_preserves_convexity a (C t) (hconv t))
    ho n hj s
  refine ⟨hp.1,?_⟩
  intro x hx
  have h:=hp.2 (x:=a*x) ⟨by simpa [orientedSet,ha] using hx.1,
    fun i=>by simpa [orientedSet,ha] using hx.2 i⟩
  simpa [ha] using h

/-- A zero linear objective with the scenario uniqueness hypothesis has no fresh risk:
    uniqueness forces every jointly feasible value to equal the singleton optimizer. -/
theorem actual_zero_objective_unique_program_has_zero_fresh_risk
    {Θ : Type*} [MeasurableSpace Θ] (law : Measure Θ)
    (domain : Set ℝ) (C : Θ→Set ℝ) (one : Θ→ℝ)
    (hunique : ∀t,∀x∈domain∩C t,x=one t)
    (n : ℕ) [NeZero n]
    (hJoint : ∀(s : Fin n→Θ)(t : Θ),∃x∈domain,(∀i,x∈C (s i))∧x∈C t)
    (s : Fin n→Θ) : actualViolation law C (one (s 0))=0 := by
  have hgood : ∀t,one (s 0)∈C t := by
    intro t
    obtain ⟨x,hxd,hxs,hxt⟩:=hJoint s t
    have hx:=hunique (s 0) x ⟨hxd,hxs 0⟩
    simpa [←hx] using hxt
  have hempty : {t | one (s 0)∉C t}=(∅ : Set Θ) := by
    ext t
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    exact not_not_intro (hgood t)
  simp [actualViolation,hempty]


/-- The fixed common-law CDF upper region has at least epsilon mass, including atoms. -/
theorem actual_single_optimizer_upper_region_has_mass_at_least_epsilon
    {Θ : Type*} [MeasurableSpace Θ] (law : Measure Θ) [IsProbabilityMeasure law]
    (one : Θ→ℝ) (hmeas : Measurable one) (epsilon : ℝ) (he : epsilon≤1) :
    epsilon≤law.real {t | 1-epsilon≤cdf (law.map one) (one t)} := by
  letI : IsProbabilityMeasure (law.map one) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).mpr inferInstance
  have hc : Measurable (cdf (law.map one)) := (monotone_cdf (law.map one)).measurable
  have hset : MeasurableSet {x : ℝ | cdf (law.map one) x<1-epsilon} :=
    measurableSet_lt hc measurable_const
  have hm:=Measure.map_apply (μ:=law) hmeas hset
  have hp:=actual_arbitrary_cdf_strict_lower_probability_bound (law.map one)
    (1-epsilon) (by linarith)
  have hA : MeasurableSet {t | cdf (law.map one) (one t)<1-epsilon} :=
    hset.preimage hmeas
  have hr : law.real {t | cdf (law.map one) (one t)<1-epsilon}≤1-epsilon := by
    change (law (one ⁻¹' {x : ℝ | cdf (law.map one) x<1-epsilon})).toReal≤_
    rw [←hm]
    exact hp
  have heq : {t | 1-epsilon≤cdf (law.map one) (one t)}=
      {t | cdf (law.map one) (one t)<1-epsilon}ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,not_lt]
  rw [heq,probReal_compl_eq_one_sub hA]
  linarith

/-- Exceeding the optimized violation threshold is exactly all scenarios missing
    that fixed epsilon-mass CDF upper region, not an assumed miss probability. -/
theorem actual_optimized_interval_risk_event_iff_every_sample_misses_upper_region
    {Θ Ω : Type*} [MeasurableSpace Θ] (law : Measure Θ) [IsProbabilityMeasure law]
    (domain : Set ℝ) (C : Θ→Set ℝ) (one : Θ→ℝ) (hmeas : Measurable one)
    (hconv : ∀t,Convex ℝ (C t)) (hOne : ∀t,IsLeast (domain∩C t) (one t))
    (n : ℕ) [NeZero n]
    (hJoint : ∀(s : Fin n→Θ)(t : Θ),∃x∈domain,(∀i,x∈C (s i))∧x∈C t)
    (X : Fin n→Ω→Θ) (epsilon : ℝ) :
    {w | epsilon<actualViolation law C (sampleMaximum n (fun i=>one (X i w)))}=
      {w | ∀i,X i w∉{t | 1-epsilon≤cdf (law.map one) (one t)}} := by
  letI : IsProbabilityMeasure (law.map one) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).mpr inferInstance
  have heq : {w | epsilon<actualViolation law C
      (sampleMaximum n (fun i=>one (X i w)))}=
      {w | epsilon<violation (law.map one) (sampleMaximum n (fun i=>one (X i w)))} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    rw [actual_interval_optimized_risk_equals_the_cdf_tail law domain C one hmeas
      hconv hOne n hJoint (fun i=>X i w),
      actual_fresh_constraint_violation_is_one_minus_its_cdf]
  rw [heq,actual_optimized_violation_event_is_all_cdf_coordinates_below_threshold]
  ext w
  simp only [Set.mem_iInter,Set.mem_ofPred_eq,not_le]

end SafeLearning.CompleteLyapunovScalarLinearScenarioRisk26
