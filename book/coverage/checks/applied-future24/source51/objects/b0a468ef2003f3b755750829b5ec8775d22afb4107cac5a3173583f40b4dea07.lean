import SafeLearning.CompleteAppliedValidationTests
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedZeroConfidence
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Exact inversion of the zero-failure binomial probability. -/
def zeroUpperLimit (n : ℕ) (delta : ℝ) : ℝ := 1-delta^((n:ℝ)⁻¹)

theorem zero_probability_inversion (n : ℕ) (hn : n≠0) (delta p : ℝ)
    (hdelta : 0≤delta) (hp : p∈Set.Icc 0 1) :
    (1-p)^n≤delta ↔ zeroUpperLimit n delta≤p := by
  have hbase : 0≤1-p := by linarith [hp.2]
  have hexp : 0<((n:ℝ)⁻¹) := by positivity
  have hh := Real.rpow_le_rpow_iff (pow_nonneg hbase n) hdelta hexp
  rw [Real.pow_rpow_inv_natCast hbase hn] at hh
  unfold zeroUpperLimit
  constructor
  · intro h
    have := hh.mpr h
    linarith
  · intro h
    apply hh.mp
    linarith

theorem zero_probability_strict_inversion (n : ℕ) (hn : n≠0) (delta p : ℝ)
    (hdelta : 0≤delta) (hp : p∈Set.Icc 0 1) :
    (1-p)^n<delta ↔ zeroUpperLimit n delta<p := by
  have hbase : 0≤1-p := by linarith [hp.2]
  have hexp : 0<((n:ℝ)⁻¹) := by positivity
  have hh := Real.rpow_lt_rpow_iff (pow_nonneg hbase n) hdelta hexp
  rw [Real.pow_rpow_inv_natCast hbase hn] at hh
  unfold zeroUpperLimit
  constructor
  · intro h
    have := hh.mpr h
    linarith
  · intro h
    apply hh.mp
    linarith

theorem zero_upper_mem_unit_interval (n : ℕ) (hn : n≠0) (delta : ℝ)
    (hd : delta∈Set.Icc 0 1) : zeroUpperLimit n delta∈Set.Icc 0 1 := by
  have hp := Real.rpow_nonneg hd.1 ((n:ℝ)⁻¹)
  have hle := Real.rpow_le_rpow hd.1 hd.2 (by positivity : 0≤((n:ℝ)⁻¹))
  rw [Real.one_rpow] at hle
  unfold zeroUpperLimit
  constructor <;> linarith

theorem zero_upper_boundary_equation (n : ℕ) (hn : n≠0) (delta : ℝ)
    (hd : 0≤delta) : (1-zeroUpperLimit n delta)^n=delta := by
  unfold zeroUpperLimit
  have he : 1-(1-delta^((n:ℝ)⁻¹))=delta^((n:ℝ)⁻¹) := by ring
  rw [he]
  exact Real.rpow_inv_natCast_pow hd hn

theorem zero_upper_unique_equation (n : ℕ) (hn : n≠0) (delta p : ℝ)
    (hd : 0≤delta) (hp : p∈Set.Icc 0 1) :
    (1-p)^n=delta ↔ p=zeroUpperLimit n delta := by
  constructor
  · intro h
    have hbase : 0≤1-p := by linarith [hp.2]
    have hh := congrArg (fun z:ℝ => z^((n:ℝ)⁻¹)) h
    rw [Real.pow_rpow_inv_natCast hbase hn] at hh
    unfold zeroUpperLimit
    linarith
  · intro h
    rw [h]
    exact zero_upper_boundary_equation n hn delta hd

/-- The reported limit is a statistic; the population parameter stays fixed. -/
def zeroOnlyUpperReport {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ)
    (delta : ℝ) (omega : Ω) : ℝ :=
  if ∀ i,X i omega=0 then zeroUpperLimit n delta else 1

theorem zero_report_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hm : ∀ i,Measurable (X i)) (delta : ℝ) :
    Measurable (zeroOnlyUpperReport n X delta) := by
  have hzero : MeasurableSet {omega | ∀ i,X i omega=0} := by
    have h : MeasurableSet (⋂ i,{omega | X i omega=0}) :=
      MeasurableSet.iInter (fun i => measurableSet_eq_fun (hm i) measurable_const)
    simpa only [Set.iInter_setOf] using h
  exact Measurable.ite hzero measurable_const measurable_const

/-- Repeated-data confidence for the explicit zero/nonzero reporting procedure. -/
theorem zero_report_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : n≠0)
    (X : Fin n → Ω → ℝ) (p : unitInterval) (delta : ℝ)
    (hd : delta∈Set.Icc 0 1) (hInd : iIndepFun X μ)
    (hm : ∀ i,Measurable (X i))
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    1-delta≤μ.real {omega | (p:ℝ)≤zeroOnlyUpperReport n X delta omega} := by
  by_cases hgood : (p:ℝ)≤zeroUpperLimit n delta
  · have he : {omega | (p:ℝ)≤zeroOnlyUpperReport n X delta omega}=Set.univ := by
      ext omega
      simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true]
      unfold zeroOnlyUpperReport
      split_ifs
      · exact hgood
      · exact p.2.2
    rw [he,probReal_univ]
    linarith [hd.1]
  · have hzero : MeasurableSet {omega | ∀ i,X i omega=0} := by
      have h : MeasurableSet (⋂ i,{omega | X i omega=0}) :=
        MeasurableSet.iInter (fun i => measurableSet_eq_fun (hm i) measurable_const)
      simpa only [Set.iInter_setOf] using h
    have he : {omega | (p:ℝ)≤zeroOnlyUpperReport n X delta omega}=
        {omega | ∀ i,X i omega=0}ᶜ := by
      ext omega
      simp only [Set.mem_setOf_eq,Set.mem_compl_iff]
      unfold zeroOnlyUpperReport
      split_ifs with hz
      · simp [hz,hgood]
      · simp [hz,p.2.2]
    rw [he,probReal_compl_eq_one_sub hzero]
    have hb := (zero_probability_inversion n hn delta p hd.1 p.2).mpr
      (le_of_lt (lt_of_not_ge hgood))
    rw [← SafeLearning.CompleteAppliedValidation.zero_failure_probability μ n X p hInd hLaw]
      at hb
    linarith

theorem proposed_rate_above_limit_rare_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : n≠0)
    (X : Fin n → Ω → ℝ) (p : unitInterval) (delta : ℝ)
    (hd : 0≤delta) (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ)
    (hp : zeroUpperLimit n delta<(p:ℝ)) :
    μ.real {omega | ∀ i,X i omega=0}<delta := by
  rw [SafeLearning.CompleteAppliedValidation.zero_failure_probability μ n X p hInd hLaw]
  exact (zero_probability_strict_inversion n hn delta p hd p.2).mpr hp

theorem hundred_run_exact_boundary :
    (1-zeroUpperLimit 100 (1/20))^100=(1/20:ℝ) ∧
    (∀ p:ℝ,p∈Set.Icc 0 1 →
      ((1-p)^100=(1/20:ℝ) ↔ p=1-(1/20:ℝ)^((100:ℝ)⁻¹))) := by
  constructor
  · exact zero_upper_boundary_equation 100 (by norm_num) (1/20) (by norm_num)
  · intro p hp
    exact zero_upper_unique_equation 100 (by norm_num) (1/20) p (by norm_num) hp

theorem hundred_run_upper_rounding :
    |zeroUpperLimit 100 (1/20)-(29513/1000000:ℝ)|≤1/2000000 := by
  have hlo : (59025/2000000:ℝ)≤zeroUpperLimit 100 (1/20) := by
    have hbad : ¬ (1-(59025/2000000:ℝ))^100≤(1/20:ℝ) := by norm_num
    exact le_of_lt (not_le.mp (fun h => hbad
      ((zero_probability_inversion 100 (by norm_num) (1/20) _
        (by norm_num) (by norm_num)).mpr h)))
  have hhi : zeroUpperLimit 100 (1/20)≤(59027/2000000:ℝ) :=
    (zero_probability_inversion 100 (by norm_num) (1/20) _
      (by norm_num) (by norm_num)).mp (by norm_num)
  rw [abs_le]
  constructor <;> linarith

theorem hundred_run_report_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 100 → Ω → ℝ)
    (p : unitInterval) (hInd : iIndepFun X μ) (hm : ∀ i,Measurable (X i))
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0 p) μ) :
    19/20≤μ.real {omega | (p:ℝ)≤zeroOnlyUpperReport 100 X (1/20) omega} := by
  convert zero_report_confidence μ 100 (by norm_num) X p (1/20)
    (by norm_num) hInd hm hLaw using 1 <;> norm_num

theorem hundred_run_zero_does_not_identify_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin 100 → Ω → ℝ)
    (hInd : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) (bernoulliMeasure (1:ℝ) 0
      SafeLearning.CompleteAppliedValidationTests.twoPercent) μ) :
    0<μ.real {omega | ∀ i,X i omega=0} ∧
    ∃ omega,(∀ i,X i omega=0) ∧
      (SafeLearning.CompleteAppliedValidationTests.twoPercent:ℝ)≠0 :=
  ⟨SafeLearning.CompleteAppliedValidationTests.positive_zero_failure_probability_at_two_percent
    μ 100 X hInd hLaw,
   SafeLearning.CompleteAppliedValidationTests.zero_failures_do_not_imply_zero_population
    μ 100 X hInd hLaw⟩

end SafeLearning.CompleteAppliedZeroConfidence
