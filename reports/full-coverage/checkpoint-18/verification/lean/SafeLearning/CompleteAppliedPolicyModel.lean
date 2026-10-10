import SafeLearning.CompleteAppliedPolicy
import SafeLearning.CompleteAppliedReturns
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedPolicyModel
open MeasureTheory ProbabilityTheory
open SafeLearning.CompleteAppliedPolicy
open scoped ENNReal NNReal

def wornReadyProbability (wear : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => 1-wear*wornReadyProbability wear n

theorem worn_tail (wear : ℝ) (n : ℕ) :
    wornReadyProbability wear (n+1)=readyProbability wear n := by
  induction n with
  | zero => simp [wornReadyProbability,readyProbability]
  | succ n ih =>
    change 1-wear*wornReadyProbability wear (n+1)=1-wear*readyProbability wear n
    rw [ih]

def wornProductionReturn (p rho : ℝ) : ℝ :=
  ∑' n : ℕ, (4/5:ℝ)^n*((2+2*p)*wornReadyProbability (rho*p) n)
def wornMaintenanceReturn (p rho : ℝ) : ℝ :=
  ∑' n : ℕ, (4/5:ℝ)^n*(1-wornReadyProbability (rho*p) n)

theorem worn_production_semantics (p rho : ℝ) (hw : rho*p ∈ Set.Icc 0 1) :
    wornProductionReturn p rho=(4/5)*productionReturn p rho := by
  have hs : Summable (fun n => (4/5:ℝ)^n*((2+2*p)*readyProbability (rho*p) n)) := by
    convert (discounted_ready_summable (rho*p) hw).mul_left (2+2*p) using 1
    ext n; ring
  have hh := hs.hasSum.mul_left (4/5:ℝ)
  change HasSum _ ((4/5)*productionReturn p rho) at hh
  have ht : HasSum (fun n : ℕ => (4/5:ℝ)^(n+1)*((2+2*p)*wornReadyProbability (rho*p) (n+1)))
      ((4/5)*productionReturn p rho) := by
    convert hh using 1; ext n; rw [worn_tail,pow_succ]; ring
  have hf := HasSum.zero_add (f := fun n : ℕ => (4/5:ℝ)^n*((2+2*p)*wornReadyProbability (rho*p) n)) ht
  simpa [wornProductionReturn,wornReadyProbability] using hf.tsum_eq

theorem worn_maintenance_semantics (p rho : ℝ) (hw : rho*p ∈ Set.Icc 0 1) :
    wornMaintenanceReturn p rho=1+(4/5)*maintenanceReturn p rho := by
  have hs : Summable (fun n => (4/5:ℝ)^n*(1-readyProbability (rho*p) n)) := by
    simp_rw [mul_sub,mul_one]
    exact (summable_geometric_of_abs_lt_one (by norm_num : |(4/5:ℝ)| < 1)).sub
      (discounted_ready_summable (rho*p) hw)
  have hh := hs.hasSum.mul_left (4/5:ℝ)
  change HasSum _ ((4/5)*maintenanceReturn p rho) at hh
  have ht : HasSum (fun n : ℕ => (4/5:ℝ)^(n+1)*(1-wornReadyProbability (rho*p) (n+1)))
      ((4/5)*maintenanceReturn p rho) := by
    convert hh using 1; ext n; rw [worn_tail,pow_succ]; ring
  have hf := HasSum.zero_add (f := fun n : ℕ => (4/5:ℝ)^n*(1-wornReadyProbability (rho*p) n)) ht
  simpa [wornMaintenanceReturn,wornReadyProbability] using hf.tsum_eq

def stationaryLaw : PMF (Fin 2) := PMF.ofFintype
  (fun i => ((![(36/41:ℝ≥0),5/41] : Fin 2 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])
def readyTransition : PMF (Fin 2) := PMF.ofFintype
  (fun i => ((![(31/36:ℝ≥0),5/36] : Fin 2 → ℝ≥0) i : ℝ≥0∞))
  (by norm_cast; norm_num [Fin.sum_univ_succ])
def stationaryKernel (state : Fin 2) : PMF (Fin 2) :=
  if state=0 then readyTransition else PMF.pure 0

theorem stationary_law_preserved : stationaryLaw.bind stationaryKernel=stationaryLaw := by
  ext i
  fin_cases i <;> norm_num [PMF.bind_apply,stationaryLaw,stationaryKernel,readyTransition,
    tsum_fintype,Fin.sum_univ_succ,PMF.pure_apply]
  all_goals apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  all_goals simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv]
  all_goals norm_num

def stationaryMarginal : ℕ → PMF (Fin 2)
  | 0 => stationaryLaw
  | n+1 => (stationaryMarginal n).bind stationaryKernel

theorem stationary_marginals (n : ℕ) : stationaryMarginal n=stationaryLaw := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stationaryMarginal,ih,stationary_law_preserved]

theorem stationary_one_shift_expectations :
    (∫ i, (if i=(1:Fin 2) then (1:ℝ) else 0) ∂stationaryLaw.toMeasure)=5/41 ∧
    (∫ i, (if i=(0:Fin 2) then (28/9:ℝ) else 0) ∂stationaryLaw.toMeasure)=112/41 := by
  norm_num [PMF.integral_eq_sum,stationaryLaw,Fin.sum_univ_succ,smul_eq_mul]

/-- These joint-event equations encode precisely the local ready→worn and worn→ready
transition rules. They do not assume the desired stationary marginals. -/
theorem stationary_worn_events {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Set Ω)
    (hm : ∀ n, MeasurableSet (W n)) (h0 : μ.real (W 0)=5/41)
    (hwear : ∀ n, μ.real (W (n+1) ∩ (W n)ᶜ)=μ.real (W n)ᶜ*(5/36))
    (hrepair : ∀ n, μ.real (W (n+1) ∩ W n)=0) :
    ∀ n, μ.real (W n)=5/41 := by
  intro n; induction n with
  | zero => exact h0
  | succ n ih =>
    have hh := measureReal_inter_add_sdiff (μ := μ) (s := W (n+1)) (hm n)
    rw [Set.sdiff_eq,hrepair n,hwear n] at hh
    have hc := measureReal_add_measureReal_compl (μ := μ) (hm n)
    have hu : μ.real Set.univ=1 := by simp [measureReal_def]
    rw [hu,ih] at hc
    linarith

theorem stationary_twenty_repairs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Set Ω)
    (hm : ∀ n, MeasurableSet (W n)) (h0 : μ.real (W 0)=5/41)
    (hwear : ∀ n, μ.real (W (n+1) ∩ (W n)ᶜ)=μ.real (W n)ᶜ*(5/36))
    (hrepair : ∀ n, μ.real (W (n+1) ∩ W n)=0) :
    (∫ omega, ∑ n ∈ Finset.range 20, (W n).indicator (fun _ => (1:ℝ)) omega ∂μ)=100/41 := by
  rw [integral_finsetSum]
  · simp_rw [integral_indicator_const (1:ℝ) (hm _),smul_eq_mul,mul_one,
      stationary_worn_events μ W hm h0 hwear hrepair]
    norm_num
  · intro n hn
    exact (integrable_const (1:ℝ)).indicator (hm n)

theorem ready_production_pathwise_return {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (production : ℕ → Ω → ℝ) (p rho : ℝ)
    (hm : ∀ n, AEStronglyMeasurable (production n) μ)
    (hb : ∀ n, ∀ᵐ omega ∂μ, |production n omega| ≤ 4)
    (he : ∀ n, (∫ omega, production n omega ∂μ)=(2+2*p)*readyProbability (rho*p) n) :
    (∫ omega, ∑' n : ℕ, (4/5:ℝ)^n*production n omega ∂μ)=productionReturn p rho := by
  rw [SafeLearning.CompleteAppliedReturns.discounted_expectation_interchange μ production (4/5) 4
    (by norm_num) hm hb]
  simp_rw [he]
  rfl

theorem ready_maintenance_pathwise_return {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Set Ω) (p rho : ℝ)
    (hm : ∀ n, MeasurableSet (W n))
    (he : ∀ n, μ.real (W n)=1-readyProbability (rho*p) n) :
    (∫ omega, ∑' n : ℕ, (4/5:ℝ)^n*(W n).indicator (fun _ => (1:ℝ)) omega ∂μ)=
      maintenanceReturn p rho := by
  rw [SafeLearning.CompleteAppliedReturns.discounted_expectation_interchange μ
    (fun n => (W n).indicator (fun _ => (1:ℝ))) (4/5) 1 (by norm_num)
    (fun n => (stronglyMeasurable_const.indicator (hm n)).aestronglyMeasurable) (by
      intro n; filter_upwards [] with omega
      by_cases h : omega ∈ W n <;> simp [h])]
  simp_rw [integral_indicator_const (1:ℝ) (hm _),smul_eq_mul,mul_one,he]
  rfl

end SafeLearning.CompleteAppliedPolicyModel
