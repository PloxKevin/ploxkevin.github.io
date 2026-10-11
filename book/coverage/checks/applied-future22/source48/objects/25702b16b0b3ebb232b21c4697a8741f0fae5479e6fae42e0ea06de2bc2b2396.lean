import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedMartingale
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

def fairSignLaw : Measure ℝ := bernoulliMeasure 1 (-1) ⟨1/2,by norm_num⟩
instance fairSignLaw_probability : IsProbabilityMeasure fairSignLaw := by
  unfold fairSignLaw
  infer_instance

def pastFiltration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (epsilon : ℕ → Ω → ℝ) (hm : ∀ i,Measurable (epsilon i)) : Filtration ℕ mΩ where
  seq n := ⨆ k ∈ {k : ℕ | k<n},MeasurableSpace.comap (epsilon k) inferInstance
  mono' i j hij := by
    exact iSup₂_le (fun k hk => le_iSup₂_of_le k (lt_of_lt_of_le hk hij) le_rfl)
  le' n := iSup₂_le (fun k _ => (hm k).comap_le)

def walk {Ω : Type*} (epsilon : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) : ℝ :=
  ∑ k ∈ Finset.range n,epsilon k omega

theorem walk_initial_and_step {Ω : Type*} (epsilon : ℕ → Ω → ℝ) (n : ℕ) :
    walk epsilon 0=0 ∧ walk epsilon (n+1)=walk epsilon n+epsilon n := by
  constructor
  · ext omega;simp [walk]
  · ext omega;simp [walk,Finset.sum_range_succ]

theorem walk_adapted {Ω : Type*} [MeasurableSpace Ω]
    (epsilon : ℕ → Ω → ℝ) (hm : ∀ i,Measurable (epsilon i)) :
    StronglyAdapted (pastFiltration epsilon hm) (walk epsilon) := by
  intro n
  have hs : StronglyMeasurable[pastFiltration epsilon hm n]
      (∑ k ∈ Finset.range n,epsilon k) := by
    apply Finset.stronglyMeasurable_sum
    intro k hk
    exact (comap_measurable (epsilon k)).stronglyMeasurable.mono
      (le_iSup₂_of_le k (Finset.mem_range.mp hk) le_rfl)
  change StronglyMeasurable[pastFiltration epsilon hm n] (fun omega => ∑ k ∈ Finset.range n,epsilon k omega)
  simpa only [Finset.sum_fn] using hs

theorem next_sign_independent_past {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (epsilon : ℕ → Ω → ℝ)
    (hm : ∀ i,Measurable (epsilon i)) (hi : iIndepFun epsilon μ) (n : ℕ) :
    Indep (MeasurableSpace.comap (epsilon n) inferInstance) (pastFiltration epsilon hm n) μ := by
  have hh : Indep (⨆ k ∈ ({n}:Set ℕ),MeasurableSpace.comap (epsilon k) inferInstance)
      (⨆ k ∈ {k : ℕ | k<n},MeasurableSpace.comap (epsilon k) inferInstance) μ :=
    indep_iSup_of_disjoint (fun k => (hm k).comap_le) hi (by simp)
  simpa [pastFiltration] using hh

theorem fair_sign_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (epsilon : Ω → ℝ) (hlaw : HasLaw epsilon fairSignLaw μ) :
    Integrable epsilon μ ∧ (∫ omega,epsilon omega ∂μ)=0 ∧
    (∀ᵐ omega ∂μ,|epsilon omega|=1) := by
  refine ⟨hlaw.integrable (integrable_bernoulliMeasure 1 (-1) ⟨1/2,by norm_num⟩ id),?_,?_⟩
  · rw [hlaw.integral_eq]
    norm_num [fairSignLaw,integral_bernoulliMeasure]
  · apply (hlaw.ae_iff (measurableSet_eq_fun measurable_id.abs measurable_const).mem).mpr
    unfold fairSignLaw
    rw [bernoulliMeasure_def,ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure
    all_goals norm_num [ae_dirac_eq]

theorem next_conditional_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : ℕ → Ω → ℝ)
    (hm : ∀ i,Measurable (epsilon i)) (hi : iIndepFun epsilon μ)
    (hlaw : ∀ i,HasLaw (epsilon i) fairSignLaw μ) (n : ℕ) :
    μ[epsilon n | pastFiltration epsilon hm n]=ᵐ[μ] 0 := by
  have hh := condExp_indep_eq (hm n).comap_le ((pastFiltration epsilon hm).le n)
    (comap_measurable (epsilon n)).stronglyMeasurable
    (next_sign_independent_past μ epsilon hm hi n)
  filter_upwards [hh] with omega homega
  simpa [(fair_sign_moments μ (epsilon n) (hlaw n)).2.1] using homega

theorem actual_fair_walk_martingale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : ℕ → Ω → ℝ)
    (hm : ∀ i,Measurable (epsilon i)) (hi : iIndepFun epsilon μ)
    (hlaw : ∀ i,HasLaw (epsilon i) fairSignLaw μ) :
    Martingale (walk epsilon) (pastFiltration epsilon hm) μ ∧
      (∀ n,Integrable (walk epsilon n) μ) ∧
      (∀ n,μ[walk epsilon (n+1) | pastFiltration epsilon hm n]=ᵐ[μ] walk epsilon n) ∧
      (∀ n,∀ᵐ omega ∂μ,|walk epsilon (n+1) omega-walk epsilon n omega|=1) := by
  have hint : ∀ n,Integrable (walk epsilon n) μ := by
    intro n
    exact integrable_finsetSum (Finset.range n)
      (fun i _ => (fair_sign_moments μ (epsilon i) (hlaw i)).1)
  have hmart : Martingale (walk epsilon) (pastFiltration epsilon hm) μ := by
    apply martingale_of_condExp_sub_eq_zero_nat (walk_adapted epsilon hm) hint
    intro n
    have he : walk epsilon (n+1)-walk epsilon n=epsilon n := by
      rw [(walk_initial_and_step epsilon n).2]
      abel
    rw [he]
    exact next_conditional_mean_zero μ epsilon hm hi hlaw n
  refine ⟨hmart,hint,fun n => hmart.2 n (n+1) (by omega),?_⟩
  intro n
  have hh := (fair_sign_moments μ (epsilon n) (hlaw n)).2.2
  simpa [(walk_initial_and_step epsilon n).2] using hh

def predictableMultiplier {Ω : Type*} (epsilon : ℕ → Ω → ℝ) (n : ℕ) (omega : Ω) : ℝ :=
  if 0≤walk epsilon n omega then 2 else 1

theorem multiplier_measurable_and_bound {Ω : Type*} [MeasurableSpace Ω]
    (epsilon : ℕ → Ω → ℝ) (hm : ∀ i,Measurable (epsilon i)) (n : ℕ) :
    StronglyMeasurable[pastFiltration epsilon hm n] (predictableMultiplier epsilon n) ∧
    (∀ omega,1≤predictableMultiplier epsilon n omega ∧ |predictableMultiplier epsilon n omega|≤2) := by
  constructor
  · have hs := (walk_adapted epsilon hm n).measurable
    exact (measurable_const.ite (measurableSet_le measurable_const hs)
      measurable_const).stronglyMeasurable
  · intro omega
    unfold predictableMultiplier
    split_ifs <;> norm_num

theorem actual_predictable_increment_zero_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (epsilon : ℕ → Ω → ℝ)
    (hm : ∀ i,Measurable (epsilon i)) (hi : iIndepFun epsilon μ)
    (hlaw : ∀ i,HasLaw (epsilon i) fairSignLaw μ) (n : ℕ) :
    μ[predictableMultiplier epsilon n*epsilon n | pastFiltration epsilon hm n]=ᵐ[μ] 0 ∧
    (∀ᵐ omega ∂μ,|(predictableMultiplier epsilon n*epsilon n) omega|≤2) := by
  have hm' := multiplier_measurable_and_bound epsilon hm n
  have hb : ∀ᵐ omega ∂μ,‖predictableMultiplier epsilon n omega‖≤2 :=
    Eventually.of_forall (fun omega => by simpa [Real.norm_eq_abs] using (hm'.2 omega).2)
  have hp := condExp_stronglyMeasurable_mul_of_bound ((pastFiltration epsilon hm).le n)
    hm'.1 (fair_sign_moments μ (epsilon n) (hlaw n)).1 2 hb
  constructor
  · exact hp.trans (by
      filter_upwards [next_conditional_mean_zero μ epsilon hm hi hlaw n] with omega hh
      simp [hh])
  · filter_upwards [(fair_sign_moments μ (epsilon n) (hlaw n)).2.2] with omega hh
    simp only [Pi.mul_apply,abs_mul,hh,mul_one]
    exact (hm'.2 omega).2

end SafeLearning.CompleteAppliedMartingale
