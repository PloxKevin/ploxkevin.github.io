import SafeLearning.CompleteAppliedTemperatureSoftmax
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter MeasureTheory InformationTheory
open scoped BigOperators ENNReal NNReal Topology
namespace SafeLearning.CompleteModulesViabilityEntropyWhole30
open SafeLearning.CompleteAppliedFiniteEntropy SafeLearning.CompleteAppliedInformation
open SafeLearning.CompleteAppliedFiniteKLSupport SafeLearning.CompleteAppliedTemperatureSoftmax

variable {X : Type*} {m : ℕ} [NeZero m]

def actualViable (next : X → Fin m → X) (failure : Set X) : Set X :=
  {x | ∃ (state : ℕ → X) (action : ℕ → Fin m), state 0 = x ∧
    (∀ n, state (n+1) = next (state n) (action n)) ∧
    ∀ n, state (n+1) ∉ failure}

def viableActions (next : X → Fin m → X) (failure : Set X) (x : X) : Finset (Fin m) :=
  by
  classical
  exact Finset.univ.filter (fun a => next x a ∈ actualViable next failure)

def stationaryRun (next : X → Fin m → X) (policy : X → Fin m) (x : X) : ℕ → X
  | 0 => x
  | n+1 => next (stationaryRun next policy x n) (policy (stationaryRun next policy x n))

theorem actual_viable_path_has_a_viable_and_immediately_safe_first_successor
    (next : X → Fin m → X) (failure : Set X) (x : X)
    (hx : x ∈ actualViable next failure) :
    ∃ a, next x a ∈ actualViable next failure ∧ next x a ∉ failure := by
  rcases hx with ⟨s,a,hs,hnext,hsafe⟩
  refine ⟨a 0, ?_, ?_⟩
  · refine ⟨(fun n => s (n+1)), (fun n => a (n+1)), ?_, ?_, ?_⟩
    · simpa [hs] using hnext 0
    · intro n
      exact hnext (n+1)
    · intro n
      exact hsafe (n+1)
  · rw [← hs, ← hnext 0]
    exact hsafe 0

theorem actual_viability_witness_gives_a_single_stationary_deterministic_safe_controller
    (next : X → Fin m → X) (failure : Set X) :
    ∃ policy : X → Fin m, ∀ x ∈ actualViable next failure,
      ∀ n, stationaryRun next policy x (n+1) ∉ failure := by
  classical
  let choice (x : X) (hx : x ∈ actualViable next failure) :=
    Classical.choose (actual_viable_path_has_a_viable_and_immediately_safe_first_successor next failure x hx)
  let policy (x : X) := if hx : x ∈ actualViable next failure then choice x hx else 0
  have step (x : X) (hx : x ∈ actualViable next failure) :
      next x (policy x) ∈ actualViable next failure ∧ next x (policy x) ∉ failure := by
    simpa [policy, hx, choice] using
      Classical.choose_spec (actual_viable_path_has_a_viable_and_immediately_safe_first_successor next failure x hx)
  refine ⟨policy, ?_⟩
  intro x hx n
  have hv (k : ℕ) : stationaryRun next policy x k ∈ actualViable next failure := by
    induction k with
    | zero => exact hx
    | succ k ih => exact (step _ ih).1
  exact (step _ (hv n)).2

section ActualRandomPaths
variable {Ω : Type*} [MeasurableSpace Ω]

def firstActionLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (action : ℕ → Ω → Fin m) (ha : Measurable (action 0)) : PMF (Fin m) :=
  letI : IsProbabilityMeasure (μ.map (action 0)) := (Measure.isProbabilityMeasure_map_iff ha.aemeasurable).2 inferInstance
  (μ.map (action 0)).toPMF

theorem actual_first_action_law_is_the_true_pushforward_marginal
    (μ : Measure Ω) [IsProbabilityMeasure μ] (action : ℕ → Ω → Fin m)
    (ha : Measurable (action 0)) (a : Fin m) :
    firstActionLaw μ action ha a = μ {ω | action 0 ω = a} := by
  unfold firstActionLaw
  rw [Measure.toPMF_apply, Measure.map_apply ha (measurableSet_singleton a)]
  rfl

theorem actual_unviable_first_successor_forces_a_later_failure_on_every_realized_path
    (next : X → Fin m → X) (failure : Set X) (x : X)
    (state : ℕ → Ω → X) (action : ℕ → Ω → Fin m)
    (hinitial : ∀ ω, state 0 ω = x)
    (hdynamics : ∀ n ω, state (n+1) ω = next (state n ω) (action n ω))
    (a : Fin m) (hbad : next x a ∉ actualViable next failure) :
    {ω | action 0 ω = a} ⊆ ⋃ n : ℕ, {ω | state (n+1) ω ∈ failure} := by
  intro ω hω
  have hf : ∃ n, state (n+2) ω ∈ failure := by
    by_contra h
    push_neg at h
    apply hbad
    refine ⟨(fun n => state (n+1) ω), (fun n => action (n+1) ω), ?_, ?_, ?_⟩
    · change action 0 ω = a at hω
      simpa [hinitial ω, hω] using hdynamics 0 ω
    · intro n
      exact hdynamics (n+1) ω
    · intro n
      exact h n
  rcases hf with ⟨n,hn⟩
  exact mem_iUnion.mpr ⟨n+1,hn⟩

theorem actual_all_time_almost_sure_safety_forces_first_action_support_in_the_viable_slice
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (next : X → Fin m → X) (failure : Set X) (x : X)
    (state : ℕ → Ω → X) (action : ℕ → Ω → Fin m)
    (ha : Measurable (action 0))
    (hinitial : ∀ ω, state 0 ω = x)
    (hdynamics : ∀ n ω, state (n+1) ω = next (state n ω) (action n ω))
    (hsafe : ∀ n, μ {ω | state (n+1) ω ∈ failure} = 0) :
    ∀ a, firstActionLaw μ action ha a ≠ 0 → a ∈ viableActions next failure x := by
  intro a hpos
  by_contra h
  have hbad : next x a ∉ actualViable next failure := by simpa [viableActions] using h
  have hz := measure_iUnion_null hsafe
  have he := measure_mono_null
    (actual_unviable_first_successor_forces_a_later_failure_on_every_realized_path
      next failure x state action hinitial hdynamics a hbad) hz
  rw [← actual_first_action_law_is_the_true_pushforward_marginal μ action ha a] at he
  exact hpos he

end ActualRandomPaths

theorem actual_probability_support_forces_the_viable_action_slice_nonempty
    (p : PMF (Fin m)) (s : Finset (Fin m)) (hs : ∀ a, p a ≠ 0 → a ∈ s) : s.Nonempty := by
  obtain ⟨a,ha⟩ := p.support_nonempty
  exact ⟨a,hs a ha⟩

theorem actual_uniform_on_viable_slice_has_the_exact_cardinality_masses
    (s : Finset (Fin m)) (hs : s.Nonempty) (a : Fin m) (ha : a ∈ s) :
    ((PMF.uniformOfFinset s hs) a).toReal = (s.card : ℝ)⁻¹ := by
  rw [PMF.uniformOfFinset_apply_of_mem hs ha, ENNReal.toReal_inv]
  simp

theorem actual_supported_policy_kl_against_viable_uniform_is_log_card_minus_entropy
    (p : PMF (Fin m)) (s : Finset (Fin m)) (hs : s.Nonempty)
    (hp : ∀ a, p a ≠ 0 → a ∈ s) :
    (klDiv p.toMeasure (PMF.uniformOfFinset s hs).toMeasure).toReal =
      Real.log (s.card : ℝ) - shannonEntropy p := by
  have hq : ∀ a, p a ≠ 0 → PMF.uniformOfFinset s hs a ≠ 0 := by
    intro a ha
    exact (PMF.mem_support_uniformOfFinset_iff hs a).mpr (hp a ha)
  rw [actual_support_kl_sum p _ hq, actual_entropy_sum]
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hs).ne'
  have hi (a : Fin m) : (p a).toReal * Real.log ((p a).toReal / (PMF.uniformOfFinset s hs a).toReal) =
      (p a).toReal * Real.log (p a).toReal + (p a).toReal * Real.log (s.card : ℝ) := by
    by_cases hz : p a = 0
    · simp [hz]
    · have hpr : (p a).toReal ≠ 0 := by
        simpa [ENNReal.toReal_eq_zero_iff, p.apply_ne_top a] using hz
      rw [actual_uniform_on_viable_slice_has_the_exact_cardinality_masses s hs a (hp a hz),
        Real.log_div hpr (inv_ne_zero hc), Real.log_inv]
      ring
  simp only [hi, Finset.sum_add_distrib, ← Finset.sum_mul, actual_finite_weights_sum,
    one_mul, neg_mul, Finset.sum_neg_distrib]
  ring

theorem actual_supported_policy_entropy_is_bounded_by_the_viable_action_count
    (p : PMF (Fin m)) (s : Finset (Fin m)) (hs : ∀ a, p a ≠ 0 → a ∈ s) :
    shannonEntropy p ≤ Real.log (s.card : ℝ) := by
  have hn := actual_probability_support_forces_the_viable_action_slice_nonempty p s hs
  have h := ENNReal.toReal_nonneg (a := klDiv p.toMeasure (PMF.uniformOfFinset s hn).toMeasure)
  rw [actual_supported_policy_kl_against_viable_uniform_is_log_card_minus_entropy p s hn hs] at h
  linarith

theorem actual_entropy_cap_is_attained_exactly_by_the_uniform_viable_law
    (p : PMF (Fin m)) (s : Finset (Fin m)) (hs : s.Nonempty)
    (hp : ∀ a, p a ≠ 0 → a ∈ s) :
    shannonEntropy p = Real.log (s.card : ℝ) ↔ p = PMF.uniformOfFinset s hs := by
  have hq : ∀ a, p a ≠ 0 → PMF.uniformOfFinset s hs a ≠ 0 := by
    intro a ha
    exact (PMF.mem_support_uniformOfFinset_iff hs a).mpr (hp a ha)
  have hf := klDiv_ne_top (actual_support_absolute_continuity p _ |>.mpr hq) Integrable.of_finite
  have hz : (klDiv p.toMeasure (PMF.uniformOfFinset s hs).toMeasure).toReal = 0 ↔
      klDiv p.toMeasure (PMF.uniformOfFinset s hs).toMeasure = 0 := by
    rw [ENNReal.toReal_eq_zero_iff]
    simp [hf]
  rw [← actual_finite_gibbs_equality p (PMF.uniformOfFinset s hs), ← hz,
    actual_supported_policy_kl_against_viable_uniform_is_log_card_minus_entropy p s hs hp]
  constructor <;> intro h <;> linarith

theorem actual_every_safe_stochastic_controller_obeys_the_full_source_entropy_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (next : X → Fin m → X) (failure : Set X) (x : X)
    (state : ℕ → Ω → X) (action : ℕ → Ω → Fin m)
    (ha : Measurable (action 0)) (hinitial : ∀ ω, state 0 ω = x)
    (hdynamics : ∀ n ω, state (n+1) ω = next (state n ω) (action n ω))
    (hsafe : ∀ n, μ {ω | state (n+1) ω ∈ failure} = 0) :
    shannonEntropy (firstActionLaw μ action ha) ≤
      Real.log ((viableActions next failure x).card : ℝ) := by
  exact actual_supported_policy_entropy_is_bounded_by_the_viable_action_count _ _
    (actual_all_time_almost_sure_safety_forces_first_action_support_in_the_viable_slice
      μ next failure x state action ha hinitial hdynamics hsafe)

def penaltyThreshold (gap u₂ u₃ α δ : ℝ) : ℝ := gap/u₃ + (u₂-Real.log δ)/u₃*α

theorem actual_softmax_critical_action_mass_obeys_the_source_two_sided_Q_bound
    (scores : Fin m → ℝ) (α p u₁ v₁ u₂ u₃ : ℝ) (hα : 0 < α)
    (a b : Fin m) (ha : scores a ≤ u₁+α*u₂-p*u₃) (hb : v₁ ≤ scores b) :
    (actualTemperatureLaw scores α a).toReal ≤
      Real.exp ((u₁-v₁)/α+u₂-p*u₃/α) := by
  have hd : Real.exp (scores b/α) ≤ actualPartition scores α := by
    unfold actualPartition
    exact Finset.single_le_sum (f := fun i : Fin m => Real.exp (scores i / α))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ b)
  rw [actual_temperature_law_has_the_literal_normalized_exponential_masses]
  calc
    Real.exp (scores a/α)/actualPartition scores α ≤
        Real.exp (scores a/α)/Real.exp (scores b/α) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hd
    _ = Real.exp ((scores a-scores b)/α) := by rw [← Real.exp_sub];congr 1;ring
    _ ≤ Real.exp ((u₁-v₁)/α+u₂-p*u₃/α) := by
      apply Real.exp_le_exp.mpr
      have h : scores a-scores b ≤ u₁-v₁+α*u₂-p*u₃ := by linarith
      have hh := (div_le_div_iff_of_pos_right hα).mpr h
      convert hh using 1 <;> field_simp <;> ring

theorem actual_source_threshold_is_equivalent_to_the_exponential_probability_bound
    (gap u₂ u₃ α δ p : ℝ) (hu₃ : 0 < u₃) (hα : 0 < α) (hδ : 0 < δ) :
    Real.exp (gap/α+u₂-p*u₃/α) ≤ δ ↔ penaltyThreshold gap u₂ u₃ α δ ≤ p := by
  have hprob : Real.exp (gap/α+u₂-p*u₃/α) ≤ δ ↔
      gap/α+u₂-p*u₃/α ≤ Real.log δ := by
    conv_lhs => rw [← Real.exp_log hδ]
    exact Real.exp_le_exp
  rw [hprob]
  unfold penaltyThreshold
  have he : gap/u₃+(u₂-Real.log δ)/u₃*α = (gap+(u₂-Real.log δ)*α)/u₃ := by ring
  rw [he, div_le_iff₀ hu₃]
  have halg : gap/α+u₂-p*u₃/α = (gap+α*u₂-p*u₃)/α := by field_simp <;> ring
  rw [halg, div_le_iff₀ hα]
  constructor <;> intro h <;> nlinarith

theorem actual_threshold_guarantees_delta_safety_for_each_critical_action
    (scores : Fin m → ℝ) (α p u₁ v₁ u₂ u₃ δ : ℝ) (hα : 0 < α)
    (hu₃ : 0 < u₃) (hδ : 0 < δ) (hp : penaltyThreshold (u₁-v₁) u₂ u₃ α δ ≤ p)
    (a b : Fin m) (ha : scores a ≤ u₁+α*u₂-p*u₃) (hb : v₁ ≤ scores b) :
    (actualTemperatureLaw scores α a).toReal ≤ δ := by
  exact (actual_softmax_critical_action_mass_obeys_the_source_two_sided_Q_bound
    scores α p u₁ v₁ u₂ u₃ hα a b ha hb).trans
    ((actual_source_threshold_is_equivalent_to_the_exponential_probability_bound
      (u₁-v₁) u₂ u₃ α δ p hu₃ hα hδ).mpr hp)

theorem actual_one_decade_of_safety_has_exact_temperature_proportional_penalty_cost
    (gap u₂ u₃ α δ : ℝ) (hu₃ : u₃ ≠ 0) (hδ : δ ≠ 0) :
    penaltyThreshold gap u₂ u₃ α (δ/10) - penaltyThreshold gap u₂ u₃ α δ =
      α*Real.log 10/u₃ := by
  unfold penaltyThreshold
  rw [Real.log_div hδ (by norm_num : (10:ℝ) ≠ 0)]
  ring

def sourceHalfPenalty : ℝ := penaltyThreshold 10 2 1 (1/2) (1/100)
def sourceDoublePenalty : ℝ := penaltyThreshold 10 2 1 2 (1/100)

theorem actual_source_penalties_are_the_exact_logarithmic_values :
    sourceHalfPenalty = 11+Real.log 10 ∧ sourceDoublePenalty = 14+4*Real.log 10 := by
  have hl : Real.log (1/100:ℝ) = -2*Real.log 10 := by
    rw [show (1/100:ℝ) = ((10:ℝ)^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    ring
  simp only [sourceHalfPenalty, sourceDoublePenalty, penaltyThreshold, hl]
  constructor <;> ring

theorem actual_log_ten_has_rigorous_rational_enclosures :
    (230258509/100000000:ℝ) < Real.log 10 ∧ Real.log 10 < 230258510/100000000 := by
  rw [show (10:ℝ) = 2*5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
    Real.log_five_gt_d9, Real.log_five_lt_d9]

theorem actual_source_two_penalties_have_the_printed_two_decimal_roundings :
    |sourceHalfPenalty-(1330/100:ℝ)| < 1/200 ∧
      |sourceDoublePenalty-(2321/100:ℝ)| < 1/200 := by
  rw [actual_source_penalties_are_the_exact_logarithmic_values.1,
    actual_source_penalties_are_the_exact_logarithmic_values.2]
  obtain ⟨hl,hu⟩ := actual_log_ten_has_rigorous_rational_enclosures
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

theorem actual_source_extra_decade_penalties_have_the_printed_two_decimal_roundings :
    |(1/2)*Real.log 10-(115/100:ℝ)| < 1/200 ∧
      |2*Real.log 10-(461/100:ℝ)| < 1/200 := by
  obtain ⟨hl,hu⟩ := actual_log_ten_has_rigorous_rational_enclosures
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

theorem actual_source_log_failure_probability_is_rounded_not_exact :
    |-Real.log (1/100:ℝ)-(4605/1000:ℝ)| < 1/2000 ∧
      -Real.log (1/100:ℝ) ≠ (4605/1000:ℝ) := by
  have hl : Real.log (1/100:ℝ) = -2*Real.log 10 := by
    rw [show (1/100:ℝ) = ((10:ℝ)^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    ring
  rw [hl]
  obtain ⟨hlo,hhi⟩ := actual_log_ten_has_rigorous_rational_enclosures
  constructor
  · rw [abs_lt];constructor <;> linarith
  · exact ne_of_gt (by linarith)



theorem actual_all_time_almost_sure_safe_random_path_supplies_a_genuine_viability_witness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (next : X → Fin m → X) (failure : Set X) (x : X)
    (state : ℕ → Ω → X) (action : ℕ → Ω → Fin m)
    (hinitial : ∀ ω, state 0 ω = x)
    (hdynamics : ∀ n ω, state (n+1) ω = next (state n ω) (action n ω))
    (hsafe : ∀ n, μ {ω | state (n+1) ω ∈ failure} = 0) :
    x ∈ actualViable next failure := by
  have ha : ∀ᵐ ω ∂μ, ∀ n, state (n+1) ω ∉ failure := by
    rw [ae_all_iff]
    intro n
    simpa only [ae_iff, mem_setOf_eq, not_not] using hsafe n
  obtain ⟨ω,hω⟩ := ha.exists
  exact ⟨fun n => state n ω,fun n => action n ω,hinitial ω,
    fun n => hdynamics n ω,hω⟩

theorem actual_viability_kernel_is_exactly_existence_of_a_stationary_safe_controller
    (next : X → Fin m → X) (failure : Set X) (x : X) :
    x ∈ actualViable next failure ↔
      ∃ policy : X → Fin m, ∀ n, stationaryRun next policy x (n+1) ∉ failure := by
  constructor
  · intro hx
    obtain ⟨policy,hpolicy⟩ := actual_viability_witness_gives_a_single_stationary_deterministic_safe_controller next failure
    exact ⟨policy,hpolicy x hx⟩
  · rintro ⟨policy,hpolicy⟩
    exact ⟨stationaryRun next policy x,fun n => policy (stationaryRun next policy x n),
      rfl,fun n => rfl,hpolicy⟩



theorem actual_source_sufficient_threshold_is_affine_in_temperature (α : ℝ) :
    penaltyThreshold 10 2 1 α (1/100) = 10+(2+2*Real.log 10)*α := by
  have hl : Real.log (1/100:ℝ) = -2*Real.log 10 := by
    rw [show (1/100:ℝ) = ((10:ℝ)^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    ring
  simp only [penaltyThreshold,hl]
  ring

theorem actual_any_fixed_penalty_is_below_the_sufficient_threshold_at_some_positive_temperature
    (p : ℝ) : ∃ α : ℝ, 0 < α ∧ p < penaltyThreshold 10 2 1 α (1/100) := by
  let α : ℝ := max p 0+1
  have ha : 0 < α := by dsimp [α];linarith [le_max_right p 0]
  have hp : p < α := by dsimp [α];linarith [le_max_left p 0]
  have hc : 1 < 2+2*Real.log 10 := by linarith [Real.log_pos (by norm_num : (1:ℝ)<10)]
  refine ⟨α,ha,?_⟩
  rw [actual_source_sufficient_threshold_is_affine_in_temperature]
  nlinarith

end SafeLearning.CompleteModulesViabilityEntropyWhole30
