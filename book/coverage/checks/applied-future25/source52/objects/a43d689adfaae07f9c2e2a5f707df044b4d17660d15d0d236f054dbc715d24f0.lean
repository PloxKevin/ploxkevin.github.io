import SafeLearning.CompleteModulesLoSBOGaussianHorizon
import SafeLearning.CompleteModulesLoSBOIndexedSafety

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SafeLearning.CompleteModulesLoSBOGaussianSafety
open CompleteModulesLoSBOIndexedSafety CompleteModulesLoSBOGaussianHorizon

theorem actual_bounded_finite_prefix_of_the_source_rounds_and_queries_is_safe
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (seed : Set X)
    (query : ℕ → X) (observation noise : ℕ → ℝ) (L E threshold : ℝ) (horizon : ℕ)
    (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (hf : ∀ a x, |f a-f x| ≤ L*dist a x)
    (hobs : ∀ t ≥ 1, t ≤ horizon → observation t=f (query t)+noise t)
    (hnoise : ∀ t ≥ 1, t ≤ horizon → noise t ≤ E)
    (hquery : ∀ t ≥ 1, t ≤ horizon → query t ∈ actualSourceRounds seed query observation
      (fun _ _ => E) (fun a x => L*dist a x) threshold t) :
    (∀ t ≤ horizon, ∀ x ∈ actualSourceRounds seed query observation
      (fun _ _ => E) (fun a x => L*dist a x) threshold t, threshold ≤ f x) ∧
      ∀ t ≥ 1, t ≤ horizon → threshold ≤ f (query t) := by
  have hs : ∀ t ≤ horizon, ∀ x ∈ actualSourceRounds seed query observation
      (fun _ _ => E) (fun a x => L*dist a x) threshold t, threshold ≤ f x := by
    intro t
    induction t with
    | zero => intro _;exact hseed
    | succ t ih =>
      intro ht
      cases t with
      | zero => exact hseed
      | succ n =>
        intro x hx
        change x ∈ actualSourceRounds seed query observation (fun _ _ => E)
          (fun a x => L*dist a x) threshold (n+1) ∪ _ at hx
        rcases hx with hx | hx
        · exact ih (by omega) x hx
        · have ho := hobs (n+1) (by omega) (by omega)
          have hn := hnoise (n+1) (by omega) (by omega)
          have hr := (abs_le.mp (hf (query (n+1)) x)).2
          change threshold ≤ observation (n+1)-E-L*dist (query (n+1)) x at hx
          linarith
  exact ⟨hs,fun t ht hT => hs t hT (query t) (hquery t ht hT)⟩

theorem actual_finite_gaussian_source_queries_have_failure_probability_at_most_delta
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : X → ℝ) (seed : Set X)
    (query : ℕ → Ω → X) (observation noise : ℕ → Ω → ℝ)
    (L threshold : ℝ) (horizon : ℕ) (ht : 1 ≤ horizon)
    (sigma : ℝ≥0) (hs : 0 < sigma) (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (hf : ∀ a x, |f a-f x| ≤ L*dist a x)
    (hobs : ∀ omega, ∀ t ≥ 1, t ≤ horizon → observation t omega=f (query t omega)+noise t omega)
    (hquery : ∀ omega, ∀ t ≥ 1, t ≤ horizon → query t omega ∈ actualSourceRounds seed
      (fun n => query n omega) (fun n => observation n omega)
      (fun _ _ => actualHorizonRadius sigma horizon delta) (fun a x => L*dist a x) threshold t)
    (hlaw : ∀ t : Fin horizon, HasLaw (noise (t.val+1)) (gaussianReal 0 (sigma^2)) P) :
    P.real {omega | ∃ t : Fin horizon, f (query (t.val+1) omega)<threshold} ≤ delta := by
  have hsub : {omega | ∃ t : Fin horizon, f (query (t.val+1) omega)<threshold} ⊆
      {omega | ∃ t : Fin horizon, actualHorizonRadius sigma horizon delta < |noise (t.val+1) omega|} := by
    intro omega ho
    by_contra hn
    have hn' : ∀ t : Fin horizon, |noise (t.val+1) omega| ≤ actualHorizonRadius sigma horizon delta := by
      simpa only [mem_setOf_eq,not_exists,not_lt] using hn
    have hp := actual_bounded_finite_prefix_of_the_source_rounds_and_queries_is_safe f seed
      (fun n => query n omega) (fun n => observation n omega) (fun n => noise n omega)
      L (actualHorizonRadius sigma horizon delta) threshold horizon hseed hf
      (hobs omega) (by
        intro t h1 hT
        have hidx : t-1<horizon := by omega
        have he : (t-1)+1=t := by omega
        have hb := hn' ⟨t-1,hidx⟩
        simp only [he] at hb
        exact (le_abs_self _).trans hb) (hquery omega)
    obtain ⟨t,htbad⟩ := ho
    have hh := hp.2 (t.val+1) (by omega) (by omega)
    exact (not_lt_of_ge hh) htbad
  exact (measureReal_mono hsub).trans
    (actual_all_horizon_gaussian_noise_exceedance_probability_is_at_most_delta P horizon ht
      (fun t => noise (t.val+1)) sigma hs delta hd hd1 hlaw)

theorem actual_measurable_finite_gaussian_query_safety_probability_is_at_least_one_minus_delta
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : X → ℝ) (seed : Set X)
    (query : ℕ → Ω → X) (observation noise : ℕ → Ω → ℝ)
    (L threshold : ℝ) (horizon : ℕ) (ht : 1 ≤ horizon)
    (sigma : ℝ≥0) (hs : 0 < sigma) (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (hf : ∀ a x, |f a-f x| ≤ L*dist a x)
    (hobs : ∀ omega, ∀ t ≥ 1, t ≤ horizon → observation t omega=f (query t omega)+noise t omega)
    (hquery : ∀ omega, ∀ t ≥ 1, t ≤ horizon → query t omega ∈ actualSourceRounds seed
      (fun n => query n omega) (fun n => observation n omega)
      (fun _ _ => actualHorizonRadius sigma horizon delta) (fun a x => L*dist a x) threshold t)
    (hlaw : ∀ t : Fin horizon, HasLaw (noise (t.val+1)) (gaussianReal 0 (sigma^2)) P)
    (hmeas : ∀ t : Fin horizon, Measurable (fun omega => f (query (t.val+1) omega))) :
    1-delta ≤ P.real {omega | ∀ t : Fin horizon, threshold ≤ f (query (t.val+1) omega)} := by
  have hb := actual_finite_gaussian_source_queries_have_failure_probability_at_most_delta
    P f seed query observation noise L threshold horizon ht sigma hs delta hd hd1 hseed hf hobs hquery hlaw
  have hm : MeasurableSet {omega | ∃ t : Fin horizon, f (query (t.val+1) omega)<threshold} := by
    have he : {omega | ∃ t : Fin horizon, f (query (t.val+1) omega)<threshold}=
        ⋃ t : Fin horizon, {omega | f (query (t.val+1) omega)<threshold} := by ext omega;simp
    rw [he]
    exact MeasurableSet.iUnion (fun t => measurableSet_lt (hmeas t) measurable_const)
  have hp := probReal_add_probReal_compl (μ:=P) hm
  have he : {omega | ∃ t : Fin horizon, f (query (t.val+1) omega)<threshold}ᶜ=
      {omega | ∀ t : Fin horizon, threshold ≤ f (query (t.val+1) omega)} := by ext omega;simp
  rw [he] at hp
  linarith

end SafeLearning.CompleteModulesLoSBOGaussianSafety
