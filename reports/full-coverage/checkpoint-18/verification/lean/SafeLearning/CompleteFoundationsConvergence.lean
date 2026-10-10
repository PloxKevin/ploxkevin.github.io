import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsConvergence

theorem real_convergence_definition (a : ℕ → ℝ) (l : ℝ) :
    Tendsto a atTop (𝓝 l) ↔
      ∀ ε : ℝ, 0<ε → ∃ T : ℕ, ∀ t ≥ T, |a t-l|<ε := by
  simpa only [Real.dist_eq] using (Metric.tendsto_atTop (u := a) (a := l))

theorem vector_convergence_definition {E : Type*} [NormedAddCommGroup E]
    (a : ℕ → E) (l : E) :
    Tendsto a atTop (𝓝 l) ↔
      ∀ ε : ℝ, 0<ε → ∃ T : ℕ, ∀ t ≥ T, ‖a t-l‖<ε := by
  simpa only [dist_eq_norm] using (Metric.tendsto_atTop (u := a) (a := l))

theorem coordinatewise_convergence (n : ℕ) (a : ℕ → Fin n → ℝ) (l : Fin n → ℝ) :
    Tendsto a atTop (𝓝 l) ↔ ∀ i, Tendsto (fun t => a t i) atTop (𝓝 (l i)) :=
  tendsto_pi_nhds

theorem euclidean_coordinatewise_convergence (n : ℕ)
    (a : ℕ → EuclideanSpace ℝ (Fin n)) (l : EuclideanSpace ℝ (Fin n)) :
    Tendsto a atTop (𝓝 l) ↔ ∀ i, Tendsto (fun t => a t i) atTop (𝓝 (l i)) := by
  constructor
  · intro h i
    exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt.tendsto.comp h
  · intro h
    have hp : Tendsto (fun t => WithLp.ofLp (a t)) atTop (𝓝 (WithLp.ofLp l)) :=
      tendsto_pi_nhds.mpr h
    simpa only [Function.comp_def,WithLp.toLp_ofLp] using
      (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).continuousAt.tendsto.comp hp

theorem real_cauchy_definition (a : ℕ → ℝ) :
    CauchySeq a ↔ ∀ ε : ℝ, 0<ε → ∃ T : ℕ,
      ∀ s ≥ T, ∀ t ≥ T, |a s-a t|<ε := by
  simpa only [Real.dist_eq] using (Metric.cauchySeq_iff (u := a))

theorem complete_converges_iff_cauchy {E : Type*} [MetricSpace E] [CompleteSpace E]
    (a : ℕ → E) : (∃ l, Tendsto a atTop (𝓝 l)) ↔ CauchySeq a := by
  constructor
  · rintro ⟨l,hl⟩; exact hl.cauchySeq
  · exact cauchySeq_tendsto_of_complete

theorem real_divergence_to_infinity_definition (a : ℕ → ℝ) :
    Tendsto a atTop atTop ↔ ∀ M : ℝ, ∃ T : ℕ, ∀ t ≥ T, M<a t := by
  constructor
  · intro h M
    have he := h.eventually (eventually_gt_atTop M)
    exact eventually_atTop.mp he
  · intro h
    apply tendsto_atTop.2
    intro M
    obtain ⟨T,hT⟩ := h M
    exact eventually_atTop.mpr ⟨T,fun t ht => (hT t ht).le⟩

theorem limits_preserve_weak_order (a b : ℕ → ℝ) (x y : ℝ)
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y))
    (hab : ∀ n, a n≤b n) : x≤y :=
  le_of_tendsto_of_tendsto ha hb (Eventually.of_forall hab)

theorem reciprocal_strictness_disappears :
    (∀ n : ℕ, 0<1/((n : ℝ)+1)) ∧
      Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0) := by
  constructor
  · intro n; positivity
  · simpa only [one_div,Function.comp_def] using
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

theorem reciprocal_tolerance_choice (ε : ℝ) (hε : 0<ε) (T n : ℕ)
    (hT : 1/ε ≤ (T : ℝ)) (hn : T≤n) : 1/((n : ℝ)+1)<ε := by
  have hT' : 1 ≤ (T : ℝ)*ε := (div_le_iff₀ hε).mp hT
  have hn' : (T : ℝ)≤n := by exact_mod_cast hn
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem limit_squeeze (a b c : ℕ → ℝ) (l : ℝ)
    (ha : Tendsto a atTop (𝓝 l)) (hb : Tendsto b atTop (𝓝 l))
    (hac : ∀ n, a n≤c n) (hcb : ∀ n, c n≤b n) :
    Tendsto c atTop (𝓝 l) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le ha hb hac hcb

theorem finite_pointwise_uniform_tolerance {X : Type*} [Fintype X]
    (F : ℕ → X → ℝ) (f : X → ℝ)
    (h : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    ∀ ε : ℝ, 0<ε → ∃ T : ℕ, ∀ n ≥ T, ∀ x, |F n x-f x|<ε := by
  intro ε hε
  have he : ∀ x, ∀ᶠ n in atTop, |F n x-f x|<ε := by
    intro x
    exact (Metric.tendsto_nhds.mp (h x) ε hε).mono fun n hn => by
      simpa only [Real.dist_eq] using hn
  have hall : ∀ᶠ n in atTop, ∀ x, |F n x-f x|<ε := eventually_all.mpr he
  exact eventually_atTop.mp hall

end SafeLearning.CompleteFoundationsConvergence
