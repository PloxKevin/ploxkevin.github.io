import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsConvergenceModels

theorem actual_normed_sequence_convergence_is_the_literal_epsilon_definition
    {E : Type*} [NormedAddCommGroup E] (a : ℕ → E) (limit : E) :
    Tendsto a atTop (𝓝 limit) ↔
      ∀ epsilon : ℝ, 0<epsilon → ∃ T : ℕ, ∀ t≥T, ‖a t-limit‖<epsilon := by
  simpa only [dist_eq_norm] using (Metric.tendsto_atTop :
    Tendsto a atTop (𝓝 limit) ↔ ∀ epsilon>0, ∃ T, ∀ t≥T, dist (a t) limit<epsilon)

theorem actual_real_sequence_convergence_is_the_literal_absolute_epsilon_definition
    (a : ℕ → ℝ) (limit : ℝ) :
    Tendsto a atTop (𝓝 limit) ↔
      ∀ epsilon : ℝ, 0<epsilon → ∃ T : ℕ, ∀ t≥T, |a t-limit|<epsilon := by
  simpa only [Real.norm_eq_abs] using actual_normed_sequence_convergence_is_the_literal_epsilon_definition a limit

theorem actual_normed_cauchy_sequence_is_the_literal_two_tail_definition
    {E : Type*} [NormedAddCommGroup E] (a : ℕ → E) :
    CauchySeq a ↔ ∀ epsilon : ℝ, 0<epsilon →
      ∃ T : ℕ, ∀ s≥T, ∀ t≥T, ‖a s-a t‖<epsilon := by
  simpa only [dist_eq_norm] using (Metric.cauchySeq_iff :
    CauchySeq a ↔ ∀ epsilon>0, ∃ T, ∀ s≥T, ∀ t≥T, dist (a s) (a t)<epsilon)

theorem actual_complete_normed_sequence_converges_iff_it_is_cauchy
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (a : ℕ → E) :
    (∃ limit : E, Tendsto a atTop (𝓝 limit)) ↔ CauchySeq a := by
  constructor
  · rintro ⟨limit,h⟩; exact h.cauchySeq
  · exact cauchySeq_tendsto_of_complete

theorem actual_euclidean_vector_convergence_iff_every_coordinate_converges
    {ι : Type*} [Fintype ι] (a : ℕ → EuclideanSpace ℝ ι) (limit : EuclideanSpace ℝ ι) :
    Tendsto a atTop (𝓝 limit) ↔ ∀ i, Tendsto (fun n=>a n i) atTop (𝓝 (limit i)) := by
  constructor
  · intro h
    exact tendsto_pi_nhds.mp ((PiLp.continuous_ofLp 2 (fun _ : ι=>ℝ)).continuousAt.tendsto.comp h)
  · intro h
    have ht : Tendsto (fun n=>WithLp.ofLp (a n)) atTop (𝓝 (WithLp.ofLp limit)) :=
      tendsto_pi_nhds.mpr h
    simpa only [Function.comp_def,WithLp.toLp_ofLp] using
      (PiLp.continuous_toLp 2 (fun _ : ι=>ℝ)).continuousAt.tendsto.comp ht

theorem actual_real_divergence_to_positive_infinity_is_the_literal_strict_tail_definition
    (a : ℕ → ℝ) : Tendsto a atTop atTop ↔
      ∀ M : ℝ, ∃ T : ℕ, ∀ t≥T, M<a t := by
  constructor
  · intro h M
    obtain ⟨T,hT⟩ := tendsto_atTop_atTop.mp h (M+1)
    exact ⟨T,fun t ht=>by have hh:=hT t ht; linarith⟩
  · intro h
    apply tendsto_atTop_atTop.mpr
    intro M
    obtain ⟨T,hT⟩:=h M
    exact ⟨T,fun t ht=>(hT t ht).le⟩

theorem actual_reciprocal_sequence_tends_to_zero :
    Tendsto (fun t : ℕ=>1/((t:ℝ)+1)) atTop (𝓝 0) := by
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)

theorem actual_reciprocal_literal_tolerance_bound
    (epsilon : ℝ) (he : 0<epsilon) (T t : ℕ) (hT : 1/epsilon≤(T:ℝ)) (ht : T≤t) :
    1/((t:ℝ)+1)≤1/((T:ℝ)+1) ∧
      1/((T:ℝ)+1)<1/(T:ℝ) ∧ 1/(T:ℝ)≤epsilon := by
  have hp : 0<(T:ℝ) := lt_of_lt_of_le (one_div_pos.mpr he) hT
  have htt : (T:ℝ)≤(t:ℝ) := by exact_mod_cast ht
  refine ⟨one_div_le_one_div_of_le (by positivity) (by linarith),?_,?_⟩
  · exact one_div_lt_one_div_of_lt hp (by linarith)
  · apply (div_le_iff₀ hp).mpr
    have hh : 1≤(T:ℝ)*epsilon := (div_le_iff₀ he).mp hT
    nlinarith

theorem actual_source_tolerance_point_zero_one_and_cutoff_one_hundred :
    ∀ t : ℕ,100≤t→|1/((t:ℝ)+1)|<(1/100:ℝ) := by
  intro t ht
  have h:=actual_reciprocal_literal_tolerance_bound (1/100) (by norm_num) 100 t (by norm_num) ht
  rw [abs_of_nonneg (by positivity)]
  exact h.1.trans_lt (h.2.1.trans_le h.2.2)

theorem actual_limit_rules_sum_product_quotient_and_order
    (a b : ℕ→ℝ) (x y : ℝ) (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y))
    (hy : y≠0) (hle : ∀ n,a n≤b n) :
    Tendsto (fun n=>a n+b n) atTop (𝓝 (x+y)) ∧
      Tendsto (fun n=>a n*b n) atTop (𝓝 (x*y)) ∧
      Tendsto (fun n=>a n/b n) atTop (𝓝 (x/y)) ∧ x≤y := by
  exact ⟨ha.add hb,ha.mul hb,ha.div hb hy,
    le_of_tendsto_of_tendsto ha hb (Eventually.of_forall hle)⟩

theorem actual_squeeze_rule_and_continuous_image_rule
    (a b c : ℕ→ℝ) (limit : ℝ) (ha : Tendsto a atTop (𝓝 limit))
    (hb : Tendsto b atTop (𝓝 limit)) (hlo : ∀ n,a n≤c n) (hhi : ∀ n,c n≤b n)
    (g : ℝ→ℝ) (hg : ContinuousAt g limit) :
    Tendsto c atTop (𝓝 limit) ∧ Tendsto (fun n=>g (a n)) atTop (𝓝 (g limit)) :=
  ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le ha hb hlo hhi,hg.tendsto.comp ha⟩

theorem actual_positive_sequence_can_have_zero_limit :
    (∀ n : ℕ,0<1/((n:ℝ)+1)) ∧
      Tendsto (fun n : ℕ=>1/((n:ℝ)+1)) atTop (𝓝 0) :=
  ⟨fun n=>by positivity,actual_reciprocal_sequence_tends_to_zero⟩

end SafeLearning.CompleteFoundationsConvergenceModels
