import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsMonotoneSequences

theorem actual_antitone_bounded_sequence_converges_to_the_true_range_infimum
    (a : ℕ→ℝ) (ha : Antitone a) (hb : BddBelow (range a)) :
    Tendsto a atTop (𝓝 (sInf (range a))) := by
  exact tendsto_atTop_ciInf ha hb

theorem actual_monotone_bounded_sequence_converges_to_the_true_range_supremum
    (a : ℕ→ℝ) (ha : Monotone a) (hb : BddAbove (range a)) :
    Tendsto a atTop (𝓝 (sSup (range a))) := by
  exact tendsto_atTop_ciSup ha hb

theorem actual_infimum_epsilon_proof_route_for_monotone_convergence
    (a : ℕ→ℝ) (ha : Antitone a) (hb : BddBelow (range a))
    (epsilon : ℝ) (he : 0<epsilon) :
    ∃ T : ℕ, a T<sInf (range a)+epsilon ∧
      ∀ t≥T,sInf (range a)≤a t ∧ a t≤a T ∧ a t<sInf (range a)+epsilon := by
  obtain ⟨value,⟨T,rfl⟩,hT⟩ := exists_lt_of_csInf_lt
    (show (range a).Nonempty from ⟨a 0,mem_range_self 0⟩)
    (by linarith : sInf (range a)<sInf (range a)+epsilon)
  exact ⟨T,hT,fun t ht=>⟨csInf_le hb (mem_range_self t),ha ht,(ha ht).trans_lt hT⟩⟩

theorem actual_infimum_plus_epsilon_is_not_a_lower_bound
    (a : ℕ→ℝ) (epsilon : ℝ) (he : 0<epsilon) :
    sInf (range a)+epsilon∉lowerBounds (range a) := by
  obtain ⟨value,hv,hlt⟩ := exists_lt_of_csInf_lt
    (show (range a).Nonempty from ⟨a 0,mem_range_self 0⟩)
    (by linarith : sInf (range a)<sInf (range a)+epsilon)
  intro h
  exact (not_le_of_gt hlt) (h hv)

theorem actual_decreasing_without_lower_bound_is_a_genuine_counterexample :
    Antitone (fun n : ℕ=>-(n:ℝ)) ∧
      ¬BddBelow (range (fun n : ℕ=>-(n:ℝ))) ∧
      Tendsto (fun n : ℕ=>-(n:ℝ)) atTop atBot := by
  refine ⟨?_,?_,tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop⟩
  · intro m n h; exact neg_le_neg (by exact_mod_cast h)
  · rintro ⟨bound,hbound⟩
    obtain ⟨n,hn⟩ := exists_nat_gt (-bound)
    have h := hbound (mem_range_self n)
    linarith

theorem actual_alternating_sequence_is_bounded_but_neither_monotone_nor_antitone :
    (∀ n : ℕ,-1≤(-1:ℝ)^n ∧ (-1:ℝ)^n≤1) ∧
      ¬Monotone (fun n : ℕ=>(-1:ℝ)^n) ∧
      ¬Antitone (fun n : ℕ=>(-1:ℝ)^n) := by
  constructor
  · intro n; exact abs_le.mp (by simp)
  constructor
  · intro h; have hh:=h (show (0:ℕ)≤1 by omega);norm_num at hh
  · intro h; have hh:=h (show (1:ℕ)≤2 by omega);norm_num at hh

theorem actual_nonnegative_nonincreasing_values_have_a_nonnegative_limit
    (a : ℕ→ℝ) (ha : Antitone a) (hnonneg : ∀ n,0≤a n) :
    ∃ value : ℝ, 0≤value ∧ Tendsto a atTop (𝓝 value) := by
  have hb : BddBelow (range a) := ⟨0,by rintro value ⟨n,rfl⟩;exact hnonneg n⟩
  have ht := actual_antitone_bounded_sequence_converges_to_the_true_range_infimum a ha hb
  exact ⟨sInf (range a),ge_of_tendsto ht (Eventually.of_forall hnonneg),ht⟩

theorem actual_positive_decreasing_values_can_converge_to_one :
    Antitone (fun n : ℕ=>1+1/((n:ℝ)+1)) ∧
      (∀ n : ℕ,0<1+1/((n:ℝ)+1)) ∧
      Tendsto (fun n : ℕ=>1+1/((n:ℝ)+1)) atTop (𝓝 1) := by
  refine ⟨?_,fun n=>by positivity,?_⟩
  · intro m n h
    have hr : 1/((n:ℝ)+1)≤1/((m:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)
    dsimp
    linarith
  · have ht : Tendsto (fun n : ℕ=>1/((n:ℝ)+1)) atTop (𝓝 0) := by
      simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).add ht

end SafeLearning.CompleteFoundationsMonotoneSequences
