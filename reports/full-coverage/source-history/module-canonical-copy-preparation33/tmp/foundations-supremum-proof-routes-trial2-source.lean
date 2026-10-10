import SafeLearning.CompleteFoundationsExtendedRealValues

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Pointwise
namespace SafeLearning.CompleteFoundationsSupremumProofRoutes
open SafeLearning.CompleteFoundationsExtendedRealValues

theorem actual_independent_sum_proof_has_the_printed_epsilon_half_witnesses
    (A B : Set ℝ) (ha : A.Nonempty) (hb : B.Nonempty)
    (_hA : BddAbove A) (_hB : BddAbove B) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ a ∈ A, ∃ b ∈ B, sSup A-epsilon/2<a ∧ sSup B-epsilon/2<b ∧
      sSup A+sSup B-epsilon<a+b := by
  obtain ⟨a,ha',hsa⟩ := exists_lt_of_lt_csSup ha
    (show sSup A-epsilon/2<sSup A by linarith)
  obtain ⟨b,hb',hsb⟩ := exists_lt_of_lt_csSup hb
    (show sSup B-epsilon/2<sSup B by linarith)
  exact ⟨a,ha',b,hb',hsa,hsb,by linarith⟩

theorem actual_set_sum_upper_bound_and_epsilon_half_route_are_literal
    (A B : Set ℝ) (ha : A.Nonempty) (hb : B.Nonempty)
    (hA : BddAbove A) (hB : BddAbove B) :
    (∀ a ∈ A, ∀ b ∈ B, a+b ≤ sSup A+sSup B) ∧
      ∀ epsilon : ℝ, 0 < epsilon → sSup A+sSup B-epsilon<sSup (A+B) := by
  have hup : ∀ a ∈ A, ∀ b ∈ B, a+b ≤ sSup A+sSup B :=
    fun a ha' b hb' => add_le_add (le_csSup hA ha') (le_csSup hB hb')
  refine ⟨hup,?_⟩
  intro epsilon he
  obtain ⟨a,ha',b,hb',_,_,hs⟩ :=
    actual_independent_sum_proof_has_the_printed_epsilon_half_witnesses A B ha hb hA hB epsilon he
  have hsum : BddAbove (A+B) := by
    refine ⟨sSup A+sSup B,?_⟩
    rintro z ⟨a,ha',b,hb',rfl⟩
    exact hup a ha' b hb'
  exact hs.trans_le (le_csSup hsum (add_mem_add ha' hb'))

theorem actual_pointwise_sum_upper_bound_is_the_printed_proof_step
    {X : Type*} (f g : X → ℝ) (hf : BddAbove (range f))
    (hg : BddAbove (range g)) (x : X) :
    f x+g x ≤ sSup (range f)+sSup (range g) :=
  add_le_add (le_csSup hf (mem_range_self x)) (le_csSup hg (mem_range_self x))

theorem actual_max_min_proof_has_the_literal_infimum_value_supremum_chain
    {X Y : Type*} (phi : X → Y → ℝ) (x' : X) (y : Y) :
    (⨅ x, (phi x y : EReal)) ≤ (phi x' y : EReal) ∧
      (phi x' y : EReal) ≤ ⨆ y', (phi x' y' : EReal) :=
  ⟨iInf_le (fun x => (phi x y : EReal)) x',le_iSup (fun y' => (phi x' y' : EReal)) y⟩

theorem actual_epsilon_approach_is_impossible_at_an_unbounded_positive_infinite_supremum :
    (univ : Set ℝ).Nonempty ∧ ¬BddAbove (univ : Set ℝ) ∧
      sSup ((fun r : ℝ => (r : EReal)) '' univ) = ⊤ ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ¬∃ a : ℝ, a ∈ (univ : Set ℝ) ∧
          sSup ((fun r : ℝ => (r : EReal)) '' univ)-(epsilon : EReal)<(a : EReal) := by
  have hs := actual_real_unbounded_above_sets_have_extended_supremum_infinity
    univ (not_bddAbove_univ : ¬BddAbove (univ : Set ℝ))
  refine ⟨⟨0,mem_univ _⟩,not_bddAbove_univ,hs,?_⟩
  intro epsilon _
  rw [hs]
  simp

end SafeLearning.CompleteFoundationsSupremumProofRoutes
