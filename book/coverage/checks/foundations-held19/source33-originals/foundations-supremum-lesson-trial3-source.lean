import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology Pointwise
namespace SafeLearning.CompleteFoundationsSupremumLesson

theorem actual_upper_bounds_are_exactly_the_printed_pointwise_bounds
    (A : Set ℝ) (u : ℝ) : u ∈ upperBounds A ↔ ∀ a ∈ A, a ≤ u := Iff.rfl

theorem actual_bounded_above_means_an_upper_bound_exists (A : Set ℝ) :
    BddAbove A ↔ ∃ u : ℝ, ∀ a ∈ A, a ≤ u := Iff.rfl

theorem actual_nonempty_bounded_real_sets_have_a_true_least_upper_bound
    (A : Set ℝ) (hn : A.Nonempty) (hb : BddAbove A) :
    ∃ u : ℝ, IsLUB A u := ⟨sSup A, isLUB_csSup hn hb⟩

theorem actual_real_supremum_has_the_literal_upper_and_epsilon_properties
    (A : Set ℝ) (hn : A.Nonempty) (hb : BddAbove A) :
    (∀ a ∈ A, a ≤ sSup A) ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ a ∈ A, sSup A - epsilon < a := by
  refine ⟨fun a ha => le_csSup hb ha, ?_⟩
  intro epsilon he
  exact exists_lt_of_lt_csSup hn (by linarith)

theorem actual_upper_and_epsilon_properties_characterize_the_supremum
    (A : Set ℝ) (hn : A.Nonempty) (u : ℝ)
    (hupper : ∀ a ∈ A, a ≤ u)
    (happroach : ∀ epsilon : ℝ, 0 < epsilon → ∃ a ∈ A, u-epsilon < a) :
    sSup A = u := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt hn hupper
  intro w hw
  obtain ⟨a,ha,h⟩ := happroach (u-w) (by linarith)
  exact ⟨a,ha,by linarith⟩

theorem actual_supremum_is_a_maximum_exactly_when_it_belongs_to_the_set
    (A : Set ℝ) (_hn : A.Nonempty) (hb : BddAbove A) :
    IsGreatest A (sSup A) ↔ sSup A ∈ A := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h,fun a ha => le_csSup hb ha⟩

theorem actual_real_infimum_is_the_negative_supremum_of_the_negated_set
    (A : Set ℝ) : sInf A = -sSup (-A) := by
  rw [Real.sSup_neg]
  simp

theorem actual_function_supremum_is_the_supremum_of_its_image
    {X : Type*} (f : X → ℝ) (D : Set X) :
    sSup (f '' D) = sSup {y : ℝ | ∃ x ∈ D, f x=y} := by
  congr 1

theorem actual_an_upper_bound_and_a_convergent_approaching_sequence_prove_the_supremum
    (A : Set ℝ) (u : ℝ) (a : ℕ → ℝ) (ha : ∀ n, a n ∈ A)
    (hupper : ∀ x ∈ A, x ≤ u) (hlimit : Tendsto a atTop (𝓝 u)) :
    sSup A = u := by
  have hn : A.Nonempty := ⟨a 0,ha 0⟩
  apply le_antisymm (csSup_le hn hupper)
  exact le_of_tendsto hlimit (Eventually.of_forall (fun n => le_csSup ⟨u,hupper⟩ (ha n)))

theorem actual_nonnegative_scaling_preserves_real_suprema
    (A : Set ℝ) (hn : A.Nonempty) (hb : BddAbove A) (c : ℝ) (hc : 0 ≤ c) :
    sSup ((fun a => c*a) '' A) = c*sSup A :=
  ((isLUB_csSup hn hb).mul_left hc).csSup_eq (hn.image _)

theorem actual_independent_set_sums_have_the_sum_of_their_suprema
    (A B : Set ℝ) (ha : A.Nonempty) (hA : BddAbove A)
    (hb : B.Nonempty) (hB : BddAbove B) :
    sSup (A+B) = sSup A+sSup B := csSup_add ha hA hb hB

theorem actual_pointwise_sum_supremum_is_at_most_the_sum_of_suprema
    {X : Type*} [Nonempty X] (f g : X → ℝ)
    (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    sSup (range (fun x => f x+g x)) ≤ sSup (range f)+sSup (range g) := by
  apply csSup_le (range_nonempty _)
  rintro z ⟨x,rfl⟩
  exact add_le_add (le_csSup hf (mem_range_self x)) (le_csSup hg (mem_range_self x))

theorem actual_pointwise_sum_infimum_is_at_least_the_sum_of_infima
    {X : Type*} [Nonempty X] (f g : X → ℝ)
    (hf : BddBelow (range f)) (hg : BddBelow (range g)) :
    sInf (range f)+sInf (range g) ≤ sInf (range (fun x => f x+g x)) := by
  apply le_csInf (range_nonempty _)
  rintro z ⟨x,rfl⟩
  exact add_le_add (csInf_le hf (mem_range_self x)) (csInf_le hg (mem_range_self x))

theorem actual_inclusion_increases_suprema_and_decreases_infima
    (A B : Set ℝ) (ha : A.Nonempty) (hab : A ⊆ B)
    (hB : BddAbove B) (hB' : BddBelow B) :
    sSup A ≤ sSup B ∧ sInf B ≤ sInf A :=
  ⟨csSup_le_csSup hB ha hab, csInf_le_csInf hB' ha hab⟩

theorem actual_arbitrary_extended_real_max_min_is_at_most_min_max
    {X Y : Type*} (phi : X → Y → EReal) :
    (⨆ y, ⨅ x, phi x y) ≤ ⨅ x, ⨆ y, phi x y :=
  iSup_iInf_le_iInf_iSup (fun y x => phi x y)

theorem actual_half_open_unit_interval_has_supremum_one_and_no_maximum :
    sSup (Ico (0:ℝ) 1)=1 ∧ ¬∃ u : ℝ, IsGreatest (Ico (0:ℝ) 1) u := by
  refine ⟨csSup_Ico (by norm_num),?_⟩
  rintro ⟨u,hu⟩
  have hv : (u+1)/2 ∈ Ico (0:ℝ) 1 := ⟨by linarith [hu.1.1],by linarith [hu.1.2]⟩
  have hh := hu.2 hv
  linarith [hu.1.2]

theorem actual_open_unit_interval_has_supremum_one_and_no_maximum :
    sSup (Ioo (0:ℝ) 1)=1 ∧ ¬∃ u : ℝ, IsGreatest (Ioo (0:ℝ) 1) u := by
  refine ⟨csSup_Ioo (by norm_num),?_⟩
  rintro ⟨u,hu⟩
  have hv : (u+1)/2 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hu.1.1],by linarith [hu.1.2]⟩
  have hh := hu.2 hv
  linarith [hu.1.2]

theorem actual_pointwise_sum_supremum_can_be_strict :
    (∀ x : ℝ, x ∈ Icc (0:ℝ) 1 → x+(-x)=0) ∧
      IsGreatest (Icc (0:ℝ) 1) 1 ∧ IsGreatest ((fun x:ℝ => -x) '' Icc 0 1) 0 ∧
      (0:ℝ)<1+0 := by
  refine ⟨fun x _ => by ring,⟨by norm_num,fun x hx => hx.2⟩,?_,by norm_num⟩
  constructor
  · exact ⟨0,by norm_num,by norm_num⟩
  · rintro z ⟨x,hx,rfl⟩
    linarith [hx.1]

end SafeLearning.CompleteFoundationsSupremumLesson
