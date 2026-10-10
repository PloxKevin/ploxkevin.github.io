import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsMaximumExistence

def argmax {X : Type*} (f : X → ℝ) (D : Set X) : Set X :=
  {x | x ∈ D ∧ ∀ y ∈ D, f y ≤ f x}

theorem actual_argmax_membership_means_an_attained_maximum
    {X : Type*} (f : X → ℝ) (D : Set X) (x : X) :
    x ∈ argmax f D ↔ x ∈ D ∧ IsGreatest (f '' D) (f x) := by
  constructor
  · rintro ⟨hx,hm⟩
    refine ⟨hx,⟨mem_image_of_mem f hx,?_⟩⟩
    rintro z ⟨y,hy,rfl⟩
    exact hm y hy
  · rintro ⟨hx,hm⟩
    exact ⟨hx,fun y hy => hm.2 (mem_image_of_mem f hy)⟩

theorem actual_nonempty_finite_domains_have_a_maximizer
    {X : Type*} (f : X → ℝ) (D : Set X) (hd : D.Finite) (hn : D.Nonempty) :
    (argmax f D).Nonempty := by
  obtain ⟨z,⟨x,hx,rfl⟩,hm⟩ := ((hd.image f).isCompact.exists_isGreatest (hn.image f))
  exact ⟨x,hx,fun y hy => hm (mem_image_of_mem f hy)⟩

theorem actual_continuous_functions_on_nonempty_compact_domains_have_a_maximizer
    {X : Type*} [TopologicalSpace X] (f : X → ℝ) (D : Set X)
    (hd : IsCompact D) (hn : D.Nonempty) (hf : ContinuousOn f D) :
    (argmax f D).Nonempty := by
  obtain ⟨x,hx,hm⟩ := hd.exists_isMaxOn hn hf
  exact ⟨x,hx,hm⟩

theorem actual_any_argmax_choice_requires_nonempty_argmax
    {X : Type*} (f : X → ℝ) (D : Set X) :
    (∃ x, x ∈ argmax f D) ↔ (argmax f D).Nonempty := Iff.rfl

theorem actual_empty_domains_are_finite_compact_and_have_no_argmax :
    (∅ : Set ℝ).Finite ∧ IsCompact (∅ : Set ℝ) ∧
      argmax (fun x : ℝ => x) ∅ = ∅ := by
  simp [argmax]

theorem actual_open_unit_interval_has_supremum_one_and_no_argmax :
    sSup (Ioo (0 : ℝ) 1) = 1 ∧ argmax (fun x : ℝ => x) (Ioo 0 1) = ∅ := by
  constructor
  · exact csSup_Ioo (by norm_num)
  · apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hm⟩
    have hy : (x+1)/2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have h := hm ((x+1)/2) hy
    linarith [hx.2]

theorem actual_bounded_nonempty_images_admit_every_positive_approximate_choice
    {X : Type*} (f : X → ℝ) (D : Set X) (hn : D.Nonempty)
    (_hb : BddAbove (f '' D)) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ x ∈ D, sSup (f '' D) - epsilon < f x := by
  obtain ⟨z,⟨x,hx,rfl⟩,hz⟩ := exists_lt_of_lt_csSup (hn.image f)
    (show sSup (f '' D)-epsilon < sSup (f '' D) by linarith)
  exact ⟨x,hx,hz⟩

end SafeLearning.CompleteFoundationsMaximumExistence
