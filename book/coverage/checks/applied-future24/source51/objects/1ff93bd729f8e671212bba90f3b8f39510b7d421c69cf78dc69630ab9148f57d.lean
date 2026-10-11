import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsSetImages

variable {X Y A I : Type*}

theorem actual_preimages_preserve_intersection_union_and_ambient_complement
    (f : X → Y) (B₁ B₂ B : Set Y) :
    f ⁻¹' (B₁ ∩ B₂) = (f ⁻¹' B₁) ∩ (f ⁻¹' B₂) ∧
      f ⁻¹' (B₁ ∪ B₂) = (f ⁻¹' B₁) ∪ (f ⁻¹' B₂) ∧
      f ⁻¹' ((univ : Set Y) \ B) = (univ : Set X) \ (f ⁻¹' B) := by
  simp

theorem actual_preimage_intersection_pointwise_proof
    (f : X → Y) (B₁ B₂ : Set Y) (x : X) :
    x ∈ f ⁻¹' (B₁ ∩ B₂) ↔ f x ∈ B₁ ∧ f x ∈ B₂ := Iff.rfl

theorem actual_safety_zero_and_sublevel_sets_are_preimages
    (h V : X → ℝ) (c : ℝ) :
    {x | h x ≥ 0} = h ⁻¹' Ici 0 ∧
      {x | h x = 0} = h ⁻¹' ({0} : Set ℝ) ∧
      {x | V x ≤ c} = V ⁻¹' Iic c := by exact ⟨rfl, rfl, rfl⟩

theorem actual_multiple_constraints_are_preimage_intersections (h : I → X → ℝ) :
    {x | ∀ i, h i x ≥ 0} = ⋂ i, (h i) ⁻¹' Ici 0 := by ext x; simp

theorem actual_images_preserve_unions_and_intersection_inclusion
    (f : X → Y) (S T : Set X) :
    f '' (S ∪ T) = f '' S ∪ f '' T ∧ f '' (S ∩ T) ⊆ f '' S ∩ f '' T :=
  ⟨Set.image_union f S T, Set.image_inter_subset f S T⟩

theorem actual_square_intersection_counterexample :
    (fun x : ℝ => x ^ 2) '' (({-1} : Set ℝ) ∩ {1}) = ∅ ∧
      ((fun x : ℝ => x ^ 2) '' ({-1} : Set ℝ)) ∩
        ((fun x : ℝ => x ^ 2) '' ({1} : Set ℝ)) = {1} := by norm_num

theorem actual_projection_introduces_an_existential (S : Set (A × X)) :
    Prod.snd '' S = {x | ∃ a, (a, x) ∈ S} := by ext x; simp

theorem actual_source_square_interval_image :
    (fun x : ℝ => x ^ 2) '' Icc (-1) 2 = Icc 0 4 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨sq_nonneg x, by nlinarith [hx.1, hx.2]⟩
  · rintro ⟨hy, hy4⟩
    refine ⟨Real.sqrt y, ?_, Real.sq_sqrt hy⟩
    have hs := Real.sq_sqrt hy
    constructor <;> nlinarith [Real.sqrt_nonneg y]

theorem actual_source_square_interval_preimages :
    (fun x : ℝ => x ^ 2) ⁻¹' Icc 1 4 = Icc (-2) (-1) ∪ Icc 1 2 ∧
      (fun x : ℝ => x ^ 2) ⁻¹' Icc (-3) (-1) = ∅ ∧
      (fun x : ℝ => x ^ 2) ⁻¹' ({1} : Set ℝ) = {-1, 1} := by
  constructor
  · ext x
    simp only [mem_preimage, mem_Icc, mem_union]
    constructor
    · rintro ⟨hl, hh⟩
      by_cases hx : x ≤ 0
      · left; constructor <;> nlinarith
      · right; constructor <;> nlinarith
    · rintro (⟨hl, hh⟩ | ⟨hl, hh⟩) <;> constructor <;> nlinarith
  constructor
  · ext x
    simp only [mem_preimage, mem_Icc, mem_empty_iff_false, iff_false, not_and]
    intro _; nlinarith [sq_nonneg x]
  · ext x
    simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
    constructor
    · intro hx
      have hz : (x - 1) * (x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with h | h
      · right; linarith
      · left; linarith
    · rintro (rfl | rfl) <;> norm_num

theorem actual_square_has_no_two_sided_inverse :
    ¬ Function.Bijective (fun x : ℝ => x ^ 2) := by
  intro h
  have he : (-1 : ℝ) = 1 := h.1 (by norm_num)
  norm_num at he

end SafeLearning.CompleteFoundationsSetImages
