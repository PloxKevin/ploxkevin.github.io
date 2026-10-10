import SafeLearning.CompleteFoundationsExtendedRealValues

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsSafeOptExtendedBands
open SafeLearning.CompleteFoundationsExtendedRealValues

def extendedImage (A : Set ℝ) : Set EReal := (fun r : ℝ => (r : EReal)) '' A
def lower (A : Set ℝ) : EReal := sInf (extendedImage A)
def upper (A : Set ℝ) : EReal := sSup (extendedImage A)

theorem actual_seed_halfline_has_lower_threshold_and_infinite_upper (h : ℝ) :
    lower (Ici h) = (h : EReal) ∧ upper (Ici h) = ⊤ := by
  constructor
  · apply le_antisymm
    · exact sInf_le (mem_image_of_mem _ (show h ∈ Ici h from (show h ≤ h from le_rfl)))
    · apply le_sInf
      rintro z ⟨r,hr,rfl⟩
      exact EReal.coe_le_coe_iff.mpr hr
  · apply actual_real_unbounded_above_sets_have_extended_supremum_infinity
    rintro ⟨u,hu⟩
    have hm : max h u+1 ∈ Ici h := by
      change h ≤ max h u+1
      linarith [le_max_left h u]
    have hh := hu hm
    linarith [le_max_right h u]

theorem actual_universal_initial_band_has_both_infinite_endpoints :
    lower univ = ⊥ ∧ upper univ = ⊤ :=
  ⟨actual_real_unbounded_below_sets_have_extended_infimum_negative_infinity
      univ not_bddBelow_univ,
    actual_real_unbounded_above_sets_have_extended_supremum_infinity
      univ not_bddAbove_univ⟩

theorem actual_empty_confidence_band_has_reversed_infinite_endpoints :
    lower ∅ = ⊤ ∧ upper ∅ = ⊥ ∧ upper ∅ < lower ∅ := by
  simp [lower,upper,extendedImage]

def initialBand {X : Type*} (seed : Set X) (h : ℝ) (x : X) : Set ℝ := by
  classical
  exact if x ∈ seed then Ici h else univ

theorem actual_seed_initialization_has_the_literal_extended_endpoints
    {X : Type*} (seed : Set X) (h : ℝ) (x : X) :
    (x ∈ seed → lower (initialBand seed h x) = (h : EReal) ∧
      upper (initialBand seed h x) = ⊤) ∧
    (x ∉ seed → lower (initialBand seed h x) = ⊥ ∧
      upper (initialBand seed h x) = ⊤) := by
  classical
  constructor
  · intro hx
    simpa [initialBand,hx] using actual_seed_halfline_has_lower_threshold_and_infinite_upper h
  · intro hx
    simpa [initialBand,hx] using actual_universal_initial_band_has_both_infinite_endpoints

theorem actual_a_confidence_truth_witness_prevents_empty_or_reversed_bands
    (A : Set ℝ) (value : ℝ) (hv : value ∈ A) :
    A.Nonempty ∧ lower A ≤ (value : EReal) ∧ (value : EReal) ≤ upper A ∧ lower A ≤ upper A := by
  have hl : lower A ≤ (value : EReal) := sInf_le (mem_image_of_mem _ hv)
  have hu : (value : EReal) ≤ upper A := le_sSup (mem_image_of_mem _ hv)
  exact ⟨⟨value,hv⟩,hl,hu,hl.trans hu⟩

theorem actual_empty_band_cannot_supply_any_confidence_or_safety_witness :
    ¬∃ value : ℝ, value ∈ (∅ : Set ℝ) := by simp

end SafeLearning.CompleteFoundationsSafeOptExtendedBands
