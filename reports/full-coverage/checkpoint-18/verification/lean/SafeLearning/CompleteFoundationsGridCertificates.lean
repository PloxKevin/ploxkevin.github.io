import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SafeLearning.CompleteFoundationsGridCertificates

open Set
open scoped NNReal

/-- The pointwise lower cone determined by one actual lower measurement. -/
def cone (L : ℝ≥0) (g ell x : ℝ) : ℝ := ell - (L : ℝ) * dist x g

/-- The true maximum of all the measured lower cones, with no added zero floor. -/
noncomputable def envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => cone L (g i) (ell i) x)

theorem actual_cone_lipschitz (L : ℝ≥0) (g ell : ℝ) :
    LipschitzWith L (cone L g ell) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  have h := dist_triangle y x g
  rw [dist_comm y x] at h
  have hL := L.coe_nonneg
  dsimp [cone]
  nlinarith

theorem actual_cone_le_envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (x : ℝ) (i : ι) :
    cone L (g i) (ell i) x ≤ envelope L g ell x := by
  exact Finset.le_sup' (fun j : ι => cone L (g j) (ell j) x) (Finset.mem_univ i)

theorem actual_envelope_lipschitz {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) : LipschitzWith L (envelope L g ell) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  apply Finset.sup'_le
  intro i _
  have h := (actual_cone_lipschitz L (g i) (ell i)).le_add_mul x y
  linarith [actual_cone_le_envelope L g ell y i]

theorem actual_envelope_satisfies_every_lower_measurement
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (i : ι) : ell i ≤ envelope L g ell (g i) := by
  simpa [cone] using actual_cone_le_envelope L g ell (g i) i

theorem actual_envelope_is_smallest_compatible_function
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (s : Set ℝ) (f : ℝ → ℝ)
    (hg : ∀ i, g i ∈ s) (hf : LipschitzOnWith L f s)
    (hmeasure : ∀ i, ell i ≤ f (g i)) {x : ℝ} (hx : x ∈ s) :
    envelope L g ell x ≤ f x := by
  apply Finset.sup'_le
  intro i _
  have h := hf.dist_le_mul (g i) (hg i) x hx
  have hlo := le_abs_self (f (g i) - f x)
  rw [Real.dist_eq, dist_comm (g i) x] at h
  dsimp [cone]
  linarith [hmeasure i]

theorem actual_nonnegative_envelope_iff_one_lower_cone
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (x : ℝ) :
    0 ≤ envelope L g ell x ↔ ∃ i, 0 ≤ cone L (g i) (ell i) x := by
  simp [envelope, Finset.le_sup'_iff]

theorem actual_cone_radius_iff (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (g ell x : ℝ) :
    0 ≤ cone L g ell x ↔ dist x g ≤ ell / (L : ℝ) := by
  rw [le_div_iff₀ hL]
  dsimp [cone]
  constructor <;> intro h <;> nlinarith

noncomputable def sourceGrid : Fin 5 → ℝ := ![0, 1/2, 1, 3/2, 2]
noncomputable def sourceLower : Fin 5 → ℝ := ![1/2, 9/20, 3/10, 1/5, 3/5]
noncomputable def sourceEnvelope : ℝ → ℝ := envelope (3/2) sourceGrid sourceLower

def SourceCompatible (f : ℝ → ℝ) : Prop :=
  LipschitzOnWith (3/2) f (Icc 0 2) ∧ ∀ i, sourceLower i ≤ f (sourceGrid i)

theorem actual_source_grid_in_domain (i : Fin 5) : sourceGrid i ∈ Icc (0 : ℝ) 2 := by
  fin_cases i <;> norm_num [sourceGrid]

theorem actual_source_envelope_compatible : SourceCompatible sourceEnvelope := by
  constructor
  · exact (actual_envelope_lipschitz (3/2) sourceGrid sourceLower).lipschitzOnWith
  · exact actual_envelope_satisfies_every_lower_measurement (3/2) sourceGrid sourceLower

theorem actual_source_certificate_is_exact (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    (∀ f : ℝ → ℝ, SourceCompatible f → 0 ≤ f x) ↔ 0 ≤ sourceEnvelope x := by
  constructor
  · intro h
    exact h sourceEnvelope actual_source_envelope_compatible
  · intro h f hf
    exact h.trans (actual_envelope_is_smallest_compatible_function (3/2)
      sourceGrid sourceLower (Icc 0 2) f actual_source_grid_in_domain hf.1 hf.2 hx)

theorem actual_source_radii :
    (fun i => sourceLower i / (3/2 : ℝ)) = ![1/3, 3/10, 1/5, 2/15, 2/5] := by
  funext i
  fin_cases i <;> norm_num [sourceLower]

theorem actual_source_cones_iff_five_intervals (x : ℝ) :
    0 ≤ sourceEnvelope x ↔
      x ∈ Icc (-1/3 : ℝ) (1/3) ∨ x ∈ Icc (1/5 : ℝ) (4/5) ∨
      x ∈ Icc (4/5 : ℝ) (6/5) ∨ x ∈ Icc (41/30 : ℝ) (49/30) ∨
      x ∈ Icc (8/5 : ℝ) (12/5) := by
  rw [sourceEnvelope, actual_nonnegative_envelope_iff_one_lower_cone]
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false, sourceGrid, sourceLower,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  have hrad (g ell : ℝ) : 0 ≤ cone (3/2) g ell x ↔
      g - ell / (3/2 : ℝ) ≤ x ∧ x ≤ g + ell / (3/2 : ℝ) := by
    rw [actual_cone_radius_iff (3/2) (by norm_num), Real.dist_eq, abs_le]
    norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  simp only [hrad, mem_Icc]
  norm_num

theorem actual_source_union (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    0 ≤ sourceEnvelope x ↔ x ∈ Icc (0 : ℝ) (6/5) ∪ Icc (41/30 : ℝ) 2 := by
  rw [actual_source_cones_iff_five_intervals]
  simp only [mem_Icc, mem_union] at *
  constructor
  · rintro (h | h | h | h | h)
    · exact Or.inl ⟨hx.1, by linarith [h.2]⟩
    · exact Or.inl ⟨hx.1, by linarith [h.2]⟩
    · exact Or.inl ⟨hx.1, h.2⟩
    · exact Or.inr ⟨h.1, hx.2⟩
    · exact Or.inr ⟨by linarith [h.1], hx.2⟩
  · rintro (h | h)
    · by_cases h1 : x ≤ 1/3
      · exact Or.inl ⟨by linarith [hx.1], h1⟩
      · by_cases h2 : x ≤ 4/5
        · exact Or.inr (Or.inl ⟨by linarith, h2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨by linarith, h.2⟩))
    · by_cases h1 : x ≤ 49/30
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h1⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith [hx.2]⟩)))

theorem actual_gap_has_a_compatible_unsafe_witness (x : ℝ)
    (hx : x ∈ Ioo (6/5 : ℝ) (41/30)) :
    ∃ f : ℝ → ℝ, SourceCompatible f ∧ f x < 0 := by
  refine ⟨sourceEnvelope, actual_source_envelope_compatible, ?_⟩
  have domain : x ∈ Icc (0 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  apply lt_of_not_ge
  rw [actual_source_union x domain]
  simp only [mem_union, mem_Icc]
  rintro (h | h) <;> linarith [hx.1, hx.2]

theorem actual_printed_second_endpoint_is_not_exact : (41/30 : ℝ) ≠ 1.367 := by
  norm_num

end SafeLearning.CompleteFoundationsGridCertificates
