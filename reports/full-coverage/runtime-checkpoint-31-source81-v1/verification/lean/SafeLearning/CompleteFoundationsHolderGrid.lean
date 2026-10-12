import SafeLearning.CompleteFoundationsGridCertificates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace SafeLearning.CompleteFoundationsHolderGrid

open Set
open scoped NNReal
open CompleteFoundationsGridCertificates

/-- The covering radius is the smallest distance bound for the actual five-node grid. -/
theorem actual_source_grid_covers (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    ∃ i : Fin 5, dist x (sourceGrid i) ≤ 1/4 := by
  simp only [mem_Icc] at hx
  by_cases h0 : x ≤ 1/4
  · refine ⟨0,?_⟩
    norm_num [sourceGrid,Real.dist_eq,abs_le]
    constructor <;> linarith [hx.1]
  by_cases h1 : x ≤ 3/4
  · refine ⟨1,?_⟩
    norm_num [sourceGrid,Real.dist_eq,abs_le]
    constructor <;> linarith
  by_cases h2 : x ≤ 5/4
  · refine ⟨2,?_⟩
    norm_num [sourceGrid,Real.dist_eq,abs_le]
    constructor <;> linarith
  by_cases h3 : x ≤ 7/4
  · refine ⟨3,?_⟩
    norm_num [sourceGrid,Real.dist_eq,abs_le]
    constructor <;> linarith
  · refine ⟨4,?_⟩
    norm_num [sourceGrid,Real.dist_eq,abs_le]
    constructor <;> linarith [hx.2]

theorem actual_source_covering_radius :
    IsLeast {r : ℝ | ∀ x ∈ Icc (0 : ℝ) 2, ∃ i : Fin 5,
      dist x (sourceGrid i) ≤ r} (1/4) := by
  refine ⟨actual_source_grid_covers,?_⟩
  intro r hr
  rcases hr (1/4) (by norm_num) with ⟨i,hi⟩
  have hl : (1/4 : ℝ) ≤ dist (1/4) (sourceGrid i) := by
    fin_cases i <;> norm_num [sourceGrid,Real.dist_eq]
  exact hl.trans hi

theorem actual_uniform_grid_threshold_and_failures :
    (3/2 : ℝ)*(1/4) = 3/8 ∧
    (∀ i : Fin 5, 3/8 ≤ sourceLower i ↔ i ≠ 2 ∧ i ≠ 3) ∧
    ¬ (∀ i : Fin 5, 3/8 ≤ sourceLower i) := by
  refine ⟨by norm_num,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [sourceLower]
  · intro h
    have h2 := h 2
    norm_num [sourceLower] at h2

theorem actual_sqrt_add_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a+b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity,?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

theorem actual_sqrt_distance_triangle (x y g : ℝ) :
    Real.sqrt (dist x g) ≤ Real.sqrt (dist x y) + Real.sqrt (dist y g) := by
  exact (Real.sqrt_le_sqrt (dist_triangle x y g)).trans
    (actual_sqrt_add_bound _ _ dist_nonneg dist_nonneg)

/-- The square-root modulus in the question, with the legitimate domain explicit. -/
def HolderCompatible (L : ℝ≥0) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ (L : ℝ)*Real.sqrt (dist x y)

noncomputable def holderCone (L : ℝ≥0) (g ell x : ℝ) : ℝ :=
  ell - (L : ℝ)*Real.sqrt (dist x g)

noncomputable def holderEnvelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => holderCone L (g i) (ell i) x)

theorem actual_holder_cone_le_envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (x : ℝ) (i : ι) :
    holderCone L (g i) (ell i) x ≤ holderEnvelope L g ell x := by
  exact Finset.le_sup' (fun j : ι => holderCone L (g j) (ell j) x) (Finset.mem_univ i)

theorem actual_holder_cone_one_sided (L : ℝ≥0) (g ell x y : ℝ) :
    holderCone L g ell x ≤ holderCone L g ell y +
      (L : ℝ)*Real.sqrt (dist x y) := by
  have h := actual_sqrt_distance_triangle y x g
  rw [dist_comm y x] at h
  dsimp [holderCone]
  nlinarith [L.coe_nonneg]

theorem actual_holder_envelope_one_sided {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (x y : ℝ) :
    holderEnvelope L g ell x ≤ holderEnvelope L g ell y +
      (L : ℝ)*Real.sqrt (dist x y) := by
  apply Finset.sup'_le
  intro i _
  have h := actual_holder_cone_one_sided L (g i) (ell i) x y
  linarith [actual_holder_cone_le_envelope L g ell y i]

theorem actual_holder_envelope_has_modulus {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (s : Set ℝ) :
    HolderCompatible L s (holderEnvelope L g ell) := by
  intro x _ y _
  rw [abs_sub_le_iff]
  constructor
  · linarith [actual_holder_envelope_one_sided L g ell x y]
  · have h := actual_holder_envelope_one_sided L g ell y x
    rw [dist_comm y x] at h
    linarith

theorem actual_holder_envelope_lower_measurements {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (i : ι) : ell i ≤ holderEnvelope L g ell (g i) := by
  simpa [holderCone] using actual_holder_cone_le_envelope L g ell (g i) i

theorem actual_holder_envelope_is_smallest {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ≥0) (g ell : ι → ℝ) (s : Set ℝ) (f : ℝ → ℝ)
    (hg : ∀ i, g i ∈ s) (hf : HolderCompatible L s f)
    (hmeasure : ∀ i, ell i ≤ f (g i)) {x : ℝ} (hx : x ∈ s) :
    holderEnvelope L g ell x ≤ f x := by
  apply Finset.sup'_le
  intro i _
  have h := hf (g i) (hg i) x hx
  rw [dist_comm (g i) x] at h
  have h1 := le_abs_self (f (g i) - f x)
  dsimp [holderCone]
  linarith [hmeasure i]

theorem actual_holder_cone_radius (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (g ell x : ℝ) (hell : 0 ≤ ell) :
    0 ≤ holderCone L g ell x ↔ dist x g ≤ (ell/(L : ℝ))^2 := by
  have hquot : 0 ≤ ell/(L : ℝ) := div_nonneg hell L.coe_nonneg
  rw [← Real.sqrt_le_left hquot, le_div_iff₀ hL]
  dsimp [holderCone]
  constructor <;> intro h <;> nlinarith

noncomputable def sourceHolderEnvelope : ℝ → ℝ :=
  holderEnvelope (3/2) sourceGrid sourceLower

def SourceHolderCompatible (f : ℝ → ℝ) : Prop :=
  HolderCompatible (3/2) (Icc 0 2) f ∧ ∀ i, sourceLower i ≤ f (sourceGrid i)

theorem actual_source_holder_envelope_compatible : SourceHolderCompatible sourceHolderEnvelope := by
  exact ⟨actual_holder_envelope_has_modulus (3/2) sourceGrid sourceLower _,
    actual_holder_envelope_lower_measurements (3/2) sourceGrid sourceLower⟩

theorem actual_source_holder_certificate_is_exact (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    (∀ f : ℝ → ℝ, SourceHolderCompatible f → 0 ≤ f x) ↔ 0 ≤ sourceHolderEnvelope x := by
  constructor
  · intro h
    exact h sourceHolderEnvelope actual_source_holder_envelope_compatible
  · intro h f hf
    exact h.trans (actual_holder_envelope_is_smallest (3/2) sourceGrid sourceLower
      (Icc 0 2) f actual_source_grid_in_domain hf.1 hf.2 hx)

theorem actual_source_holder_radii :
    (fun i => (sourceLower i / (3/2 : ℝ))^2) = ![1/9, 9/100, 1/25, 4/225, 4/25] := by
  funext i
  fin_cases i <;> norm_num [sourceLower]

theorem actual_source_holder_radii_strictly_smaller (i : Fin 5) :
    0 < (sourceLower i/(3/2 : ℝ))^2 ∧
    (sourceLower i/(3/2 : ℝ))^2 < sourceLower i/(3/2 : ℝ) := by
  fin_cases i <;> norm_num [sourceLower]

theorem actual_source_holder_certificate_intervals (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    0 ≤ sourceHolderEnvelope x ↔
      x ∈ Icc (0 : ℝ) (1/9) ∨ x ∈ Icc (41/100 : ℝ) (59/100) ∨
      x ∈ Icc (24/25 : ℝ) (26/25) ∨ x ∈ Icc (667/450 : ℝ) (683/450) ∨
      x ∈ Icc (46/25 : ℝ) 2 := by
  change 0 ≤ Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin 5 => holderCone (3/2) (sourceGrid i) (sourceLower i) x) ↔ _
  simp only [Finset.le_sup'_iff, Finset.mem_univ, true_and]
  have hi (i : Fin 5) : 0 ≤ holderCone (3/2) (sourceGrid i) (sourceLower i) x ↔
      sourceGrid i - (sourceLower i/(3/2 : ℝ))^2 ≤ x ∧
      x ≤ sourceGrid i + (sourceLower i/(3/2 : ℝ))^2 := by
    rw [actual_holder_cone_radius (3/2) (by norm_num) _ _ _
      (by fin_cases i <;> norm_num [sourceLower]), Real.dist_eq, abs_le]
    norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  simp only [hi]
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false, sourceGrid, sourceLower,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  simp only [mem_Icc] at *
  constructor
  · rintro (h | h | h | h | h)
    · exact Or.inl ⟨hx.1,h.2⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1,hx.2⟩)))
  · rintro (h | h | h | h | h)
    · exact Or.inl ⟨by linarith [h.1],h.2⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1,by linarith [h.2]⟩)))

theorem actual_holder_printed_radii_not_exact :
    (1/9 : ℝ) ≠ 0.111 ∧ (4/225 : ℝ) ≠ 0.018 := by
  norm_num

end SafeLearning.CompleteFoundationsHolderGrid
