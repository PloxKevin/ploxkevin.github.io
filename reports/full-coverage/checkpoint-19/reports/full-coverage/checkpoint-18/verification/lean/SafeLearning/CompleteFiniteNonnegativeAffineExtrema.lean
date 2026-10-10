import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SafeLearning.CompleteFiniteNonnegativeAffineExtrema

variable {I J : Type*} [Fintype I] [Fintype J]

def AffineFeasible (L : (I → ℝ) →ₗ[ℝ] (J → ℝ)) (b : J → ℝ) (x : I → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ L x = b

theorem actual_supported_direction_has_positive_two_sided_feasible_step
    (x δ : I → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hsupport : ∀ i, ¬ 0 < x i → δ i = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε * |δ i| ≤ x i := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    letI := h
    exact ⟨1, zero_lt_one, fun i => isEmptyElim i⟩
  | inr h =>
    letI := h
    let radius (i : I) : ℝ := if 0 < x i then x i / (|δ i| + 1) else 1
    have hradius (i : I) : 0 < radius i := by
      by_cases hi : 0 < x i
      · simp only [radius, ite_eq_left hi]
        exact div_pos hi (by positivity)
      · simp [radius, hi]
    obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ radius Finset.univ_nonempty
    refine ⟨radius i₀, hradius i₀, ?_⟩
    intro i
    have hle := hmin i (Finset.mem_univ i)
    by_cases hi : 0 < x i
    · calc
        radius i₀ * |δ i| ≤ radius i * |δ i| :=
          mul_le_mul_of_nonneg_right hle (abs_nonneg _)
        _ ≤ radius i * (|δ i| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (hradius i).le
        _ = x i := by
          simp only [radius, if_pos hi]
          exact div_mul_cancel₀ _ (by positivity)
    · simpa [hsupport i hi] using hx i

theorem actual_extreme_nonnegative_affine_point_has_no_supported_kernel_direction
    (L : (I → ℝ) →ₗ[ℝ] (J → ℝ)) (b : J → ℝ) (x : I → ℝ)
    (hext : x ∈ Set.extremePoints ℝ {y | AffineFeasible L b y})
    (δ : I → ℝ) (hδ : L δ = 0) (hsupport : ∀ i, ¬ 0 < x i → δ i = 0) :
    δ = 0 := by
  obtain ⟨ε, hε, hbound⟩ :=
    actual_supported_direction_has_positive_two_sided_feasible_step x δ hext.1.1 hsupport
  have hminus : AffineFeasible L b (x - ε • δ) := by
    constructor
    · intro i
      change 0 ≤ x i - ε * δ i
      have h := mul_le_mul_of_nonneg_left (le_abs_self (δ i)) hε.le
      linarith [hbound i]
    · simp only [map_sub, map_smul, hδ, smul_zero, sub_zero]
      exact hext.1.2
  have hplus : AffineFeasible L b (x + ε • δ) := by
    constructor
    · intro i
      change 0 ≤ x i + ε * δ i
      have h := mul_le_mul_of_nonneg_left (neg_abs_le (δ i)) hε.le
      linarith [hbound i]
    · simp only [map_add, map_smul, hδ, smul_zero, add_zero]
      exact hext.1.2
  have hsegment : x ∈ openSegment ℝ (x - ε • δ) (x + ε • δ) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i
    change (1 / 2 : ℝ) * (x i - ε * δ i) + (1 / 2 : ℝ) * (x i + ε * δ i) = x i
    ring
  have heq := hext.2 hminus hplus hsegment
  funext i
  have hi := congrArg (fun y : I → ℝ => y i) heq
  change x i - ε * δ i = x i at hi
  have hz : ε * δ i = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hε)

abbrev PositiveSupport (x : I → ℝ) := {i : I // 0 < x i}

instance positiveSupportFintype (x : I → ℝ) : Fintype (PositiveSupport x) := by
  classical
  exact inferInstance

def supportExtension (x : I → ℝ) (v : PositiveSupport x → ℝ) (i : I) : ℝ := by
  classical
  exact if h : 0 < x i then v ⟨i, h⟩ else 0

def supportExtensionLinearMap (x : I → ℝ) :
    (PositiveSupport x → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun := supportExtension x
  map_add' v w := by
    classical
    ext i
    change supportExtension x (v + w) i = supportExtension x v i + supportExtension x w i
    by_cases hi : 0 < x i <;> simp [supportExtension, hi]
  map_smul' c v := by
    classical
    ext i
    change supportExtension x (c • v) i = c * supportExtension x v i
    by_cases hi : 0 < x i <;> simp [supportExtension, hi]

theorem actual_support_extension_is_injective (x : I → ℝ) :
    Function.Injective (supportExtensionLinearMap x) := by
  classical
  intro v w h
  funext i
  rcases i with ⟨i, hi⟩
  have he := congrArg (fun y : I → ℝ => y i) h
  simpa [supportExtensionLinearMap, supportExtension, hi] using he

theorem actual_extreme_point_positive_support_linear_map_is_injective
    (L : (I → ℝ) →ₗ[ℝ] (J → ℝ)) (b : J → ℝ) (x : I → ℝ)
    (hext : x ∈ Set.extremePoints ℝ {y | AffineFeasible L b y}) :
    Function.Injective (L.comp (supportExtensionLinearMap x)) := by
  classical
  intro v w h
  have hk : L (supportExtensionLinearMap x (v - w)) = 0 := by
    change (L.comp (supportExtensionLinearMap x)) (v - w) = 0
    rw [map_sub, h, sub_self]
  have hz := actual_extreme_nonnegative_affine_point_has_no_supported_kernel_direction
    L b x hext (supportExtensionLinearMap x (v - w)) hk
    (fun i hi => by simp [supportExtensionLinearMap, supportExtension, hi])
  have he : supportExtensionLinearMap x (v - w) = supportExtensionLinearMap x 0 := by
    rw [hz, map_zero]
  exact sub_eq_zero.mp (actual_support_extension_is_injective x he)

theorem actual_extreme_point_positive_support_cardinality_bound
    (L : (I → ℝ) →ₗ[ℝ] (J → ℝ)) (b : J → ℝ) (x : I → ℝ)
    (hext : x ∈ Set.extremePoints ℝ {y | AffineFeasible L b y}) :
    Fintype.card (PositiveSupport x) ≤ Fintype.card J := by
  classical
  have h := LinearMap.finrank_le_finrank_of_injective
    (actual_extreme_point_positive_support_linear_map_is_injective L b x hext)
  simpa only [Module.finrank_fintype_fun_eq_card] using h

end SafeLearning.CompleteFiniteNonnegativeAffineExtrema
