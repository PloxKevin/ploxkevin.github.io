import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesSafeOptPracticeTheorems

theorem actual_metric_lipschitz_lower_confidence_transfer {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (constant : NNReal) (hf : LipschitzWith constant f)
    (anchor candidate : X) (lower : ℝ) (hl : lower ≤ f anchor) :
    lower-constant*dist anchor candidate ≤ f candidate := by
  have h := hf.dist_le_mul anchor candidate
  rw [Real.dist_eq] at h
  have hb := (abs_le.mp h).2
  linarith

def actualExpansion {X : Type*} [PseudoMetricSpace X] (old : Set X)
    (lower : X → ℝ) (constant : NNReal) (threshold : ℝ) : Set X :=
  {candidate | ∃ anchor ∈ old, threshold ≤ lower anchor-constant*dist anchor candidate}

def actualRounds {X : Type*} [PseudoMetricSpace X] (seed : Set X)
    (lower : ℕ → X → ℝ) (constant : NNReal) (threshold : ℝ) : ℕ → Set X
  | 0 => seed
  | n+1 => actualExpansion (actualRounds seed lower constant threshold n) (lower (n+1)) constant threshold

theorem actual_joint_confidence_and_safe_seed_prove_every_expanded_round_and_every_selected_query_safe
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (constant : NNReal)
    (hf : LipschitzWith constant f) (threshold : ℝ) (seed : Set X)
    (lower : ℕ → X → ℝ) (hconfidence : ∀ n x, lower n x ≤ f x)
    (hseed : ∀ x ∈ seed, threshold ≤ f x) :
    (∀ n x, x ∈ actualRounds seed lower constant threshold n → threshold ≤ f x) ∧
      ∀ query : ℕ → X, (∀ n, query n ∈ actualRounds seed lower constant threshold n) →
        ∀ n, threshold ≤ f (query n) := by
  have hs : ∀ n x, x ∈ actualRounds seed lower constant threshold n → threshold ≤ f x := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n _ =>
      intro candidate hc
      obtain ⟨anchor,_ha,hcertificate⟩ := hc
      exact hcertificate.trans (actual_metric_lipschitz_lower_confidence_transfer
        f constant hf anchor candidate (lower (n+1) anchor) (hconfidence (n+1) anchor))
  refine ⟨hs,?_⟩
  intro query hq n
  exact hs n (query n) (hq n)

theorem actual_source_quarter_radius_certifies_the_threshold_including_its_boundary
    (f : ℝ → ℝ) (hf : LipschitzWith (2:NNReal) f) (anchor candidate : ℝ)
    (hl : (3/5:ℝ) ≤ f anchor) (hd : |anchor-candidate| ≤ (1/4:ℝ)) :
    (1/10:ℝ) ≤ f candidate := by
  have h := actual_metric_lipschitz_lower_confidence_transfer f 2 hf anchor candidate (3/5) hl
  norm_num only [Real.dist_eq,NNReal.coe_ofNat] at h
  linarith

def sourceQueryValue (i : Fin 4) : ℝ := ![2,3,4,3] i

theorem actual_source_query_regrets_cumulative_average_and_final_simple_regret :
    (∀ i : Fin 4, (5-sourceQueryValue i)=(![3,2,1,2] : Fin 4 → ℝ) i) ∧
      (∑ i : Fin 4,(5-sourceQueryValue i))=8 ∧
      (∑ i : Fin 4,(5-sourceQueryValue i))/4=2 ∧ (5:ℝ)-24/5=1/5 := by
  refine ⟨?_,?_,?_,by norm_num⟩
  · intro i
    fin_cases i <;> norm_num [sourceQueryValue]
  · norm_num [sourceQueryValue,Fin.sum_univ_succ]
  · norm_num [sourceQueryValue,Fin.sum_univ_succ]

theorem actual_repeating_the_value_two_query_adds_three_per_repeat_without_changing_simple_regret
    (repeats : ℕ) :
    (∑ i : Fin 4,(5-sourceQueryValue i))+(∑ _i ∈ Finset.range repeats,((5:ℝ)-2))=8+3*repeats ∧
      (5:ℝ)-24/5=1/5 := by
  norm_num [sourceQueryValue,Fin.sum_univ_succ,Finset.sum_const]
  ring

theorem actual_fixed_finite_comparison_set_has_a_true_maximum_with_the_source_interval_gap_bound
    {X : Type*} [Fintype X] (comparison : Set X) (f lower upper : X → ℝ)
    (recommendation : X) (hr : recommendation ∈ comparison)
    (hl : ∀ x ∈ comparison, lower x ≤ f x) (hu : ∀ x ∈ comparison, f x ≤ upper x)
    (hupper : IsGreatest (upper '' comparison) (11/10:ℝ))
    (hlower : lower recommendation=(51/50:ℝ)) :
    ∃ maximum : ℝ, IsGreatest (f '' comparison) maximum ∧
      maximum-f recommendation ≤ (2/25:ℝ) := by
  have hc : IsCompact (f '' comparison) := (comparison.toFinite.image f).isCompact
  have hn : (f '' comparison).Nonempty := ⟨f recommendation,⟨recommendation,hr,rfl⟩⟩
  obtain ⟨maximum,hm⟩ := hc.exists_isGreatest hn
  refine ⟨maximum,hm,?_⟩
  obtain ⟨winner,hw,hvalue⟩ := hm.1
  have hwupper := hupper.2 (show upper winner ∈ upper '' comparison from ⟨winner,hw,rfl⟩)
  have hwf := hu winner hw
  have hrlo := hl recommendation hr
  rw [hlower] at hrlo
  linarith

theorem actual_grid_values_and_covering_margin_prove_the_source_positive_margin_on_every_design_point
    {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (hf : LipschitzWith (2:NNReal) f)
    (design grid : Set X) (hgrid : ∀ z ∈ grid, (3/25:ℝ) ≤ f z)
    (hcover : ∀ x ∈ design, ∃ z ∈ grid, dist z x ≤ (1/20:ℝ)) :
    ∀ x ∈ design, (1/50:ℝ) ≤ f x := by
  intro x hx
  obtain ⟨z,hz,hd⟩ := hcover x hx
  have h := actual_metric_lipschitz_lower_confidence_transfer f 2 hf z x (3/25) (hgrid z hz)
  norm_num only [NNReal.coe_ofNat] at h
  linarith

theorem actual_nonnegative_grid_values_can_fail_between_points_despite_the_true_lipschitz_and_cover_bounds :
    LipschitzWith (2:NNReal) (fun x : ℝ => -2*x) ∧
      (∀ x ∈ Icc (0:ℝ) (1/20), ∃ z ∈ ({0}:Set ℝ), dist z x ≤ (1/20:ℝ)) ∧
      (∀ z ∈ ({0}:Set ℝ), 0 ≤ -2*z) ∧ -2*(1/20:ℝ)=(-1/10) ∧
      (1/20:ℝ) ∈ Icc (0:ℝ) (1/20) := by
  refine ⟨?_,?_,?_,by norm_num,by norm_num⟩
  · rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [Real.dist_eq]
    rw [← mul_sub,abs_mul]
    norm_num
  · intro x hx
    refine ⟨0,rfl,?_⟩
    rw [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg hx.1]
    exact hx.2
  · intro z hz
    have h : z=0 := hz
    rw [h]
    norm_num

end SafeLearning.CompleteModulesSafeOptPracticeTheorems
