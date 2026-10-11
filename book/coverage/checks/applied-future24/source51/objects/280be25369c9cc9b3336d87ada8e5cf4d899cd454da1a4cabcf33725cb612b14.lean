import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace SafeLearning.CompleteFoundationsSemicontinuity23

theorem actual_lower_semicontinuity_iff_closed_sublevels
    {X : Type*} [TopologicalSpace X] (f : X → ℝ) :
    LowerSemicontinuous f ↔ ∀ c : ℝ, IsClosed {x | f x ≤ c} := by
  simpa only [preimage, mem_Iic] using (lowerSemicontinuous_iff_isClosed_preimage (f:=f))

theorem actual_lower_semicontinuity_iff_all_sequence_liminf_bounds
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] (f : X → ℝ) :
    LowerSemicontinuous f ↔ ∀ (x : X) (u : ℕ → X), Tendsto u atTop (𝓝 x) →
      (f x : EReal) ≤ liminf (fun n => (f (u n) : EReal)) atTop := by
  constructor
  · intro hf x u hu
    apply le_of_forall_lt_imp_le_of_dense
    intro y hy
    cases y using EReal.rec with
    | bot => exact (bot_le : (⊥:EReal) ≤ _)
    | coe r =>
        have hr : r < f x := EReal.coe_lt_coe_iff.mp hy
        have he : ∀ᶠ n in atTop, (r:EReal) ≤ (f (u n):EReal) :=
          (hu.eventually (hf x r hr)).mono (fun n hn => EReal.coe_le_coe hn.le)
        exact le_liminf_of_le (by isBoundedDefault) he
    | top => exact False.elim (not_top_lt hy)
  · intro hs x
    apply LowerSemicontinuousAt.of_frequently
    intro r hr
    obtain ⟨u, hu, hb⟩ := exists_seq_forall_of_frequently hr
    have hlow := hs x u hu
    have hhigh : limsup (fun n => (f (u n):EReal)) atTop ≤ (r:EReal) :=
      limsup_le_of_le (by isBoundedDefault)
        (Eventually.of_forall (fun n => EReal.coe_le_coe (hb n)))
    have horder : liminf (fun n => (f (u n):EReal)) atTop ≤
        limsup (fun n => (f (u n):EReal)) atTop :=
      liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)
    exact EReal.coe_le_coe_iff.mp (hlow.trans (horder.trans hhigh))

theorem actual_lower_semicontinuous_compact_set_has_a_minimizer
    {X : Type*} [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (hne : K.Nonempty) (f : X → ℝ) (hf : LowerSemicontinuousOn f K) :
    ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  exact hf.exists_isMinOn hne hK

theorem actual_lower_semicontinuous_compact_sublevels_are_compact
    {X : Type*} [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (f : X → ℝ) (hf : LowerSemicontinuousOn f K) (c : ℝ) :
    IsCompact (K ∩ {x | f x ≤ c}) := by
  exact hf.isCompact_inter_preimage_Iic hK c

def step (x : ℝ) : ℝ := if x ≤ 0 then 0 else 1

theorem actual_printed_step_values :
    (∀ x : ℝ, x ≤ 0 → step x=0) ∧ (∀ x : ℝ, 0<x → step x=1) := by
  constructor
  · intro x hx; simp [step,hx]
  · intro x hx; simp [step,not_le.mpr hx]

theorem actual_printed_step_all_sublevel_sets (c : ℝ) :
    {x : ℝ | step x ≤ c} = if c<0 then ∅ else if c<1 then Iic 0 else univ := by
  ext x
  by_cases hc : c<0
  · simp only [hc,if_pos,mem_setOf_eq,mem_empty_iff_false]
    unfold step
    split_ifs <;> simp only [iff_false] <;> linarith
  · by_cases hc1 : c<1
    · simp only [hc,hc1,if_false,if_true,mem_setOf_eq,mem_Iic]
      unfold step
      split_ifs with hx
      · simp only [hx,iff_true];linarith
      · simp only [hx,iff_false];linarith
    · simp only [hc,hc1,if_false,mem_setOf_eq,mem_univ,iff_true]
      unfold step
      split_ifs <;> linarith

theorem actual_printed_step_is_lower_semicontinuous : LowerSemicontinuous step := by
  apply (actual_lower_semicontinuity_iff_closed_sublevels step).mpr
  intro c
  rw [actual_printed_step_all_sublevel_sets]
  split_ifs <;> first | exact isClosed_empty | exact isClosed_Iic | exact isClosed_univ

theorem actual_compactness_is_sufficient_for_continuous_minimum
    {X : Type*} [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (hne : K.Nonempty) (f : X → ℝ) (hf : ContinuousOn f K) :
    ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y :=
  hK.exists_isMinOn hne hf

theorem actual_real_line_is_not_compact : ¬IsCompact (univ : Set ℝ) := by
  intro hc
  obtain ⟨x, _, hx⟩ := hc.exists_isMaxOn univ_nonempty continuous_id.continuousOn
  have h := hx (mem_univ (x+1))
  change x+1≤x at h
  linarith

theorem actual_printed_square_attains_unique_minimum_on_noncompact_real_line :
    Continuous (fun x : ℝ => x^2) ∧ ¬IsCompact (univ : Set ℝ) ∧
      (∀ x : ℝ, (0:ℝ)^2≤x^2) ∧ (∀ x : ℝ, x^2=0 ↔ x=0) := by
  refine ⟨continuous_id.pow 2,actual_real_line_is_not_compact,?_,?_⟩
  · intro x;simpa only [zero_pow (by norm_num : 2≠0)] using sq_nonneg x
  · intro x;exact sq_eq_zero_iff

end SafeLearning.CompleteFoundationsSemicontinuity23
