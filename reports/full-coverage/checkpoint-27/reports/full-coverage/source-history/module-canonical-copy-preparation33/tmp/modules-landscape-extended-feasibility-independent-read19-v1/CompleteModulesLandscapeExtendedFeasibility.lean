import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLandscapeExtendedFeasibility

def extendedSup {E : Type*} (U : Set E) (f : E → ℝ) : EReal :=
  sSup ((fun u => (f u:EReal)) '' U)

theorem actual_positive_extended_supremum_supplies_a_strictly_feasible_input
    {E : Type*} (U : Set E) (f : E → ℝ)
    (hsup : (0:EReal)<extendedSup U f) : ∃u∈U, 0<f u := by
  obtain ⟨y,⟨u,hu,rfl⟩,hy⟩ := lt_sSup_iff.mp hsup
  exact ⟨u,hu,by change (0:EReal)<(f u:EReal) at hy; exact EReal.coe_lt_coe_iff.mp hy⟩

theorem actual_nonnegative_extended_supremum_excludes_an_empty_input_set
    {E : Type*} (U : Set E) (f : E → ℝ)
    (hsup : (0:EReal)≤extendedSup U f) : U.Nonempty := by
  by_contra hn
  have he : U=∅ := not_nonempty_iff_eq_empty.mp hn
  simp [extendedSup,he] at hsup

theorem actual_compact_continuous_nonnegative_extended_supremum_supplies_a_maximizing_feasible_input
    {E : Type*} [TopologicalSpace E] (U : Set E) (f : E → ℝ)
    (hc : IsCompact U) (hf : ContinuousOn f U)
    (hsup : (0:EReal)≤extendedSup U f) :
    ∃u∈U, IsMaxOn f U u ∧ 0≤f u ∧ extendedSup U f=(f u:EReal) := by
  have hne := actual_nonnegative_extended_supremum_excludes_an_empty_input_set U f hsup
  obtain ⟨u,hu,hm⟩ := hc.exists_isMaxOn hne hf
  have hg : IsGreatest ((fun v => (f v:EReal)) '' U) (f u:EReal) := by
    refine ⟨mem_image_of_mem _ hu,?_⟩
    rintro y ⟨v,hv,rfl⟩
    exact EReal.coe_le_coe (hm hv)
  have he : extendedSup U f=(f u:EReal) := hg.isLUB.sSup_eq
  refine ⟨u,hu,hm,?_,he⟩
  rw [he] at hsup
  exact_mod_cast hsup

theorem actual_nonconstant_affine_objective_has_extended_supremum_top_and_feasible_inputs
    (a b : ℝ) (hb : b≠0) :
    extendedSup (univ: Set ℝ) (fun u => a+b*u)=⊤ ∧
      ∃u : ℝ, 0<a+b*u := by
  have he : (fun u : ℝ => ((a+b*u:ℝ):EReal)) '' univ=Set.range (fun y : ℝ => (y:EReal)) := by
    ext y
    constructor
    · rintro ⟨u,_,rfl⟩
      exact ⟨a+b*u,rfl⟩
    · rintro ⟨v,rfl⟩
      refine ⟨(v-a)/b,mem_univ _,?_⟩
      congr 1
      field_simp [hb]
      ring
  have hl : sSup (Set.range (fun y : ℝ => (y:EReal)))=⊤ := by
    apply top_le_iff.mp
    by_contra hn
    have hlt : sSup (Set.range (fun y : ℝ => (y:EReal)))<⊤ := lt_of_not_ge hn
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real hlt
    have hbnd : (r:EReal) ≤ sSup (Set.range (fun y : ℝ => (y:EReal))) := le_sSup ⟨r,rfl⟩
    exact not_lt_of_ge hbnd hr
  have hs : extendedSup (univ:Set ℝ) (fun u => a+b*u)=⊤ := by
    unfold extendedSup
    rw [he,hl]
  refine ⟨hs,?_⟩
  obtain ⟨u,_,hu⟩ := actual_positive_extended_supremum_supplies_a_strictly_feasible_input
    (univ:Set ℝ) (fun u => a+b*u) (by rw [hs]; exact EReal.coe_lt_top 0)
  exact ⟨u,hu⟩
end SafeLearning.CompleteModulesLandscapeExtendedFeasibility
