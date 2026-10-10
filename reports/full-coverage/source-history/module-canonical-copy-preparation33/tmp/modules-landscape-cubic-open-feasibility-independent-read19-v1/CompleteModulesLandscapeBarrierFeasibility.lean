import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace SafeLearning.CompleteModulesLandscapeBarrierFeasibility

theorem actual_compact_nonempty_admissible_set_attains_its_supremum
    {E : Type*} [TopologicalSpace E] (U : Set E) (f : E → ℝ)
    (hc : IsCompact U) (hne : U.Nonempty) (hf : ContinuousOn f U) :
    ∃u ∈ U, IsGreatest (f '' U) (f u) ∧ sSup (f '' U)=f u := by
  obtain ⟨u,hu,hm⟩ := hc.exists_isMaxOn hne hf
  have hg : IsGreatest (f '' U) (f u) := by
    refine ⟨mem_image_of_mem f hu,?_⟩
    rintro y ⟨v,hv,rfl⟩
    exact hm hv
  exact ⟨u,hu,hg,hg.csSup_eq⟩

theorem actual_compact_nonnegative_supremum_supplies_a_feasible_input
    {E : Type*} [TopologicalSpace E] (U : Set E) (f : E → ℝ)
    (hc : IsCompact U) (hne : U.Nonempty) (hf : ContinuousOn f U)
    (hsup : 0 ≤ sSup (f '' U)) : ∃u ∈ U, 0 ≤ f u := by
  obtain ⟨u,hu,_,he⟩ := actual_compact_nonempty_admissible_set_attains_its_supremum U f hc hne hf
  exact ⟨u,hu,he ▸ hsup⟩

theorem actual_positive_supremum_supplies_a_strictly_feasible_input
    {E : Type*} (U : Set E) (f : E → ℝ) (hne : U.Nonempty)
    (hsup : 0 < sSup (f '' U)) : ∃u ∈ U, 0 < f u := by
  obtain ⟨y,⟨u,hu,rfl⟩,hy⟩ := exists_lt_of_lt_csSup (hne.image f) hsup
  exact ⟨u,hu,hy⟩

theorem actual_nonconstant_unrestricted_affine_objective_supplies_an_input
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (b : E) (hb : b ≠ 0) :
    ∃u : E, 0 < a+⟪b,u⟫ := by
  have hp : 0 < ⟪b,b⟫ := (real_inner_self_pos (x:=b)).mpr hb
  refine ⟨((1-a)/⟪b,b⟫) • b,?_⟩
  rw [real_inner_smul_right]
  have he : a+((1-a)/⟪b,b⟫)*⟪b,b⟫=1 := by field_simp; ring
  rw [he]
  norm_num

def openInputs : Set ℝ := Ioo 0 1
def openObjective (u : ℝ) : ℝ := -1+u

theorem actual_open_admissible_objective_has_exact_range_and_zero_unattained_supremum :
    openObjective '' openInputs=Ioo (-1) 0 ∧
      IsLUB (openObjective '' openInputs) 0 ∧
      sSup (openObjective '' openInputs)=0 ∧
      ¬∃u ∈ openInputs, 0 ≤ openObjective u := by
  have he : openObjective '' openInputs=Ioo (-1) 0 := by
    ext y
    constructor
    · rintro ⟨u,hu,rfl⟩
      change 0<u ∧ u<1 at hu
      change -1 < -1+u ∧ -1+u<0
      constructor <;> linarith [hu.1,hu.2]
    · intro hy
      refine ⟨y+1,?_,by simp [openObjective]⟩
      change 0<y+1 ∧ y+1<1
      constructor <;> linarith [hy.1,hy.2]
  refine ⟨he,?_,?_,?_⟩
  · rw [he]
    exact isLUB_Ioo (by norm_num)
  · rw [he]
    exact csSup_Ioo (by norm_num)
  · rintro ⟨u,hu,hs⟩
    change 0<u ∧ u<1 at hu
    change 0 ≤ -1+u at hs
    linarith [hu.2]

theorem actual_open_input_source_barrier_is_infeasible_at_the_boundary :
    HasDerivAt (fun x : ℝ => x) 1 0 ∧
      (∀u ∈ openInputs, 1*(-1+u)+(0:ℝ)<0) ∧
      ¬∃u ∈ openInputs, 0 ≤ 1*(-1+u)+(0:ℝ) := by
  refine ⟨hasDerivAt_id 0,?_,?_⟩
  · intro u hu
    change 0<u ∧ u<1 at hu
    linarith [hu.2]
  · simpa [openObjective] using
      actual_open_admissible_objective_has_exact_range_and_zero_unattained_supremum.2.2.2

end SafeLearning.CompleteModulesLandscapeBarrierFeasibility
