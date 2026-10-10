import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace SafeLearning.CompleteModulesLandscapeAffineFeasibility
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def objective (a : ℝ) (b u : E) : ℝ := a+⟪b,u⟫
def admissibleSup (a : ℝ) (b : E) : EReal :=
  sSup ((fun u : E => (objective a b u:EReal)) '' univ)

theorem actual_nonzero_control_direction_realizes_every_affine_objective_value
    (a target : ℝ) (b : E) (hb : b≠0) :
    ∃u : E, objective a b u=target := by
  have hp : 0<⟪b,b⟫ := (real_inner_self_pos (x:=b)).mpr hb
  refine ⟨((target-a)/⟪b,b⟫) • b,?_⟩
  unfold objective
  rw [real_inner_smul_right]
  field_simp [ne_of_gt hp]
  ring

theorem actual_zero_control_direction_has_its_exact_constant_extended_supremum
    (a : ℝ) : admissibleSup a (0:E)=(a:EReal) := by
  have he : (fun u : E => (objective a (0:E) u:EReal)) '' univ={(a:EReal)} := by
    ext y
    constructor
    · rintro ⟨u,_,rfl⟩
      simp [objective]
    · intro hy
      have he : y=(a:EReal) := mem_singleton_iff.mp hy
      refine ⟨0,mem_univ _,?_⟩
      simp [objective,he]
  unfold admissibleSup
  rw [he,sSup_singleton]

theorem actual_unrestricted_nonnegative_affine_supremum_always_supplies_a_feasible_input
    (a : ℝ) (b : E) (hs : (0:EReal)≤admissibleSup a b) :
    ∃u : E, 0≤objective a b u := by
  by_cases hb : b=0
  · subst b
    rw [actual_zero_control_direction_has_its_exact_constant_extended_supremum] at hs
    have ha : 0≤a := by exact_mod_cast hs
    exact ⟨0,by simpa [objective] using ha⟩
  · obtain ⟨u,hu⟩ := actual_nonzero_control_direction_realizes_every_affine_objective_value a 1 b hb
    exact ⟨u,by rw [hu]; norm_num⟩

theorem actual_nonzero_control_direction_gives_no_maximum_even_though_it_is_feasible
    (a : ℝ) (b : E) (hb : b≠0) :
    (∃u : E, 0<objective a b u) ∧
      ¬∃u : E, IsMaxOn (objective a b) univ u := by
  constructor
  · obtain ⟨u,hu⟩ := actual_nonzero_control_direction_realizes_every_affine_objective_value a 1 b hb
    exact ⟨u,by rw [hu]; norm_num⟩
  · rintro ⟨u,hm⟩
    obtain ⟨v,hv⟩ := actual_nonzero_control_direction_realizes_every_affine_objective_value
      a (objective a b u+1) b hb
    have h := hm (mem_univ v)
    rw [hv] at h
    linarith
end SafeLearning.CompleteModulesLandscapeAffineFeasibility
