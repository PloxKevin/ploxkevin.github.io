import SafeLearning.CompleteModulesRKHSStructure
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeUnsafeSeeds
open CompleteModulesRKHSStructure

def seed : Set Bool := univ
def truth : Bool → ℝ := fun a => if a then -1 else 1
def priorSD : Bool → ℝ := fun a => if a then 1 else 2
def priorKernel : Matrix Bool Bool ℝ := Matrix.diagonal (fun a => priorSD a ^ 2)
def priorBand (a : Bool) : Set ℝ := Icc (-priorSD a) (priorSD a)
def initializedBand (a : Bool) : Set ℝ := Ici (0:ℝ) ∩ priorBand a
def lower (_ : Bool) : ℝ := 0
def upper (a : Bool) : ℝ := priorSD a
def width (a : Bool) : ℝ := upper a-lower a
def maximizerSet : Set Bool := {a | ∀b : Bool, lower b ≤ upper a}
def firstQuery : Bool := false

theorem actual_mixed_seed_contains_an_unsafe_point_but_the_first_query_is_safe :
    true ∈ seed ∧ truth true < 0 ∧ firstQuery ∈ seed ∧ 0 ≤ truth firstQuery := by
  norm_num [seed,truth,firstQuery]

theorem actual_mixed_seed_has_a_valid_positive_definite_prior_kernel_and_truth_in_both_raw_bands :
    priorKernel.PosDef ∧ ∀a : Bool, truth a ∈ priorBand a := by
  constructor
  · apply Matrix.posDef_diagonal_iff.mpr
    intro a
    cases a <;> norm_num [priorSD]
  · intro a
    cases a <;> norm_num [truth,priorBand,priorSD]

theorem actual_source_seed_initialization_has_exact_endpoints_and_admits_both_candidates :
    (∀a : Bool, initializedBand a=Icc (lower a) (upper a)) ∧
      maximizerSet=univ ∧
      IsLeast (initializedBand false) 0 ∧ IsGreatest (initializedBand false) 2 ∧
      IsLeast (initializedBand true) 0 ∧ IsGreatest (initializedBand true) 1 := by
  have he : ∀a : Bool, initializedBand a=Icc (lower a) (upper a) := by
    intro a
    cases a <;> ext y <;> simp only [initializedBand,priorBand,priorSD,lower,upper,
      Bool.false_eq_true,ite_false,ite_true,mem_inter_iff,mem_Ici,mem_Icc] <;> constructor <;>
      intro h <;> constructor <;> linarith
  refine ⟨he,?_,?_,?_,?_,?_⟩
  · ext a
    cases a <;> simp [maximizerSet,lower,upper,priorSD]
  · rw [he false]
    norm_num [lower,upper,priorSD]
    exact ⟨by norm_num,fun y hy => hy.1⟩
  · rw [he false]
    norm_num [lower,upper,priorSD]
    exact ⟨by norm_num,fun y hy => hy.2⟩
  · rw [he true]
    norm_num [lower,upper,priorSD]
    exact ⟨by norm_num,fun y hy => hy.1⟩
  · rw [he true]
    norm_num [lower,upper,priorSD]
    exact ⟨by norm_num,fun y hy => hy.2⟩

theorem actual_unique_maximum_width_first_query_can_avoid_the_unsafe_seed_point :
    firstQuery ∈ maximizerSet ∧ (∀a : Bool, width a ≤ width firstQuery) ∧
      (∀a : Bool, width a=width firstQuery → a=firstQuery) ∧
      0 ≤ truth firstQuery := by
  refine ⟨by norm_num [firstQuery,maximizerSet,lower,upper,priorSD],?_,?_,by norm_num [firstQuery,truth]⟩
  · intro a; cases a <;> norm_num [width,upper,lower,priorSD,firstQuery]
  · intro a; cases a <;> norm_num [width,upper,lower,priorSD,firstQuery]

theorem actual_selected_unsafe_seed_is_unsafe_if_and_only_if_the_first_selected_value_is_unsafe
    {X : Type*} (f : X → ℝ) (threshold : ℝ) (queries : ℕ → X) :
    f (queries 1) < threshold ↔ ¬threshold ≤ f (queries 1) := by exact not_le.symm

def positiveDesign (a : Bool) : ℝ := if a then 2 else 1

theorem actual_underestimated_RKHS_norm_bound_does_not_force_an_unsafe_query :
    (1/4:ℝ) < ‖(1:ℝ)‖^2 ∧
      (∀a : Bool, linearFunction 1 (positiveDesign a) ≥ (0:ℝ)) ∧
      ∀queries : ℕ → Bool, ∀t : ℕ, 0 ≤ linearFunction 1 (positiveDesign (queries t)) := by
  refine ⟨by norm_num,?_,?_⟩
  · intro a
    cases a <;> norm_num [linear_function_evaluation,positiveDesign]
  · intro queries t
    cases queries t <;> norm_num [linear_function_evaluation,positiveDesign]

end SafeLearning.CompleteModulesLandscapeUnsafeSeeds
