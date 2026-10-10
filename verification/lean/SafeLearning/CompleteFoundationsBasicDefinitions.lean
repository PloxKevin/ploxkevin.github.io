import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsBasicDefinitions
open Set
open scoped NNReal

section Sets
variable {X I : Type*}

theorem actual_set_membership_and_subset (A B : Set X) (x : X) :
    (x∉A↔¬x∈A) ∧ (A⊆B↔∀ y,y∈A→y∈B) ∧
      (A=B↔A⊆B∧B⊆A) ∧ (x∉(∅:Set X)) := by
  exact ⟨Iff.rfl,Iff.rfl,Set.Subset.antisymm_iff,by simp⟩

theorem actual_set_builder_filter (ambient : Set X) (P : X→Prop) (x : X) :
    x∈{y∈ambient|P y}↔x∈ambient∧P x := Iff.rfl

theorem actual_proper_subset_definition (A B : Set X) :
    A⊂B↔A⊆B∧¬B⊆A := Iff.rfl

theorem actual_indexed_union_and_intersection (index : Set I) (family : I→Set X) (x : X) :
    (x∈⋃ i∈index,family i↔∃ i∈index,x∈family i) ∧
      (x∈⋂ i∈index,family i↔∀ i∈index,x∈family i) := by simp

end Sets

section Logic

theorem actual_connectives_and_implication (P Q : Prop) :
    ((P↔Q)↔(P→Q)∧(Q→P)) ∧
      (¬(P→Q)↔P∧¬Q) ∧ ((P→Q)↔(¬Q→¬P)) ∧
      ((P→Q)↔¬P∨Q) := by tauto

theorem actual_converse_is_not_equivalent_in_general :
    ∃ P Q : Prop,(P→Q)∧¬(Q→P) := ⟨False,True,False.elim,fun h=>h trivial⟩

theorem actual_bounded_quantifier_negations {X : Type*} (ambient : Set X) (P : X→Prop) :
    (¬(∀ x∈ambient,P x)↔∃ x∈ambient,¬P x) ∧
      (¬(∃ x∈ambient,P x)↔∀ x∈ambient,¬P x) := by
  classical
  constructor <;> simp

theorem actual_empty_quantification {X : Type*} (P : X→Prop) :
    (∀ x∈(∅:Set X),P x) ∧ ¬(∃ x∈(∅:Set X),P x) := by simp

theorem actual_control_invariance_negation {X U : Type*} (states : Set X)
    (inputs : Set U) (dynamics : X→U→X) :
    ¬(∀ x∈states,∃ u∈inputs,dynamics x u∈states)↔
      ∃ x∈states,∀ u∈inputs,dynamics x u∉states := by
  classical
  simp

end Logic

section Functions
variable {X Y Z U : Type*}

theorem actual_function_has_exactly_one_value (f : X→Y) (x : X) :
    ∃! y,y=f x := ⟨f x,rfl,fun _ h=>h⟩

theorem actual_image_and_preimage (f : X→Y) (A : Set X) (B : Set Y) (y : Y) (x : X) :
    (y∈f '' A↔∃ a∈A,f a=y) ∧ (x∈f ⁻¹' B↔f x∈B) := ⟨Iff.rfl,Iff.rfl⟩

theorem actual_composition_restriction_and_product (f : X→Y) (g : Y→Z)
    (A : Set X) (x : A) (dynamics : X×U→Y) (u : U) :
    (g∘f) x.val=g (f x.val) ∧ A.domRestrict f x=f x.val ∧
      dynamics (x.val,u)=(Function.uncurry (Function.curry dynamics)) (x.val,u) := by
  exact ⟨rfl,rfl,rfl⟩

def graphOf (F : X→Set Y) : Set (X×Y) := {p|p.2∈F p.1}

theorem actual_set_valued_graph (F : X→Set Y) (x : X) (y : Y) :
    (x,y)∈graphOf F↔y∈F x := Iff.rfl

theorem actual_singleton_values_are_exactly_functions (F : X→Set Y) :
    (∀ x,∃! y,y∈F x)↔∃ f : X→Y,∀ x,F x={f x} := by
  classical
  constructor
  · intro h
    choose f hf using fun x=>(h x).exists
    refine ⟨f,fun x=>?_⟩
    ext y
    simp only [Set.mem_singleton_iff]
    exact ⟨fun hy=>(h x).unique hy (hf x),fun hy=>hy ▸ hf x⟩
  · rintro ⟨f,hf⟩ x
    rw [hf x]
    exact ⟨f x,rfl,fun _ h=>h⟩

def predecessor (dynamics : X→U→X) (inputs : Set U) (target : Set X) : Set X :=
  {x|∃ u∈inputs,dynamics x u∈target}

theorem actual_predecessor_membership (dynamics : X→U→X) (inputs : Set U)
    (target : Set X) (x : X) :
    x∈predecessor dynamics inputs target↔∃ u∈inputs,dynamics x u∈target := Iff.rfl

end Functions

def monotoneRelation (R : Set (ℝ×ℝ)) : Prop :=
  ∀ p∈R,∀ q∈R,(p.1-q.1)*(p.2-q.2)≥0

theorem actual_real_monotone_relation_definition (R : Set (ℝ×ℝ)) :
    monotoneRelation R↔∀ a b a' b',(a,b)∈R→(a',b')∈R→(a-a')*(b-b')≥0 := by
  constructor
  · intro h a b a' b' hab hab'
    exact h (a,b) hab (a',b') hab'
  · intro h p hp q hq
    exact h p.1 p.2 q.1 q.2 hp hq

section FixedPoints
variable {E : Type*} [NormedAddCommGroup E]

omit [NormedAddCommGroup E] in
theorem actual_fixed_point_and_iteration (g : E→E) (x : E) (n : ℕ) :
    (Function.IsFixedPt g x↔g x=x) ∧ g^[n+1] x=g (g^[n] x) :=
  ⟨Iff.rfl,Function.iterate_succ_apply' _ _ _⟩

theorem actual_norm_contraction_definition (g : E→E) (L : ℝ≥0) :
    ContractingWith L g↔(L<1∧∀ x y,‖g x-g y‖≤(L:ℝ)*‖x-y‖) := by
  simp only [ContractingWith,lipschitzWith_iff_dist_le_mul,dist_eq_norm]

end FixedPoints
end SafeLearning.CompleteFoundationsBasicDefinitions
