import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsSetOperations
open Set

section Operations
variable {X Y I Ω : Type*}

theorem actual_union_intersection_difference_complement_and_product_membership
    (A B : Set X) (C : Set Y) (x : X) (y : Y) :
    (x∈A∪B↔x∈A∨x∈B) ∧ (x∈A∩B↔x∈A∧x∈B) ∧
      (x∈A\B↔x∈A∧x∉B) ∧ (x∈Aᶜ↔x∉A) ∧
      ((x,y)∈A×ˢC↔x∈A∧y∈C) := by exact ⟨Iff.rfl,Iff.rfl,Iff.rfl,Iff.rfl,Iff.rfl⟩

theorem actual_relative_complement_keeps_the_ambient_set (ambient A : Set X) (x : X) :
    x∈ambient\A↔x∈ambient∧x∉A := Iff.rfl

theorem actual_powerset_is_the_set_of_all_subsets (ambient A : Set X) :
    A∈𝒫 ambient↔A⊆ambient := Iff.rfl

theorem actual_indexed_de_morgan_laws (family : I→Set X) :
    (⋃i,family i)ᶜ=⋂i,(family i)ᶜ ∧
      (⋂i,family i)ᶜ=⋃i,(family i)ᶜ := by
  classical
  constructor <;> ext x <;> simp

theorem actual_relative_indexed_de_morgan_laws (ambient : Set X)
    (index : Set I) (family : I→Set X) :
    ambient\(⋃i∈index,family i)=ambient∩(⋂i∈index,(family i)ᶜ) ∧
      ambient\(⋂i∈index,family i)=ambient∩(⋃i∈index,(family i)ᶜ) := by
  classical
  constructor <;> ext x <;> simp

theorem actual_simultaneous_constraints_are_an_intersection
    (constraints : I→X→ℝ) :
    {x|∀i,0≤constraints i x}=⋂i,{x|0≤constraints i x} := by ext x;simp

theorem actual_finite_time_failure_is_a_union (trajectory : Ω→ℕ→X)
    (safe : Set X) (horizon : ℕ) :
    {ω|∃t≤horizon,trajectory ω t∉safe}=
      ⋃t∈Set.Iic horizon,{ω|trajectory ω t∉safe} := by ext ω;simp

end Operations

def sourceDomain : Finset ℕ := {1,2,3,4,5,6}
def sourceS : Finset ℕ := {2,3}
def sourceT : Finset ℕ := {3,4,5}

theorem actual_source_finite_set_operations_and_cardinalities :
    sourceS∪sourceT={2,3,4,5} ∧ sourceS∩sourceT={3} ∧
      sourceDomain\sourceS={1,4,5,6} ∧
      (sourceDomain\sourceS).card=4 ∧
      (sourceS×ˢ({1,2}:Finset ℕ)).card=4 := by
  constructor
  · ext n; simp [sourceS,sourceT]; tauto
  constructor
  · ext n; simp [sourceS,sourceT]
  constructor
  · ext n; simp [sourceDomain,sourceS]; omega
  constructor <;> norm_num [sourceS,sourceT,sourceDomain,Finset.product,Finset.card]

theorem actual_source_set_level_operations_and_cardinalities :
    ((sourceS: Set ℕ)∪(sourceT:Set ℕ))=({2,3,4,5}:Set ℕ) ∧
      ((sourceS:Set ℕ)∩(sourceT:Set ℕ))=({3}:Set ℕ) ∧
      (((sourceDomain:Set ℕ)\(sourceS:Set ℕ)).ncard)=4 ∧
      (((sourceS:Set ℕ)×ˢ({1,2}:Set ℕ)).ncard)=4 := by
  have h := actual_source_finite_set_operations_and_cardinalities
  constructor
  · rw [←Finset.coe_union,h.1];simp
  constructor
  · rw [←Finset.coe_inter,h.2.1];simp
  constructor
  · rw [←Finset.coe_sdiff,Set.ncard_coe_finset]
    exact h.2.2.2.1
  · rw [show ({1,2}:Set ℕ)=((({1,2}:Finset ℕ):Set ℕ)) by simp]
    rw [←Finset.coe_product,Set.ncard_coe_finset]
    exact h.2.2.2.2

theorem actual_negative_powers_and_source_three_term_sum :
    (2:ℝ)^(-3:ℤ)=1/(2:ℝ)^3 ∧ (2:ℝ)^(-3:ℤ)=1/8 ∧
      (∑t∈Finset.range 3,(1/2:ℝ)^t)=7/4 := by norm_num [Finset.sum_range_succ]

theorem actual_nonzero_real_integer_power_rules (a : ℝ) (ha : a≠0) (m n : ℤ) :
    a^(m+n)=a^m*a^n ∧ a^(0:ℤ)=1 := ⟨zpow_add₀ ha m n,zpow_zero a⟩

end SafeLearning.CompleteFoundationsSetOperations
