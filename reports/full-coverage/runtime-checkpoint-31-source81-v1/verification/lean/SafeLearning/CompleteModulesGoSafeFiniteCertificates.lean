import SafeLearning.CompleteModulesGoSafeBackupConsequences
import SafeLearning.CompleteModulesTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace SafeLearning.CompleteModulesGoSafeFiniteCertificates

inductive SourceNode where
  | A | B | C
  deriving DecidableEq
open SourceNode

def sourceEdge : SourceNode→SourceNode→Prop
  | A,A => True
  | A,B => True
  | B,A => True
  | B,C => True
  | C,C => True
  | _,_ => False

def sourceReach (x y : SourceNode) : Prop := Relation.ReflTransGen sourceEdge x y

theorem actual_all_three_safe_nodes_are_reachable_from_the_seed :
    ∀ x : SourceNode,sourceReach A x := by
  intro x;cases x with
  | A => exact .refl
  | B => exact .tail .refl (by trivial)
  | C =>
    have hab : sourceReach A B := .tail .refl (by trivial)
    exact .tail hab (by trivial)

theorem actual_any_path_from_the_trap_remains_at_the_trap
    (x : SourceNode) (h : sourceReach C x) : x=C := by
  induction h with
  | refl => rfl
  | @tail b c path edge ih =>
    rw [ih] at edge
    cases c <;> simp_all [sourceEdge]

theorem actual_reachable_and_returnable_set_is_exactly_the_source_A_B_pair :
    {x | sourceReach A x ∧ sourceReach x A}=({A,B} : Set SourceNode) ∧
      ¬sourceReach C A := by
  have hc : ¬sourceReach C A := by
    intro h
    have impossible := actual_any_path_from_the_trap_remains_at_the_trap A h
    cases impossible
  refine ⟨?_,hc⟩
  ext x;cases x with
  | A => simp [sourceReach,Relation.ReflTransGen.refl]
  | B =>
    have hab : sourceReach A B := .tail .refl (by trivial)
    have hba : sourceReach B A := .tail .refl (by trivial)
    simp [hab,hba]
  | C => simp [hc]

def actualFiniteMinimum {ι : Type*} [Fintype ι] [Nonempty ι] (lower : ι→ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty lower

theorem actual_finite_minimum_transfers_the_one_backup_condition_to_every_constraint
    {X ι : Type*} [PseudoMetricSpace X] [Fintype ι] [Nonempty ι]
    (g : ι→X→ℝ) (L : ℝ≥0) (hg : ∀ i,LipschitzWith L (g i))
    (stored current activation : X) (lower : ι→ℝ) (motion : ℝ)
    (hstored : ∀ i,lower i ≤ g i stored) (hmove : dist activation current ≤ motion)
    (hcertificate : (L:ℝ)*(dist current stored+motion) ≤ actualFiniteMinimum lower) :
    ∀ i,0 ≤ g i activation := by
  intro i
  apply CompleteModulesGoSafeBackupConsequences.actual_lipschitz_backup_certificate_covers_every_possible_activation
    (g i) L (hg i) stored current activation (lower i) motion (hstored i) hmove
  exact hcertificate.trans (Finset.inf'_le lower (Finset.mem_univ i))

def certifiedStateUnion {X κ ι : Type*} [PseudoMetricSpace X] [Fintype ι] [Nonempty ι]
    (backups : Set κ) (center : κ→X) (lower : κ→ι→ℝ) (L motion : ℝ) : Set X :=
  {x | ∃ b∈backups,dist x (center b) ≤ actualFiniteMinimum (lower b)/L-motion}

theorem actual_retained_backups_and_pointwise_increasing_lower_bounds_grow_the_full_state_union
    {X κ ι : Type*} [PseudoMetricSpace X] [Fintype ι] [Nonempty ι]
    (oldBackups newBackups : Set κ) (center : κ→X) (oldLower newLower : κ→ι→ℝ)
    (L motion : ℝ) (hL : 0<L) (hretained : oldBackups⊆newBackups)
    (hmonotone : ∀ b∈oldBackups,∀ i,oldLower b i ≤ newLower b i) :
    certifiedStateUnion oldBackups center oldLower L motion⊆
      certifiedStateUnion newBackups center newLower L motion := by
  rintro x ⟨b,hb,hx⟩
  refine ⟨b,hretained hb,hx.trans ?_⟩
  apply sub_le_sub_right
  apply div_le_div_of_nonneg_right _ hL.le
  apply (Finset.le_inf'_iff _ _).mpr
  intro i hi
  exact (Finset.inf'_le (oldLower b) hi).trans (hmonotone b hb i)

theorem actual_three_time_uniform_function_bands_have_the_source_union_budget
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Fin 3→Set Ω) (hmeas : ∀ i,MeasurableSet (failure i))
    (hbound : ∀ i,μ.real (failure i) ≤ (1/100:ℝ)) :
    μ.real (⋃ i,failure i) ≤ (3/100:ℝ) ∧
      (97/100:ℝ) ≤ μ.real (⋂ i,(failure i)ᶜ) := by
  constructor
  · have h := CompleteModulesTheory.finite_failure_union μ failure (fun _ => (1/100:ℝ)) hbound
    norm_num at h ⊢;exact h
  · have h := CompleteModulesTheory.simultaneous_success μ failure (fun _ => (1/100:ℝ)) hmeas hbound
    norm_num at h ⊢;exact h

theorem actual_equal_third_budgets_keep_the_joint_failure_within_point_zero_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Fin 3→Set Ω)
    (hbound : ∀ i,μ.real (failure i) ≤ (1/300:ℝ)) :
    μ.real (⋃ i,failure i) ≤ (1/100:ℝ) := by
  have h := CompleteModulesTheory.finite_failure_union μ failure (fun _ => (1/300:ℝ)) hbound
  norm_num at h ⊢;exact h

theorem actual_required_radius_sample_interval_and_switching_delay_conditions (interval : ℝ) :
    ((2:ℝ)*((1/10)+5*interval) ≤ 3/10 ↔ interval ≤ 1/100) ∧
      ((2:ℝ)*((1/10)+5*(interval+1/250)) ≤ 3/10 ↔ interval ≤ 3/500) ∧
      (3/10-(2:ℝ)*((1/10)+5*(1/100))=0) ∧
      (3/10-(2:ℝ)*((1/10)+5*((3/500)+(1/250)))=0) := by
  constructor
  · constructor <;> intro h <;> linarith
  constructor
  · constructor <;> intro h <;> linarith
  norm_num

end SafeLearning.CompleteModulesGoSafeFiniteCertificates
