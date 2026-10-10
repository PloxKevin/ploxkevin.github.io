import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal
namespace SafeLearning.CompleteFoundationsQuantifierSafety

def sharedCertificate {E I : Type*} [PseudoMetricSpace E]
    (evaluated : Set E) (constraints : I → E → ℝ) (bound : ℝ) : Set E :=
  {a | ∃ witness ∈ evaluated, ∀ i,
    0 ≤ constraints i witness - bound * dist a witness}

def perConstraintCertificate {E I : Type*} [PseudoMetricSpace E]
    (evaluated : Set E) (constraints : I → E → ℝ) (bound : ℝ) : Set E :=
  {a | ∀ i, ∃ witness ∈ evaluated,
    0 ≤ constraints i witness - bound * dist a witness}

theorem actual_shared_witness_certificate_is_always_a_subset_of_per_constraint_certificate
    {E I : Type*} [PseudoMetricSpace E] (evaluated : Set E)
    (constraints : I → E → ℝ) (bound : ℝ) :
    sharedCertificate evaluated constraints bound ⊆
      perConstraintCertificate evaluated constraints bound := by
  rintro a ⟨witness, hw, h⟩ i
  exact ⟨witness, hw, h i⟩

theorem actual_normed_domain_certificate_formulas
    {E I : Type*} [NormedAddCommGroup E] (evaluated : Set E)
    (constraints : I → E → ℝ) (bound : ℝ) (a : E) :
    (a ∈ sharedCertificate evaluated constraints bound ↔
      ∃ witness ∈ evaluated, ∀ i,
        0 ≤ constraints i witness - bound * ‖a - witness‖) ∧
    (a ∈ perConstraintCertificate evaluated constraints bound ↔
      ∀ i, ∃ witness ∈ evaluated,
        0 ≤ constraints i witness - bound * ‖a - witness‖) := by
  simp only [sharedCertificate, perConstraintCertificate, mem_ofPred_eq, dist_eq_norm]
  trivial

theorem actual_per_constraint_witnesses_certify_true_constraint_values
    {E I : Type*} [PseudoMetricSpace E] (evaluated : Set E)
    (constraints : I → E → ℝ) (bound : ℝ≥0)
    (hLip : ∀ i, LipschitzWith bound (constraints i)) (a : E)
    (ha : a ∈ perConstraintCertificate evaluated constraints (bound : ℝ)) :
    ∀ i, 0 ≤ constraints i a := by
  intro i
  obtain ⟨witness, _, hw⟩ := ha i
  have hb := (hLip i).dist_le_mul a witness
  rw [Real.dist_eq] at hb
  have hreverse := (neg_le_abs (constraints i a - constraints i witness)).trans hb
  linarith

theorem actual_shared_to_per_constraint_inclusion_survives_accuracy_and_old_set_union
    {E I : Type*} [PseudoMetricSpace E] (evaluated : Set E)
    (constraints : I → E → ℝ) (bound accuracy : ℝ) :
    evaluated ∪ sharedCertificate evaluated (fun i a => constraints i a - accuracy) bound ⊆
      evaluated ∪ perConstraintCertificate evaluated
        (fun i a => constraints i a - accuracy) bound := by
  exact union_subset_union_right evaluated
    (actual_shared_witness_certificate_is_always_a_subset_of_per_constraint_certificate
      evaluated (fun i a => constraints i a - accuracy) bound)

def sourceEvaluated : Set ℝ := {0, 2}

def sourceConstraints (i : Fin 2) (a : ℝ) : ℝ :=
  if i = 0 then 2 - 3 / 4 * a else 1 / 2 + 3 / 4 * a

theorem actual_source_constraint_values_and_distances :
    sourceConstraints 0 0 = 2 ∧ sourceConstraints 0 2 = 1 / 2 ∧
      sourceConstraints 1 0 = 1 / 2 ∧ sourceConstraints 1 2 = 2 ∧
      dist (1 : ℝ) 0 = 1 ∧ dist (1 : ℝ) 2 = 1 := by
  norm_num [sourceConstraints, Real.dist_eq]

theorem actual_source_constraints_have_the_genuine_global_lipschitz_bound :
    ∀ i, LipschitzWith 1 (sourceConstraints i) := by
  intro i
  apply LipschitzWith.of_dist_le_mul
  intro a b
  fin_cases i
  all_goals
    simp [sourceConstraints, Real.dist_eq]
    have he : |(3 / 4 : ℝ) * (a - b)| = (3 / 4 : ℝ) * |a - b| := by
      rw [abs_mul]
      norm_num
    have hn := abs_nonneg (a - b)
    first
    | rw [show 2 - 3 / 4 * a + 3 / 4 * b - 2 =
          -((3 / 4 : ℝ) * (a - b)) by ring, abs_neg, he]
      linarith
    | rw [show 3 / 4 * a - 3 / 4 * b =
          (3 / 4 : ℝ) * (a - b) by ring, he]
      linarith

theorem actual_source_separate_witnesses_succeed_and_every_shared_witness_fails :
    (1 : ℝ) ∈ perConstraintCertificate sourceEvaluated sourceConstraints 1 ∧
      (1 : ℝ) ∉ sharedCertificate sourceEvaluated sourceConstraints 1 := by
  constructor
  · intro i
    fin_cases i
    · refine ⟨0, by simp [sourceEvaluated], ?_⟩
      norm_num [sourceConstraints, Real.dist_eq]
    · refine ⟨2, by simp [sourceEvaluated], ?_⟩
      norm_num [sourceConstraints, Real.dist_eq]
  · rintro ⟨witness, hw, h⟩
    rcases (by simpa [sourceEvaluated] using hw : witness = 0 ∨ witness = 2) with hw | hw
    · subst witness
      have hf := h 1
      norm_num [sourceConstraints, Real.dist_eq] at hf
    · subst witness
      have hf := h 0
      norm_num [sourceConstraints, Real.dist_eq] at hf

theorem actual_source_candidate_is_truly_safe_for_both_constraints :
    ∀ i, 0 ≤ sourceConstraints i 1 := by
  exact actual_per_constraint_witnesses_certify_true_constraint_values sourceEvaluated
    sourceConstraints 1 actual_source_constraints_have_the_genuine_global_lipschitz_bound 1
    actual_source_separate_witnesses_succeed_and_every_shared_witness_fails.1

def viable {X U : Type*} (admissible : Set U) (failure : Set X)
    (flow : X → U → ℝ → X) : Set X :=
  {x | ∃ u ∈ admissible, ∀ t, 0 ≤ t → flow x u t ∉ failure}

theorem actual_viability_membership_and_ambient_complement_quantifier_order
    {X U : Type*} (ambient : Set X) (admissible : Set U) (failure : Set X)
    (flow : X → U → ℝ → X) (x : X) :
    (x ∈ viable admissible failure flow ↔
      ∃ u ∈ admissible, ∀ t, 0 ≤ t → flow x u t ∉ failure) ∧
    (x ∈ ambient \ viable admissible failure flow ↔
      x ∈ ambient ∧ ∀ u ∈ admissible, ∃ t, 0 ≤ t ∧ flow x u t ∈ failure) := by
  classical
  constructor
  · rfl
  · simp only [mem_sdiff, viable, mem_ofPred_eq]
    push Not
    rfl

theorem actual_unviability_is_the_exact_ambient_complement_set
    {X U : Type*} (ambient : Set X) (admissible : Set U) (failure : Set X)
    (flow : X → U → ℝ → X) :
    ambient \ viable admissible failure flow =
      {x ∈ ambient | ∀ u ∈ admissible, ∃ t, 0 ≤ t ∧ flow x u t ∈ failure} := by
  ext x
  exact (actual_viability_membership_and_ambient_complement_quantifier_order
    ambient admissible failure flow x).2

end SafeLearning.CompleteFoundationsQuantifierSafety
