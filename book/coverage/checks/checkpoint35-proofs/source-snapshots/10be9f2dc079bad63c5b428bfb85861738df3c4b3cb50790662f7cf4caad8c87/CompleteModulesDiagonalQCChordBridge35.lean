import SafeLearning.CompleteModulesDiagonalQC

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators

namespace SafeLearning.CompleteModulesDiagonalQCChordBridge35

open CompleteModulesLipSDP CompleteModulesDiagonalQC

/-- The formula sheet's quotient definition, restricted to unequal inputs. -/
def quotientSlopeRestricted (activation : ℝ → ℝ) (alpha beta : ℝ) : Prop :=
  ∀ first second : ℝ, first ≠ second →
    alpha ≤ (activation first - activation second) / (first - second) ∧
      (activation first - activation second) / (first - second) ≤ beta

/-- Equal inputs cause no division; their zero chord admits an endpoint slope. -/
theorem quotient_definition_iff_all_chords
    (activation : ℝ → ℝ) (alpha beta : ℝ) (hab : alpha ≤ beta) :
    quotientSlopeRestricted activation alpha beta ↔
      slopeRestricted activation alpha beta := by
  constructor
  · intro h first second
    by_cases he : first = second
    · subst second
      exact ⟨alpha, le_rfl, hab, by simp⟩
    · obtain ⟨hl, hu⟩ := h first second he
      exact ⟨(activation first - activation second) / (first - second), hl, hu,
        (div_mul_cancel₀ _ (sub_ne_zero.mpr he)).symm⟩
  · intro h first second he
    obtain ⟨slope, hl, hu, hchord⟩ := h first second
    have hquotient : (activation first - activation second) / (first - second) = slope := by
      rw [hchord]
      exact mul_div_cancel_right₀ slope (sub_ne_zero.mpr he)
    simpa only [hquotient] using And.intro hl hu

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The actual shared elementwise activation satisfies the printed block QC. -/
theorem quotient_definition_implies_actual_block_qc
    (activation : ℝ → ℝ) (alpha beta : ℝ) (hab : alpha ≤ beta)
    (hactivation : quotientSlopeRestricted activation alpha beta)
    (multiplier : K → ℝ) (hmultiplier : ∀ k, 0 ≤ multiplier k)
    (first second : K → ℝ) :
    0 ≤ quadratic (diagonalQCMatrix alpha beta multiplier)
      (Sum.elim (first - second)
        (fun k => activation (first k) - activation (second k))) := by
  rw [diagonal_qc_is_actual_block_quadratic]
  exact diagonal_qc_from_actual_activations (fun _ => activation) alpha beta
    (fun _ => (quotient_definition_iff_all_chords activation alpha beta hab).mp hactivation)
    multiplier hmultiplier first second

/-- Conversely, all diagonal multipliers recover every unequal-input quotient. -/
theorem all_actual_diagonal_qcs_imply_quotient_definition
    (activation : ℝ → ℝ) (alpha beta : ℝ) (hab : alpha ≤ beta)
    (hqc : ∀ first second : ℝ, ∀ multiplier : Fin 1 → ℝ,
      (∀ k, 0 ≤ multiplier k) →
      0 ≤ diagonalQC alpha beta multiplier (fun _ => first - second)
        (fun _ => activation first - activation second)) :
    quotientSlopeRestricted activation alpha beta := by
  apply (quotient_definition_iff_all_chords activation alpha beta hab).mpr
  intro first second
  have hscalar := (all_diagonal_qcs_iff_coordinate_qcs alpha beta
    (fun _ : Fin 1 => first - second)
    (fun _ : Fin 1 => activation first - activation second)).mp (hqc first second) 0
  exact (scalar_qc_iff_admissible_chord alpha beta (first - second)
    (activation first - activation second) hab).mp hscalar

end SafeLearning.CompleteModulesDiagonalQCChordBridge35
