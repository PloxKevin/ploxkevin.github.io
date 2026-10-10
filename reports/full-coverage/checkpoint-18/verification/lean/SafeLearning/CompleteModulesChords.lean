import SafeLearning.CompleteModulesDiagonalQC

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SafeLearning.CompleteModulesChords

open CompleteModulesLipSDP CompleteModulesDiagonalQC

theorem actual_linear_activation_has_declared_slope (alpha beta slope : ℝ)
    (hl : alpha ≤ slope) (hu : slope ≤ beta) :
    slopeRestricted (fun value : ℝ => slope*value) alpha beta := by
  intro first second
  exact ⟨slope,hl,hu,by ring⟩

theorem scalar_qc_iff_realizable_actual_increment (alpha beta input hidden : ℝ)
    (hab : alpha ≤ beta) :
    0 ≤ scalarQC alpha beta input hidden ↔
      ∃ activation : ℝ → ℝ, slopeRestricted activation alpha beta ∧
        ∃ first second : ℝ, first-second=input ∧ activation first-activation second=hidden := by
  constructor
  · intro h
    obtain ⟨slope,hl,hu,he⟩ :=
      (scalar_qc_iff_admissible_chord alpha beta input hidden hab).mp h
    refine ⟨fun value => slope*value,actual_linear_activation_has_declared_slope _ _ _ hl hu,
      input,0,by ring,?_⟩
    rw [he]
    ring
  · rintro ⟨activation,hactivation,first,second,hinput,hhidden⟩
    rw [← hinput,← hhidden]
    exact scalar_slope_quadratic_constraint activation alpha beta hactivation first second

theorem unit_interval_qc_is_scalar_product (input hidden : ℝ) :
    scalarQC 0 1 input hidden=2*hidden*(input-hidden) := by
  unfold scalarQC
  ring

end SafeLearning.CompleteModulesChords
