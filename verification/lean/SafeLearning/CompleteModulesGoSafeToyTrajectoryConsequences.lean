import SafeLearning.CompleteModulesGoSafeToyAffine

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology
namespace SafeLearning.CompleteModulesGoSafeToyTrajectoryConsequences
open SafeLearning.CompleteModulesGoSafeToyAffine

theorem actual_arbitrary_initial_state_has_the_literal_monotonic_approach
    (q equilibrium initial : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (initial ≤ equilibrium → Monotone (actualTrajectory q equilibrium initial)) ∧
      (equilibrium ≤ initial → Antitone (actualTrajectory q equilibrium initial)) := by
  constructor
  · intro hstart
    apply monotone_nat_of_le_succ
    intro n
    have hp := pow_nonneg hq n
    have hd := mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hq1)) (sub_nonneg.mpr hstart)
    unfold actualTrajectory
    rw [pow_succ]
    nlinarith
  · intro hstart
    apply antitone_nat_of_succ_le
    intro n
    have hp := pow_nonneg hq n
    have hd := mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hq1)) (sub_nonneg.mpr hstart)
    unfold actualTrajectory
    rw [pow_succ]
    nlinarith

theorem actual_non_equilibrium_initial_state_never_reaches_equilibrium
    (q equilibrium initial : ℝ) (hq : 0 < q) (hi : initial ≠ equilibrium) :
    ∀ n : ℕ, actualTrajectory q equilibrium initial n ≠ equilibrium := by
  intro n h
  have hp : q^n ≠ 0 := ne_of_gt (pow_pos hq n)
  have hh : q^n*(initial-equilibrium)=0 := by
    unfold actualTrajectory at h
    linarith
  exact hi (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hp))

theorem actual_supremum_of_all_trajectory_absolute_values_is_the_literal_maximum
    (q equilibrium initial : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (he : 0 ≤ equilibrium) :
    sSup (range (fun n : ℕ => |actualTrajectory q equilibrium initial n|))=
      max |initial| equilibrium := by
  let values := range (fun n : ℕ => |actualTrajectory q equilibrium initial n|)
  have hnon : values.Nonempty := range_nonempty _
  have hb : BddAbove values := ⟨max |initial| equilibrium,by
    rintro value ⟨n,rfl⟩
    exact actual_trajectory_absolute_values_are_bounded_by_the_start_equilibrium_maximum q equilibrium initial hq hq1.le he n⟩
  change sSup values=max |initial| equilibrium
  apply le_antisymm
  · apply csSup_le hnon
    rintro value ⟨n,rfl⟩
    exact actual_trajectory_absolute_values_are_bounded_by_the_start_equilibrium_maximum q equilibrium initial hq hq1.le he n
  · apply max_le
    · have h0 := le_csSup hb (show |actualTrajectory q equilibrium initial 0| ∈ values from ⟨0,rfl⟩)
      simpa [actualTrajectory] using h0
    · have ht := (actual_trajectory_converges_to_its_equilibrium q equilibrium initial hq hq1).abs
      have heq : |equilibrium|=equilibrium := abs_of_nonneg he
      rw [heq] at ht
      exact le_of_tendsto' ht (fun n => le_csSup hb ⟨n,rfl⟩)

end SafeLearning.CompleteModulesGoSafeToyTrajectoryConsequences
