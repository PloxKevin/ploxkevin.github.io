import SafeLearning.CompleteFiniteTrajectoryReturns

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace SafeLearning.CompleteFinitePathOccupancyReindex

open SafeLearning.CompleteFiniteTrajectoryReturns

variable {F Ω : Type*} [Fintype F] [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → F)

/-- The one-based convention uses the same coordinate process shifted by one. -/
def oneBasedAtomMass (t : ℕ) (z : F) : ℝ := μ.real {ω | Z (t - 1) ω = z}

/-- A sum over t≥1 is represented over naturals with its t=0 summand zero. -/
def oneBasedOccupancy (γ : ℝ) (z : F) : ℝ :=
  (1 - γ) * ∑' t : ℕ, if 0 < t then γ ^ (t - 1) * oneBasedAtomMass μ Z t z else 0

theorem actual_one_based_successor_is_the_original_coordinate (n : ℕ) (z : F) :
    oneBasedAtomMass μ Z (n + 1) z = atomMass μ Z n z := by
  simp only [oneBasedAtomMass, Nat.add_sub_cancel, atomMass]

theorem actual_one_based_discounted_series_summable (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (z : F) :
    Summable (fun t : ℕ => if 0 < t then γ ^ (t - 1) * oneBasedAtomMass μ Z t z else 0) := by
  apply (summable_nat_add_iff (f := fun t : ℕ =>
    if 0 < t then γ ^ (t - 1) * oneBasedAtomMass μ Z t z else 0) 1).mp
  simpa only [Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel,
    actual_one_based_successor_is_the_original_coordinate] using
    actual_atom_discounted_series_summable μ Z γ hγ0 hγ1 z

theorem actual_one_based_occupancy_equals_zero_based_occupancy (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (z : F) :
    oneBasedOccupancy μ Z γ z = pathOccupancy μ Z γ z := by
  have htail : Summable (fun t : ℕ =>
      if 0 < t + 1 then γ ^ (t + 1 - 1) * oneBasedAtomMass μ Z (t + 1) z else 0) := by
    simpa only [Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel,
      actual_one_based_successor_is_the_original_coordinate] using
      actual_atom_discounted_series_summable μ Z γ hγ0 hγ1 z
  have hsplit := tsum_eq_zero_add'
    (f := fun t : ℕ => if 0 < t then γ ^ (t - 1) * oneBasedAtomMass μ Z t z else 0) htail
  simpa only [oneBasedOccupancy, pathOccupancy, Nat.lt_irrefl, ite_false, zero_add,
    Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel,
    actual_one_based_successor_is_the_original_coordinate] using
    congrArg (fun v : ℝ => (1 - γ) * v) hsplit

end SafeLearning.CompleteFinitePathOccupancyReindex
