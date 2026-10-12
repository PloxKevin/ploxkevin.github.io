import SafeLearning.CompleteAppliedFiniteEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedEntropyJensen
open Set MeasureTheory
open scoped BigOperators Classical
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedFiniteEntropy

def positiveAtoms {n : ℕ} (p : PMF (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (p i).toReal ≠ 0)

theorem actual_positive_atoms_total_mass {n : ℕ} (p : PMF (Fin n)) :
    (∑ i ∈ positiveAtoms p, (p i).toReal) = 1 := by
  rw [positiveAtoms, Finset.sum_filter]
  have he : (∑ i : Fin n, if (p i).toReal ≠ 0 then (p i).toReal else 0) =
      ∑ i : Fin n, (p i).toReal := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (p i).toReal = 0 <;> simp [hi]
  rw [he, actual_finite_weights_sum]

theorem actual_entropy_inverse_log_sum {n : ℕ} (p : PMF (Fin n)) :
    shannonEntropy p = ∑ i ∈ positiveAtoms p,
      (p i).toReal * Real.log (1 / (p i).toReal) := by
  rw [actual_entropy_sum, positiveAtoms, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (p i).toReal = 0
  · simp [hi]
  · simp [hi, one_div, Real.log_inv]

theorem actual_reciprocal_mean_is_support_card {n : ℕ} (p : PMF (Fin n)) :
    (∑ i ∈ positiveAtoms p, (p i).toReal * (1 / (p i).toReal)) =
      ((positiveAtoms p).card : ℝ) := by
  calc
    _ = ∑ _i ∈ positiveAtoms p, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hp : (p i).toReal ≠ 0 := (Finset.mem_filter.mp hi).2
      simp [hp]
    _ = _ := by simp

theorem actual_jensen_entropy_support_bound {n : ℕ} (p : PMF (Fin n)) :
    shannonEntropy p ≤ Real.log ((positiveAtoms p).card : ℝ) := by
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := positiveAtoms p) (w := fun i => (p i).toReal)
    (p := fun i => 1 / (p i).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) (actual_positive_atoms_total_mass p)
    (fun i hi => one_div_pos.mpr (lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Finset.mem_filter.mp hi).2)))
  simp only [smul_eq_mul] at hj
  rw [actual_reciprocal_mean_is_support_card, ← actual_entropy_inverse_log_sum] at hj
  exact hj

theorem actual_jensen_entropy_upper_bound {n : ℕ} (p : PMF (Fin n)) :
    shannonEntropy p ≤ Real.log (n : ℝ) := by
  have hs : (positiveAtoms p).Nonempty := by
    by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    have hm := actual_positive_atoms_total_mass p
    rw [hz] at hm
    simp at hm
  have hc : (positiveAtoms p).card ≤ n := by
    have h := Finset.card_le_card (Finset.filter_subset
      (fun i : Fin n => (p i).toReal ≠ 0) Finset.univ)
    simpa [positiveAtoms] using h
  exact (actual_jensen_entropy_support_bound p).trans
    (Real.log_le_log (Nat.cast_pos.mpr (Finset.card_pos.mpr hs)) (Nat.cast_le.mpr hc))

end SafeLearning.CompleteAppliedEntropyJensen
