import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteModulesRealHarmonicFrequencyChoices

def selectedFrequency (n m : ℕ) (i : Fin m) : ZMod n := ((i.val+1:ℕ) : ZMod n)

theorem actual_selected_positive_frequencies_are_nonzero
    (n m : ℕ) (hRange : 2*m < n) (i : Fin m) : selectedFrequency n m i≠0 := by
  intro hz
  have hlt : i.val+1 < n := by omega
  have hv := congrArg ZMod.val hz
  simp only [selectedFrequency,ZMod.val_natCast_of_lt hlt,ZMod.val_zero] at hv
  omega

theorem actual_selected_positive_frequencies_are_distinct
    (n m : ℕ) (hRange : 2*m < n) : Function.Injective (selectedFrequency n m) := by
  intro i j hij
  have hi : i.val+1 < n := by omega
  have hj : j.val+1 < n := by omega
  have hv := congrArg ZMod.val hij
  simp only [selectedFrequency,ZMod.val_natCast_of_lt hi,ZMod.val_natCast_of_lt hj] at hv
  apply Fin.ext
  omega

theorem actual_no_selected_frequency_pair_sums_to_zero
    (n m : ℕ) (hRange : 2*m < n) (i j : Fin m) :
    selectedFrequency n m i+selectedFrequency n m j≠0 := by
  have hlt : (i.val+1)+(j.val+1) < n := by omega
  intro hz
  have hv := congrArg ZMod.val hz
  simp only [selectedFrequency,←Nat.cast_add,ZMod.val_natCast_of_lt hlt,ZMod.val_zero] at hv
  omega

theorem actual_even_strict_dimension_and_odd_dimension_supply_enough_frequency_pairs
    (d n : ℕ) (hd : 0 < d) (hOrder : d ≤ n) :
    (Even d ∧ d<n → 2*(d/2) < n) ∧
      (Odd d → 2*((d-1)/2) < n) := by
  constructor
  · rintro ⟨he,hlt⟩
    obtain ⟨k,hk⟩ := he
    omega
  · intro ho
    obtain ⟨k,hk⟩ := ho
    omega

end SafeLearning.CompleteModulesRealHarmonicFrequencyChoices
