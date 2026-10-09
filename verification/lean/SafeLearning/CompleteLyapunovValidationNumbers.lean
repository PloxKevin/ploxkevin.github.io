import SafeLearning.CompleteAppliedGridConfidence
import SafeLearning.CompletePolicyDivergence

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteLyapunovValidationNumbers

theorem genuine_log200_log100_log1000_enclosures :
    (5298316 / 1000000 : ℝ) < Real.log 200 ∧ Real.log 200 < 5298318 / 1000000 ∧
    (4605169 / 1000000 : ℝ) < Real.log 100 ∧ Real.log 100 < 4605171 / 1000000 ∧
    (6907754 / 1000000 : ℝ) < Real.log 1000 ∧ Real.log 1000 < 6907756 / 1000000 := by
  obtain ⟨hl, hu⟩ := SafeLearning.CompleteAppliedGridConfidence.log400_enclosure
  obtain ⟨h2l, h2u⟩ := SafeLearning.CompletePolicyDivergence.log_two_enclosure
  have h200 : Real.log (200 : ℝ) = Real.log 400 - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have h100 : Real.log (100 : ℝ) = Real.log 400 - 2 * Real.log 2 := by
    rw [show (100 : ℝ) = 400 / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h1000 : Real.log (1000 : ℝ) = (3 / 2) * Real.log 400 - 3 * Real.log 2 := by
    have h400 : Real.log (400 : ℝ) = 2 * Real.log 20 := by
      rw [show (400 : ℝ) = 20 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h10 : Real.log (10 : ℝ) = Real.log 20 - Real.log 2 := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow, h10, h400]
    ring
  rw [h200, h100, h1000]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem actual_sample_threshold_enclosures :
    (4139305 / 100 : ℝ) < Real.log 200 / (2 * (8 / 1000) ^ 2) ∧
      Real.log 200 / (2 * (8 / 1000) ^ 2) < 4139315 / 100 ∧
    (3597785 / 100 : ℝ) < Real.log 100 / (2 * (8 / 1000) ^ 2) ∧
      Real.log 100 / (2 * (8 / 1000) ^ 2) < 3597795 / 100 ∧
    (5396675 / 100 : ℝ) < Real.log 1000 / (2 * (8 / 1000) ^ 2) ∧
      Real.log 1000 / (2 * (8 / 1000) ^ 2) < 5396685 / 100 := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := genuine_log200_log100_log1000_enclosures
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

theorem actual_minimal_integer_sample_sizes (n : ℕ) :
    (Real.log 200 / (2 * (8 / 1000) ^ 2) ≤ (n : ℝ) ↔ 41394 ≤ n) ∧
    (Real.log 100 / (2 * (8 / 1000) ^ 2) ≤ (n : ℝ) ↔ 35978 ≤ n) ∧
    (Real.log 1000 / (2 * (8 / 1000) ^ 2) ≤ (n : ℝ) ↔ 53967 ≤ n) := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := actual_sample_threshold_enclosures
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro h
    have : (41393 : ℝ) < n := by linarith
    exact_mod_cast this
  · intro h
    have : (41394 : ℝ) ≤ n := by exact_mod_cast h
    linarith
  · intro h
    have : (35977 : ℝ) < n := by linarith
    exact_mod_cast this
  · intro h
    have : (35978 : ℝ) ≤ n := by exact_mod_cast h
    linarith
  · intro h
    have : (53966 : ℝ) < n := by linarith
    exact_mod_cast this
  · intro h
    have : (53967 : ℝ) ≤ n := by exact_mod_cast h
    linarith

def radius : ℝ := Real.sqrt (Real.log 200 / (2 * 34980))

theorem actual_validation_radius_enclosure :
    (870250 / 100000000 : ℝ) < radius ∧ radius < 870251 / 100000000 := by
  obtain ⟨hl,hu,_,_,_,_⟩ := genuine_log200_log100_log1000_enclosures
  obtain ⟨h4l, h4u⟩ := SafeLearning.CompleteAppliedGridConfidence.log400_enclosure
  obtain ⟨h2l, h2u⟩ := SafeLearning.CompletePolicyDivergence.log_two_enclosure
  have hlog : Real.log (200 : ℝ) = Real.log 400 - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hsharp : (5298316819 / 1000000000 : ℝ) < Real.log 200 := by
    rw [hlog]; linarith
  have hsq : radius ^ 2 = Real.log 200 / (2 * 34980) :=
    Real.sq_sqrt (by positivity)
  have hn : 0 ≤ radius := Real.sqrt_nonneg _
  constructor <;> nlinarith

theorem actual_maximum_45_failures (failures : ℕ) :
    (99 / 100 + radius ≤ 1 - (failures : ℝ) / 34980 ↔ failures ≤ 45) := by
  obtain ⟨hl,hu⟩ := actual_validation_radius_enclosure
  constructor
  · intro h
    have : (failures : ℝ) < 46 := by linarith
    have : failures < 46 := by exact_mod_cast this
    omega
  · intro h
    have : (failures : ℝ) ≤ 45 := by exact_mod_cast h
    linarith

theorem actual_successes_and_rounded_cutoff :
    (34980 - 45 : ℕ) = 34935 ∧
      (9987 / 10000 : ℝ) < 99 / 100 + radius ∧
      (2 / 1000000 : ℝ) < 99 / 100 + radius - 9987 / 10000 ∧
      99 / 100 + radius - 9987 / 10000 < 3 / 1000000 := by
  obtain ⟨hl,hu⟩ := actual_validation_radius_enclosure
  refine ⟨by norm_num,?_,?_,?_⟩ <;> linarith

theorem actual_repeated_testing_allocation_and_increase :
    (5 : ℝ) * (2 / 1000) = 1 / 100 ∧
      (3 / 10 : ℝ) < (53967 - 41394) / 41394 ∧
      (53967 - 41394 : ℝ) / 41394 < 31 / 100 := by
  norm_num

end SafeLearning.CompleteLyapunovValidationNumbers
