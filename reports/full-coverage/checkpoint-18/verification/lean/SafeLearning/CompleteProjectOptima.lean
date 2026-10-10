import SafeLearning.CompleteBookProjects

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteProjectOptima

open SafeLearning.CompleteBookProjects

def trueSafety (_a : ℝ) : ℝ := 4 / 25

def certifiedSet : Set ℝ :=
  {a | a ∈ Icc 0 1 ∧
    (0 ≤ tuningLower (9 / 50) (1 / 50) (1 / 5) a ∨
     0 ≤ tuningLower (7 / 50) (1 / 50) (1 / 2) a)}

theorem actual_certificate_set : certifiedSet = Icc 0 (37 / 50) := by
  have he : certifiedSet = Icc (0 : ℝ) (13 / 25) ∪ Icc (13 / 50) (37 / 50) := by
    ext a
    change (a ∈ Icc 0 1 ∧ (_ ∨ _)) ↔ _
    rw [and_or_left]
    exact or_congr (tuning_first_set a) (tuning_second_set a)
  exact he.trans tuning_union

theorem true_safety_observations_compatible :
    |trueSafety (1 / 5) - 9 / 50| ≤ 1 / 50 ∧
    |trueSafety (1 / 2) - 7 / 50| ≤ 1 / 50 ∧
    ∀ a b : ℝ, |trueSafety a - trueSafety b| ≤ (1 / 2) * |a - b| := by
  refine ⟨by norm_num [trueSafety], by norm_num [trueSafety], ?_⟩
  intro a b
  simp only [trueSafety, sub_self, abs_zero]
  positivity

theorem actual_truly_safe_set : {a : ℝ | a ∈ Icc 0 1 ∧ 0 ≤ trueSafety a} = Icc 0 1 := by
  ext a
  norm_num [trueSafety]

theorem certified_identity_maximum : IsGreatest certifiedSet (37 / 50) := by
  rw [actual_certificate_set]
  refine ⟨⟨by norm_num, le_rfl⟩, ?_⟩
  intro a ha
  exact ha.2

theorem full_identity_maximum :
    IsGreatest {a : ℝ | a ∈ Icc 0 1 ∧ 0 ≤ trueSafety a} 1 := by
  rw [actual_truly_safe_set]
  refine ⟨⟨by norm_num, le_rfl⟩, ?_⟩
  intro a ha
  exact ha.2

theorem certified_optimum_misses_full_safe_optimum :
    (1 : ℝ) ∉ certifiedSet ∧ 0 < trueSafety 1 ∧
      ∀ a ∈ certifiedSet, (fun x : ℝ => x) a < (fun x : ℝ => x) 1 := by
  rw [actual_certificate_set]
  refine ⟨by norm_num, by norm_num [trueSafety], ?_⟩
  intro a ha
  dsimp
  linarith [ha.2]

end SafeLearning.CompleteProjectOptima
