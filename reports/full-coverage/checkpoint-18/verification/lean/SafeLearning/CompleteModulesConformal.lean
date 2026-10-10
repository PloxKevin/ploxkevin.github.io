import SafeLearning.CompleteConformal

set_option autoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteModulesConformal

theorem ninety_nine_finite_rank_iff (n : ℕ) :
    SafeLearning.CompleteConformal.conformalRank n (1/100) ≤ n ↔ 99 ≤ n := by
  unfold SafeLearning.CompleteConformal.conformalRank
  rw [Nat.ceil_le]
  push_cast
  constructor
  · intro h
    have hn : (99:ℝ) ≤ n := by linarith
    exact_mod_cast hn
  · intro h
    have hn : (99:ℝ) ≤ n := by exact_mod_cast h
    linarith

theorem rank_ninety_nine_one_percent :
    SafeLearning.CompleteConformal.conformalRank 99 (1/100)=99 := by
  norm_num [SafeLearning.CompleteConformal.conformalRank]

theorem whole_trajectory_ninety_nine_coverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (scores : Ω → Fin 100 → ℝ)
    (hm : Measurable scores)
    (hex : ∀ p : Equiv.Perm (Fin 100),
      IdentDistrib (fun ω i => scores ω (p i)) scores μ μ)
    (test : Fin 100) :
    99/100 ≤ μ.real {ω | (scores ω test : EReal) ≤
      SafeLearning.CompleteConformal.calibrationThreshold (scores ω) test 99} := by
  have h := SafeLearning.CompleteConformal.split_conformal_coverage
    99 μ scores hm hex (1/100) (by norm_num) test
  rw [rank_ninety_nine_one_percent] at h
  norm_num at h ⊢
  exact h

theorem finite_horizon_score_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (residual : ι → ℝ) (radius : ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => |residual i|) ≤ radius ↔
      ∀ i, |residual i| ≤ radius := by
  rw [Finset.sup'_le_iff]
  simp

theorem nine_calibration_rank :
    SafeLearning.CompleteConformal.conformalRank 9 (1/5)=8 := by
  norm_num [SafeLearning.CompleteConformal.conformalRank]

theorem thirty_nine_calibration_rank :
    SafeLearning.CompleteConformal.conformalRank 39 (1/40)=39 ∧
    SafeLearning.CompleteConformal.conformalRank 19 (1/40)=20 := by
  norm_num [SafeLearning.CompleteConformal.conformalRank]

end SafeLearning.CompleteModulesConformal
