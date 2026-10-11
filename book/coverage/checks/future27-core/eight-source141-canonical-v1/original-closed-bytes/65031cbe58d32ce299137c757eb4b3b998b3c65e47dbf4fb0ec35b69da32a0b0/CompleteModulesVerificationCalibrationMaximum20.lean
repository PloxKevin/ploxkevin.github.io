import SafeLearning.CompleteModulesConformal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Classical

namespace SafeLearning.CompleteModulesVerificationCalibrationMaximum20
open CompleteConformal

theorem actual_full_calibration_rank_is_the_finite_calibration_supremum
    {ι : Type*} [Fintype ι] (scores : ι → ℝ) (test : ι) :
    calibrationThreshold scores test (Fintype.card ι - 1) =
      (Finset.univ.erase test).sup (fun i => (scores i : EReal)) := by
  classical
  letI : DecidableEq ι := Classical.decEq _
  unfold calibrationThreshold
  have hc : (Finset.univ.erase test).card = Fintype.card ι - 1 := by simp
  rw [← hc, Finset.powersetCard_self, Finset.inf_singleton]

theorem actual_thirty_nine_calibration_threshold_is_an_attained_real_maximum
    (scores : Fin 40 → ℝ) (test : Fin 40) :
    ∃ i : Fin 40, i ≠ test ∧
      IsGreatest (scores '' {j | j ≠ test}) (scores i) ∧
      calibrationThreshold scores test 39 = (scores i : EReal) := by
  classical
  letI : DecidableEq (Fin 40) := Classical.decEq _
  let s : Finset (Fin 40) := Finset.univ.erase test
  have hc : s.card = 39 := by simp [s]
  have hn : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi, hm⟩ := Finset.exists_mem_eq_sup s hn (fun j => (scores j : EReal))
  have hit : i ≠ test := (Finset.mem_erase.mp hi).1
  refine ⟨i, hit, ⟨⟨i,hit,rfl⟩,?_⟩,?_⟩
  · rintro y ⟨j,hjt,rfl⟩
    have hj : j ∈ s := Finset.mem_erase.mpr ⟨hjt,Finset.mem_univ _⟩
    have hle := Finset.le_sup (f := fun j => (scores j : EReal)) hj
    rw [hm] at hle
    exact EReal.coe_le_coe_iff.mp hle
  · have h := actual_full_calibration_rank_is_the_finite_calibration_supremum scores test
    norm_num at h
    exact h.trans hm

end SafeLearning.CompleteModulesVerificationCalibrationMaximum20
