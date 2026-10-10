import SafeLearning.CompleteBarrierDiscontinuousSign
import SafeLearning.CompleteBarrierFilippovHalfspaces

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SafeLearning.CompleteBarrierSignFilippov

theorem genuine_positive_point_outside_null_set (r : ℝ) (hr : 0 < r)
    (N : Set ℝ) (hN : volume N = 0) : ∃ z ∈ Ioo 0 r, z ∉ N := by
  by_contra hn
  push Not at hn
  have hsub : Ioo 0 r ⊆ N := fun z hz => hn z hz
  have hz := measure_mono_null hsub hN
  rw [Real.volume_Ioo] at hz
  have hp : (0 : ENNReal) < ENNReal.ofReal (r - 0) := by positivity
  rw [hz] at hp
  exact lt_irrefl _ hp

theorem genuine_negative_point_outside_null_set (r : ℝ) (hr : 0 < r)
    (N : Set ℝ) (hN : volume N = 0) : ∃ z ∈ Ioo (-r) 0, z ∉ N := by
  by_contra hn
  push Not at hn
  have hsub : Ioo (-r) 0 ⊆ N := fun z hz => hn z hz
  have hz := measure_mono_null hsub hN
  rw [Real.volume_Ioo] at hz
  have hp : (0 : ENNReal) < ENNReal.ofReal (0 - (-r)) :=
    ENNReal.ofReal_pos.mpr (by linarith)
  rw [hz] at hp
  exact lt_irrefl _ hp

/-- The actual Filippov velocity set of the source's sign-field example at
zero is the entire interval [-1,1], including after deleting ANY null set. -/
theorem genuine_sign_filippov_at_zero :
    CompleteBarrierFilippovHalfspaces.velocities volume
      CompleteBarrierDiscontinuousSign.field 0 = Icc (-1 : ℝ) 1 := by
  apply Subset.antisymm
  · intro v hv
    have h := mem_iInter.mp (mem_iInter.mp (mem_iInter.mp
      (mem_iInter.mp hv 1) (by norm_num)) ∅) (by simp)
    have hs : CompleteBarrierDiscontinuousSign.field '' (Metric.ball 0 1 \ ∅)
        ⊆ Icc (-1 : ℝ) 1 := by
      rintro w ⟨z, _, rfl⟩
      unfold CompleteBarrierDiscontinuousSign.field
      split_ifs <;> norm_num
    exact closure_minimal (convexHull_min hs (convex_Icc _ _)) isClosed_Icc h
  · intro v hv
    apply mem_iInter.mpr
    intro r
    apply mem_iInter.mpr
    intro hr
    apply mem_iInter.mpr
    intro N
    apply mem_iInter.mpr
    intro hN
    obtain ⟨zp, hzp, hzpN⟩ := genuine_positive_point_outside_null_set r hr N hN
    obtain ⟨zn, hzn, hznN⟩ := genuine_negative_point_outside_null_set r hr N hN
    let A := CompleteBarrierDiscontinuousSign.field '' (Metric.ball 0 r \ N)
    have hminus : (-1 : ℝ) ∈ convexHull ℝ A := by
      apply subset_convexHull
      refine ⟨zp, ⟨?_, hzpN⟩, ?_⟩
      · simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hzp.1] using hzp.2
      · simp [CompleteBarrierDiscontinuousSign.field, not_lt.mpr hzp.1.le]
    have hplus : (1 : ℝ) ∈ convexHull ℝ A := by
      apply subset_convexHull
      refine ⟨zn, ⟨?_, hznN⟩, ?_⟩
      · simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg hzn.2]
        linarith [hzn.1]
      · simp [CompleteBarrierDiscontinuousSign.field, hzn.2]
    have hcomb := convex_convexHull ℝ A hplus hminus
      (show 0 ≤ (1 + v) / 2 by linarith [hv.1])
      (show 0 ≤ (1 - v) / 2 by linarith [hv.2])
      (show (1 + v) / 2 + (1 - v) / 2 = 1 by ring)
    have heq : ((1 + v) / 2) • (1 : ℝ) + ((1 - v) / 2) • (-1 : ℝ) = v := by
      simp only [smul_eq_mul]
      ring
    rw [heq] at hcomb
    exact subset_closure hcomb

/-- Unlike the Caratheodory ODE, its Filippov inclusion really has the
stationary absolutely continuous solution from zero. -/
theorem genuine_stationary_filippov_solution (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => (0 : ℝ)) a b ∧
    ∀ t : ℝ, HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t ∧
      (0 : ℝ) ∈ CompleteBarrierFilippovHalfspaces.velocities volume
        CompleteBarrierDiscontinuousSign.field 0 := by
  refine ⟨?_, fun t => ⟨hasDerivAt_const t 0, ?_⟩⟩
  · apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  · rw [genuine_sign_filippov_at_zero]
    norm_num

end SafeLearning.CompleteBarrierSignFilippov
