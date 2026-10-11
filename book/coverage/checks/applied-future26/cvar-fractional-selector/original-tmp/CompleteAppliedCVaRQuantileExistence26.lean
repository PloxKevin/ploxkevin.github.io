import SafeLearning.CompleteAppliedFractionalTailDual
import Mathlib.Probability.CDF

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedCVaRQuantileExistence26

/-- Every real probability law, including laws with atoms and gaps, has an
attained quantile whose lower and upper CDF values bracket each interior level. -/
theorem actual_arbitrary_real_probability_has_an_attained_fractional_tail_threshold
    (P : Measure ℝ) [IsProbabilityMeasure P] (alpha : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ threshold : ℝ,
      Function.leftLim (cdf P) threshold ≤ alpha ∧ alpha ≤ cdf P threshold := by
  let upper : Set ℝ := {x | alpha ≤ cdf P x}
  obtain ⟨above, habove⟩ := ((tendsto_cdf_atTop P).eventually (eventually_gt_nhds ha1)).exists
  obtain ⟨below, hbelow⟩ := ((tendsto_cdf_atBot P).eventually (eventually_lt_nhds ha0)).exists
  have hnonempty : upper.Nonempty := ⟨above, habove.le⟩
  have hbounded : BddBelow upper := by
    refine ⟨below, ?_⟩
    intro x hx
    by_contra h
    have horder : x ≤ below := le_of_lt (lt_of_not_ge h)
    have hcdf := (monotone_cdf P) horder
    exact (not_le_of_gt hbelow) ((show alpha ≤ cdf P x from hx).trans hcdf)
  let threshold : ℝ := sInf upper
  have haboveroot : ∀ x : Ioi threshold, alpha ≤ cdf P x := by
    intro x
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hnonempty x.property
    exact (show alpha ≤ cdf P y from hy).trans ((monotone_cdf P) hyx.le)
  have hroot : alpha ≤ cdf P threshold := by
    letI : Nonempty (Ioi threshold) := ⟨⟨threshold + 1, by simp⟩⟩
    rw [← (cdf P).iInf_Ioi_eq threshold]
    exact le_ciInf haboveroot
  have hbelowroot : ∀ x : ℝ, x < threshold → cdf P x < alpha := by
    intro x hx
    by_contra h
    have hmember : x ∈ upper := le_of_not_gt h
    exact (not_le_of_gt hx) (csInf_le hbounded hmember)
  have hleft : Function.leftLim (cdf P) threshold ≤ alpha := by
    rw [(monotone_cdf P).leftLim_eq_sSup]
    apply csSup_le
    · exact ⟨cdf P (threshold - 1), ⟨threshold - 1, by simp, rfl⟩⟩
    · rintro y ⟨x, hx, rfl⟩
      exact (hbelowroot x hx).le
  exact ⟨threshold, hleft, hroot⟩

end SafeLearning.CompleteAppliedCVaRQuantileExistence26
