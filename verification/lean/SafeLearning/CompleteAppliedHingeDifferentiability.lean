import SafeLearning.CompleteFoundationsHingeExpectations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace SafeLearning.CompleteAppliedHingeDifferentiability
open CompleteFoundationsHingeExpectations

variable {Omega : Type*} [MeasurableSpace Omega]
variable (P : Measure Omega) [IsProbabilityMeasure P]

def hingeExpectation (loss : Omega → ℝ) (center : ℝ) : ℝ :=
  ∫ o,hinge (loss o) center ∂P

theorem actual_nonstrict_tail_probability_is_atom_plus_strict_tail
    (loss : Omega → ℝ) (hm : Measurable loss) (center : ℝ) :
    P.real {o | center≤loss o}=P.real {o | loss o=center}+P.real {o | center<loss o} := by
  have hs : {o | center≤loss o}={o | loss o=center} ∪ {o | center<loss o} := by
    ext o
    simp only [mem_ofPred_eq,mem_union]
    constructor
    · intro h
      exact (eq_or_lt_of_le h).imp Eq.symm id
    · rintro (h|h)
      · exact le_of_eq h.symm
      · exact h.le
  rw [hs]
  apply measureReal_union
  · apply Set.disjoint_left.mpr
    intro o he ht
    simp only [mem_ofPred_eq] at he ht
    linarith
  · exact measurableSet_lt measurable_const hm
  · finiteness
  · finiteness

theorem actual_hinge_expectation_right_and_left_slope_limits
    (loss : Omega → ℝ) (hm : Measurable loss) (hi : Integrable loss P) (center : ℝ) :
    Tendsto (slope (hingeExpectation P loss) center) (𝓝[>] center)
      (𝓝 (-P.real {o | center<loss o})) ∧
    Tendsto (slope (hingeExpectation P loss) center) (𝓝[<] center)
      (𝓝 (-P.real {o | center≤loss o})) := by
  have he : slope (hingeExpectation P loss) center=(fun threshold =>
      ((∫ o,hinge (loss o) threshold ∂P)-(∫ o,hinge (loss o) center ∂P))/(threshold-center)) := by
    funext threshold
    simp only [slope_def_field,hingeExpectation]
  rw [he]
  exact actual_bounded_convergence_moves_both_one_sided_hinge_quotients_through_expectation
    loss hm hi center

theorem actual_hinge_expectation_has_the_ordinary_derivative_exactly_at_atom_free_thresholds
    (loss : Omega → ℝ) (hm : Measurable loss) (hi : Integrable loss P) (center : ℝ) :
    HasDerivAt (hingeExpectation P loss) (-P.real {o | center<loss o}) center ↔
      P {o | loss o=center}=0 := by
  obtain ⟨hr,hl⟩ := actual_hinge_expectation_right_and_left_slope_limits P loss hm hi center
  have hp := actual_nonstrict_tail_probability_is_atom_plus_strict_tail P loss hm center
  constructor
  · intro hd
    have hleft := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
    have he := tendsto_nhds_unique hl hleft
    have hz : P.real {o | loss o=center}=0 := by linarith
    exact (measureReal_eq_zero_iff (by finiteness)).mp hz
  · intro hz
    have hzR : P.real {o | loss o=center}=0 := by simp [measureReal_def,hz]
    have he : P.real {o | center≤loss o}=P.real {o | center<loss o} := by linarith
    apply hasDerivAt_iff_tendsto_slope_left_right.mpr
    exact ⟨by simpa only [he] using hl,hr⟩

theorem actual_hinge_expectation_is_differentiable_iff_the_threshold_has_no_atom
    (loss : Omega → ℝ) (hm : Measurable loss) (hi : Integrable loss P) (center : ℝ) :
    DifferentiableAt ℝ (hingeExpectation P loss) center ↔ P {o | loss o=center}=0 := by
  constructor
  · intro hd
    obtain ⟨hr,hl⟩ := actual_hinge_expectation_right_and_left_slope_limits P loss hm hi center
    have hh := hasDerivAt_iff_tendsto_slope_left_right.mp hd.hasDerivAt
    have er := tendsto_nhds_unique hr hh.2
    have el := tendsto_nhds_unique hl hh.1
    have hp := actual_nonstrict_tail_probability_is_atom_plus_strict_tail P loss hm center
    have hz : P.real {o | loss o=center}=0 := by linarith
    exact (measureReal_eq_zero_iff (by finiteness)).mp hz
  · intro hz
    exact ((actual_hinge_expectation_has_the_ordinary_derivative_exactly_at_atom_free_thresholds
      P loss hm hi center).mpr hz).differentiableAt

end SafeLearning.CompleteAppliedHingeDifferentiability
