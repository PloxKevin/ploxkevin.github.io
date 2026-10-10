import SafeLearning.CompleteFoundationsHingeExpectations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsCVaRQuotients
open CompleteFoundationsHingeExpectations

def actualRUObjective {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (loss : Ω → ℝ) (alpha threshold : ℝ) : ℝ :=
  threshold + (1 / (1 - alpha)) * ∫ omega, hinge (loss omega) threshold ∂P

theorem actual_RU_one_sided_difference_quotients_follow_from_true_bounded_convergence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (loss : Ω → ℝ) (hm : Measurable loss) (hi : Integrable loss P)
    (alpha center : ℝ) (_halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    Tendsto (fun threshold =>
      (actualRUObjective P loss alpha threshold - actualRUObjective P loss alpha center) /
        (threshold - center)) (𝓝[>] center)
      (𝓝 (1 - P.real {omega | center < loss omega} / (1 - alpha))) ∧
    Tendsto (fun threshold =>
      (actualRUObjective P loss alpha threshold - actualRUObjective P loss alpha center) /
        (threshold - center)) (𝓝[<] center)
      (𝓝 (1 - P.real {omega | center ≤ loss omega} / (1 - alpha))) := by
  have hr := actual_bounded_convergence_moves_both_one_sided_hinge_quotients_through_expectation
    loss hm hi center
  have hg (threshold : ℝ) (hne : threshold ≠ center) :
      (actualRUObjective P loss alpha threshold - actualRUObjective P loss alpha center) /
        (threshold - center) = 1 + (1 / (1 - alpha)) *
          (((∫ omega, hinge (loss omega) threshold ∂P) -
            (∫ omega, hinge (loss omega) center ∂P)) / (threshold - center)) := by
    unfold actualRUObjective
    field_simp [sub_ne_zero.mpr hne, (sub_pos.mpr halpha1).ne']
    ring
  constructor
  · have ht := (hr.1.const_mul (1 / (1 - alpha))).const_add 1
    have heq : (1 : ℝ) + 1 / (1 - alpha) * (-P.real {omega | center < loss omega}) =
        1 - P.real {omega | center < loss omega} / (1 - alpha) := by ring
    rw [heq] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with threshold hn
    change center < threshold at hn
    exact (hg threshold hn.ne').symm
  · have ht := (hr.2.const_mul (1 / (1 - alpha))).const_add 1
    have heq : (1 : ℝ) + 1 / (1 - alpha) * (-P.real {omega | center ≤ loss omega}) =
        1 - P.real {omega | center ≤ loss omega} / (1 - alpha) := by ring
    rw [heq] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with threshold hn
    change threshold < center at hn
    exact (hg threshold hn.ne).symm

end SafeLearning.CompleteFoundationsCVaRQuotients
