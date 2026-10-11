import Mathlib
import SafeLearning.CompleteAppliedConformalRanks
import SafeLearning.CompleteConformal

set_option autoImplicit false
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteModulesConformalCommonUniform27

def unitUniform : Measure ℝ := volume.restrict (Icc 0 1)

instance actual_unit_uniform_is_probability : IsProbabilityMeasure unitUniform := by
  apply isProbabilityMeasure_iff.mpr
  rw [unitUniform,Measure.restrict_apply_univ]
  norm_num

instance actual_unit_uniform_is_atomless : NullSingletonClass unitUniform := by
  unfold unitUniform
  infer_instance

def commonScoreLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  unitUniform.map (fun u => fun _ : Fin n => u)

theorem actual_constant_vector_map_is_measurable (n : ℕ) :
    Measurable (fun u : ℝ => fun _ : Fin n => u) := by
  exact Measurable.of_eval (fun _ => measurable_id)

instance actual_common_score_law_is_probability (n : ℕ) :
    IsProbabilityMeasure (commonScoreLaw n) := by
  unfold commonScoreLaw
  infer_instance

theorem actual_common_uniform_score_joint_law_is_exchangeable (n : ℕ) :
    CompleteAppliedConformalRanks.exchangeable (commonScoreLaw n) := by
  intro permutation
  unfold commonScoreLaw
  rw [Measure.map_map
    (CompleteAppliedConformalRanks.actual_permuted_scores_are_measurable permutation)
    (actual_constant_vector_map_is_measurable n)]
  rfl

theorem actual_every_common_score_marginal_is_uniform (n : ℕ) (i : Fin n) :
    (commonScoreLaw n).map (fun scores => scores i) = unitUniform := by
  unfold commonScoreLaw
  rw [Measure.map_map (measurable_pi_apply i) (actual_constant_vector_map_is_measurable n)]
  exact Measure.map_id

theorem actual_every_common_score_marginal_has_zero_atom_mass (n : ℕ) (i : Fin n) (a : ℝ) :
    ((commonScoreLaw n).map (fun scores => scores i)) {a}=0 := by
  rw [actual_every_common_score_marginal_is_uniform]
  exact measure_singleton a

theorem actual_unit_uniform_cdf_formula (x : ℝ) :
    cdf unitUniform x = max (min x 1) 0 := by
  rw [cdf_eq_real,measureReal_def,unitUniform,Measure.restrict_apply measurableSet_Iic]
  have he : Iic x ∩ Icc (0 : ℝ) 1 = Icc 0 (min x 1) := by
    ext t
    simp only [mem_inter_iff,mem_Iic,mem_Icc,le_min_iff]
    tauto
  rw [he,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal']

theorem actual_every_common_score_marginal_cdf_is_continuous (n : ℕ) (i : Fin n) :
    Continuous (cdf ((commonScoreLaw n).map (fun scores => scores i))) := by
  rw [actual_every_common_score_marginal_is_uniform]
  have he : (cdf unitUniform : ℝ → ℝ) = fun x => max (min x 1) 0 := by
    funext x
    exact actual_unit_uniform_cdf_formula x
  rw [he]
  fun_prop

theorem actual_common_uniform_scores_are_tied_everywhere_almost_surely (n : ℕ) :
    ∀ᵐ scores ∂commonScoreLaw n, ∀ i j : Fin n, scores i=scores j := by
  unfold commonScoreLaw
  apply ae_map_iff (actual_constant_vector_map_is_measurable n).aemeasurable
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)) |>.2
  exact Filter.Eventually.of_forall (fun _ _ _ => rfl)

theorem actual_common_uniform_scores_are_always_calibration_covered (test : Fin 10) :
    ∀ᵐ scores ∂commonScoreLaw 10,
      (scores test : EReal) ≤ CompleteConformal.calibrationThreshold scores test 9 := by
  filter_upwards [actual_common_uniform_scores_are_tied_everywhere_almost_surely 10] with scores hs
  rw [←not_lt,CompleteConformal.calibration_failure_iff,not_le]
  have hr : CompleteConformal.strictRank scores test=0 := by
    unfold CompleteConformal.strictRank
    have he : (Finset.univ.filter (fun i : Fin 10 => scores i < scores test)) = ∅ := by
      ext i
      simp [hs i test]
    rw [he,Finset.card_empty]
  rw [hr]
  norm_num

theorem actual_continuous_marginals_do_not_give_the_strict_upper_coverage_bound
    (test : Fin 10) :
    (commonScoreLaw 10).real {scores | (scores test : EReal) ≤ CompleteConformal.calibrationThreshold scores test 9}=1 ∧
      ¬((commonScoreLaw 10).real {scores | (scores test : EReal) ≤ CompleteConformal.calibrationThreshold scores test 9}<
        1-(1/10 : ℝ)+1/10) := by
  have he : {scores : Fin 10 → ℝ | (scores test : EReal) ≤ CompleteConformal.calibrationThreshold scores test 9} =ᵐ[commonScoreLaw 10] univ := by
    filter_upwards [actual_common_uniform_scores_are_always_calibration_covered test] with scores h
    simp [h]
  have hp : (commonScoreLaw 10).real {scores | (scores test : EReal) ≤ CompleteConformal.calibrationThreshold scores test 9}=1 := by
    rw [measureReal_congr he]
    simp
  rw [hp]
  norm_num

end SafeLearning.CompleteModulesConformalCommonUniform27
