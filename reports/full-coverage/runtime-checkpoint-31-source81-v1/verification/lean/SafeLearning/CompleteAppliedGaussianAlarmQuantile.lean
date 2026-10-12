import SafeLearning.CompleteAppliedGaussianTailIntegral
import SafeLearning.CompleteAppliedGaussianQuantile
import SafeLearning.CompleteAppliedGaussianStandardization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SafeLearning.CompleteAppliedGaussianAlarmQuantile
open CompleteAppliedGaussianCDF CompleteAppliedGaussianGeneralIntegral
open CompleteAppliedGaussianTailIntegral CompleteAppliedGaussianQuantile CompleteAppliedGaussianStandardization

theorem actual_two_sided_alarm_quantile_has_a_certified_true_cdf_bracket :
    standardCDF (389059/100000:ℝ)<19999/20000 ∧
      (19999/20000:ℝ)<standardCDF (389060/100000:ℝ) := by
  have hc := actual_standard_gaussian_normalization_high_precision_rational_enclosure
  have ha := actual_gaussian_exponential_tail_integral_uniform_rational_error
    (389059/100000:ℝ) (by constructor <;> norm_num)
  have hb := actual_gaussian_exponential_tail_integral_uniform_rational_error
    (389060/100000:ℝ) (by constructor <;> norm_num)
  have hpa : (125318880492/100000000000:ℝ)<actualTailPolynomialIntegral
      (389059/100000:ℝ) ∧ actualTailPolynomialIntegral
      (389059/100000:ℝ)<125318880493/100000000000 := by
    norm_num [actualTailPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  have hpb : (125318881009/100000000000:ℝ)<actualTailPolynomialIntegral
      (389060/100000:ℝ) ∧ actualTailPolynomialIntegral
      (389060/100000:ℝ)<125318881010/100000000000 := by
    norm_num [actualTailPolynomialIntegral,Finset.sum_range_succ,Nat.factorial]
  rw [abs_le] at ha hb
  rw [actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral,
    actual_standard_gaussian_cdf_at_every_radius_is_the_true_interval_integral]
  constructor <;> nlinarith

def trueTwoSidedAlarmQuantile : ℝ := sInf {point : ℝ | (19999/20000:ℝ)≤ standardCDF point}

theorem actual_two_sided_alarm_quantile_is_the_unique_cdf_root_and_smallest_threshold :
    standardCDF trueTwoSidedAlarmQuantile=19999/20000 ∧
    (∀point:ℝ,(19999/20000:ℝ)≤ standardCDF point ↔ trueTwoSidedAlarmQuantile≤point) ∧
    (389059/100000:ℝ)<trueTwoSidedAlarmQuantile ∧
    trueTwoSidedAlarmQuantile<(389060/100000:ℝ) := by
  have hc := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing
  have hb := actual_two_sided_alarm_quantile_has_a_certified_true_cdf_bracket
  obtain ⟨root,hrange,hroot⟩ := intermediate_value_Icc
    (by norm_num : (389059/100000:ℝ)≤389060/100000)
    hc.1.continuousOn ⟨hb.1.le,hb.2.le⟩
  have hset : {point : ℝ | (19999/20000:ℝ)≤ standardCDF point}=Ici root := by
    ext point
    simp only [mem_setOf_eq,mem_Ici]
    rw [←hroot,hc.2.le_iff_le]
  have hq : trueTwoSidedAlarmQuantile=root := by
    rw [trueTwoSidedAlarmQuantile,hset,csInf_Ici]
  rw [hq]
  refine ⟨hroot,?_,?_,?_⟩
  · intro point;rw [←hroot,hc.2.le_iff_le]
  · exact hc.2.lt_iff_lt.mp (hroot.symm ▸ hb.1)
  · exact hc.2.lt_iff_lt.mp (hroot.symm ▸ hb.2)

theorem actual_standard_gaussian_two_sided_tail_probability (radius : ℝ) (hradius : 0≤radius) :
    (gaussianReal 0 1).real {point : ℝ | radius< |point|}=2*(1-standardCDF radius) := by
  haveI : NullSingletonClass (gaussianReal (0:ℝ) (1:ℝ≥0)) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hset : Iic radius\Iio (-radius)=Icc (-radius) radius := by
    ext point;simp
  have hdiff := measureReal_sdiff (μ:=gaussianReal 0 1)
    (s₁:=Iic radius) (s₂:=Iio (-radius)) (by
      intro point hp
      change point< -radius at hp
      exact hp.le.trans (by linarith)) measurableSet_Iio
  rw [hset,measureReal_congr (Iio_ae_eq_Iic (μ:=gaussianReal 0 1))] at hdiff
  change (gaussianReal 0 1).real (Icc (-radius) radius)=standardCDF radius-standardCDF (-radius) at hdiff
  rw [actual_standard_gaussian_cdf_reflection] at hdiff
  have he : {point : ℝ | radius< |point|}=(Icc (-radius) radius)ᶜ := by
    ext point
    simp only [mem_setOf_eq,mem_compl_iff,mem_Icc,←abs_le,not_le]
  have hu : (gaussianReal 0 1).real univ=1 := by simp
  rw [he,measureReal_compl measurableSet_Icc,hu,hdiff]
  ring

theorem actual_true_alarm_quantile_gives_the_required_two_sided_false_alarm_level :
    (gaussianReal 0 1).real {point : ℝ | trueTwoSidedAlarmQuantile< |point|}=1/10000 ∧
      (∀radius:ℝ,0≤radius→((gaussianReal 0 1).real {point : ℝ | radius< |point|}≤1/10000 ↔
        trueTwoSidedAlarmQuantile≤radius)) := by
  have hq := actual_two_sided_alarm_quantile_is_the_unique_cdf_root_and_smallest_threshold
  have hpos : 0≤trueTwoSidedAlarmQuantile := by linarith [hq.2.2.1]
  constructor
  · rw [actual_standard_gaussian_two_sided_tail_probability _ hpos,hq.1];norm_num
  · intro radius hr
    rw [actual_standard_gaussian_two_sided_tail_probability radius hr]
    have he := hq.2.1 radius
    constructor
    · intro h;apply he.mp;linarith
    · intro h;have hc := he.mpr h;linarith

theorem actual_printed_three_point_eight_nine_is_rounded_but_violates_the_exact_required_level :
    |trueTwoSidedAlarmQuantile-(389/100:ℝ)|<1/200 ∧
      (389/100:ℝ)<trueTwoSidedAlarmQuantile ∧
      (1/10000:ℝ)<(gaussianReal 0 1).real {point : ℝ | (389/100:ℝ)< |point|} := by
  have hq := actual_two_sided_alarm_quantile_is_the_unique_cdf_root_and_smallest_threshold
  have hlo : (389/100:ℝ)<trueTwoSidedAlarmQuantile := by linarith [hq.2.2.1]
  refine ⟨?_,hlo,?_⟩
  · rw [abs_lt];constructor <;> linarith [hq.2.2.1,hq.2.2.2]
  · have hc := actual_standard_gaussian_cdf_is_continuous_and_strictly_increasing.2 hlo
    rw [hq.1] at hc
    rw [actual_standard_gaussian_two_sided_tail_probability _ (by norm_num)]
    linarith

end SafeLearning.CompleteAppliedGaussianAlarmQuantile
