import SafeLearning.CompleteModulesLandscapeARGaussianLaw
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SafeLearning.CompleteModulesLandscapeARStationaryGaussian

def stationaryVariance (k sigma : ℝ) : ℝ≥0 := (sigma ^ 2 / (k * (2-k))).toNNReal
def stationaryLaw (k goal sigma : ℝ) : Measure ℝ :=
  gaussianReal goal (stationaryVariance k sigma)

theorem actual_stationary_variance_is_the_printed_nonnegative_real_variance
    (k sigma : ℝ) (hk : 0 < k) (hk2 : k < 2) :
    (stationaryVariance k sigma : ℝ) = sigma ^ 2 / (k * (2-k)) := by
  unfold stationaryVariance
  exact Real.coe_toNNReal _ (div_nonneg (sq_nonneg sigma) (mul_nonneg hk.le (by linarith)))

theorem actual_stationary_variance_is_fixed_by_the_source_variance_update
    (k sigma : ℝ) (hk : 0 < k) (hk2 : k < 2) :
    (⟨(1-k)^2, sq_nonneg (1-k)⟩ : ℝ≥0) * stationaryVariance k sigma +
      (⟨sigma^2, sq_nonneg sigma⟩ : ℝ≥0) = stationaryVariance k sigma := by
  apply NNReal.eq
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk,
    actual_stationary_variance_is_the_printed_nonnegative_real_variance k sigma hk hk2]
  have hd : k * (2-k) ≠ 0 := ne_of_gt (mul_pos hk (by linarith))
  field_simp
  ring

theorem actual_stable_gaussian_law_is_invariant_under_one_update_with_independent_standard_noise
    (k goal sigma : ℝ) (hk : 0 < k) (hk2 : k < 2) :
    ((stationaryLaw k goal sigma).prod (gaussianReal 0 1)).map
      (fun z : ℝ × ℝ => z.1 - k * (z.1-goal) + sigma * z.2) =
      stationaryLaw k goal sigma := by
  let v := stationaryVariance k sigma
  let P := (gaussianReal goal v).prod (gaussianReal 0 1)
  have hx : HasLaw (fun z : ℝ × ℝ => z.1) (gaussianReal goal v) P :=
    measurePreserving_fst.hasLaw
  have hw : HasLaw (fun z : ℝ × ℝ => z.2) (gaussianReal 0 1) P :=
    measurePreserving_snd.hasLaw
  have hind : IndepFun (fun z : ℝ × ℝ => z.1) (fun z : ℝ × ℝ => z.2) P :=
    indepFun_prod measurable_id measurable_id
  have hscaled := hind.comp
    (show Measurable (fun x : ℝ => (1-k)*x) by fun_prop)
    (show Measurable (fun w : ℝ => sigma*w) by fun_prop)
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hscaled
    (gaussianReal_const_mul hx (1-k)) (gaussianReal_const_mul hw sigma)
  have hsumLaw : HasLaw (fun z : ℝ × ℝ => (1-k)*z.1 + sigma*z.2)
      (gaussianReal ((1-k)*goal + sigma*0)
        ((⟨(1-k)^2, sq_nonneg (1-k)⟩ : ℝ≥0)*v +
          (⟨sigma^2, sq_nonneg sigma⟩ : ℝ≥0)*1)) P := by
    exact ⟨by fun_prop, hsum⟩
  have hshift := gaussianReal_add_const hsumLaw (k*goal)
  have hm : (1-k)*goal + sigma*0 + k*goal = goal := by ring
  have hv : (⟨(1-k)^2, sq_nonneg (1-k)⟩ : ℝ≥0)*v +
      (⟨sigma^2, sq_nonneg sigma⟩ : ℝ≥0)*1 = v := by
    simpa only [mul_one] using
      actual_stationary_variance_is_fixed_by_the_source_variance_update k sigma hk hk2
  rw [hm, hv] at hshift
  have he : (fun z : ℝ × ℝ => z.1 - k*(z.1-goal) + sigma*z.2) =
      (fun z : ℝ × ℝ => ((1-k)*z.1 + sigma*z.2) + k*goal) := by
    funext z
    ring
  change P.map (fun z : ℝ × ℝ => z.1 - k*(z.1-goal) + sigma*z.2) = gaussianReal goal v
  rw [he]
  exact hshift.map_eq

theorem actual_zero_noise_stationary_law_is_the_deterministic_goal
    (k goal : ℝ) : stationaryLaw k goal 0 = Measure.dirac goal := by
  simp [stationaryLaw, stationaryVariance]

end SafeLearning.CompleteModulesLandscapeARStationaryGaussian
