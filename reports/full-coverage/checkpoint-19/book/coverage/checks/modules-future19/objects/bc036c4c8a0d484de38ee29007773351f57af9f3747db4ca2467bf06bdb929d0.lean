import SafeLearning.CompleteModulesLandscapeARStationaryGaussian
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SafeLearning.CompleteModulesLandscapeStationaryCharacterization
open CompleteModulesLandscapeARStationaryGaussian

def updatedVariance (k sigma : ℝ) (v : ℝ≥0) : ℝ≥0 :=
  NNReal.mk ((1-k)^2) (sq_nonneg (1-k))*v + NNReal.mk (sigma^2) (sq_nonneg sigma)

def updatedLaw (k goal sigma : ℝ) (v : ℝ≥0) : Measure ℝ :=
  ((gaussianReal goal v).prod (gaussianReal 0 1)).map
    (fun z : ℝ × ℝ => z.1-k*(z.1-goal)+sigma*z.2)

theorem actual_arbitrary_gaussian_state_and_independent_fresh_noise_have_the_source_updated_law
    (k goal sigma : ℝ) (v : ℝ≥0) :
    updatedLaw k goal sigma v = gaussianReal goal (updatedVariance k sigma v) := by
  let P := (gaussianReal goal v).prod (gaussianReal 0 1)
  have hx : HasLaw (fun z : ℝ × ℝ => z.1) (gaussianReal goal v) P :=
    measurePreserving_fst.hasLaw
  have hw : HasLaw (fun z : ℝ × ℝ => z.2) (gaussianReal 0 1) P :=
    measurePreserving_snd.hasLaw
  have hind : IndepFun (fun z : ℝ × ℝ => z.1) (fun z : ℝ × ℝ => z.2) P :=
    indepFun_prod measurable_id measurable_id
  have hs := gaussianReal_add_gaussianReal_of_indepFun
    (hind.comp (show Measurable (fun x : ℝ => (1-k)*x) by fun_prop)
      (show Measurable (fun w : ℝ => sigma*w) by fun_prop))
    (gaussianReal_const_mul hx (1-k)) (gaussianReal_const_mul hw sigma)
  have hl : HasLaw (fun z : ℝ × ℝ => (1-k)*z.1+sigma*z.2)
      (gaussianReal ((1-k)*goal+sigma*0)
        (NNReal.mk ((1-k)^2) (sq_nonneg (1-k))*v+
          NNReal.mk (sigma^2) (sq_nonneg sigma)*1)) P := ⟨by fun_prop,hs⟩
  have hshift := gaussianReal_add_const hl (k*goal)
  have hm : (1-k)*goal+sigma*0+k*goal = goal := by ring
  rw [hm,mul_one] at hshift
  have he : (fun z : ℝ × ℝ => z.1-k*(z.1-goal)+sigma*z.2) =
      (fun z : ℝ × ℝ => ((1-k)*z.1+sigma*z.2)+k*goal) := by funext z; ring
  change P.map (fun z : ℝ × ℝ => z.1-k*(z.1-goal)+sigma*z.2) = _
  rw [he]
  exact hshift.map_eq

theorem actual_gaussian_law_is_unchanged_exactly_when_the_true_variance_is_fixed
    (k goal sigma : ℝ) (v : ℝ≥0) :
    updatedLaw k goal sigma v = gaussianReal goal v ↔
      (1-k)^2*(v:ℝ)+sigma^2 = (v:ℝ) := by
  rw [actual_arbitrary_gaussian_state_and_independent_fresh_noise_have_the_source_updated_law,
    gaussianReal_ext_iff]
  simp only [true_and,NNReal.eq_iff,updatedVariance,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_mk]

theorem actual_stable_gain_has_exactly_the_printed_gaussian_stationary_variance
    (k goal sigma : ℝ) (v : ℝ≥0) (hk : 0 < k) (hk2 : k < 2) :
    updatedLaw k goal sigma v = gaussianReal goal v ↔
      (v:ℝ) = sigma^2/(k*(2-k)) := by
  rw [actual_gaussian_law_is_unchanged_exactly_when_the_true_variance_is_fixed]
  have hd : k*(2-k) ≠ 0 := ne_of_gt (mul_pos hk (by linarith))
  rw [eq_div_iff hd]
  constructor <;> intro h <;> nlinarith

theorem actual_unique_stationary_gaussian_variance_is_the_existing_stationary_law
    (k goal sigma : ℝ) (v : ℝ≥0) (hk : 0 < k) (hk2 : k < 2) :
    updatedLaw k goal sigma v = gaussianReal goal v ↔
      gaussianReal goal v = stationaryLaw k goal sigma := by
  rw [actual_stable_gain_has_exactly_the_printed_gaussian_stationary_variance k goal sigma v hk hk2]
  unfold stationaryLaw
  rw [gaussianReal_ext_iff]
  simp only [true_and,NNReal.eq_iff,
    actual_stationary_variance_is_the_printed_nonnegative_real_variance k sigma hk hk2]

end SafeLearning.CompleteModulesLandscapeStationaryCharacterization
