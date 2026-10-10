import SafeLearning.CompletePolicyCPOExample
import SafeLearning.CompletePolicyFeasibleTRPO

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix
namespace SafeLearning.CompletePolicyCPOExampleRegimes
open CompletePolicyQuadraticDual CompletePolicyCPOExample

def actualQ : ℝ := 92/175
def actualR : ℝ := 72/175
def actualS : ℝ := 116/175
def actualTRPOScale : ℝ := Real.sqrt (2 * δ / actualQ)
def actualProjectedLambda : ℝ := max (Real.sqrt (actualQ / (2 * δ))) (actualR / |c|)

theorem actual_source_q_r_s_match_the_true_inverse_forms :
    g ⬝ᵥ (H⁻¹ *ᵥ g) = actualQ ∧ g ⬝ᵥ (H⁻¹ *ᵥ b) = actualR ∧
    b ⬝ᵥ (H⁻¹ *ᵥ b) = actualS := by
  exact ⟨actual_exact_q_r_s_and_reduced_radicands.1,
    actual_exact_q_r_s_and_reduced_radicands.2.1,
    actual_exact_q_r_s_and_reduced_radicands.2.2.1⟩

theorem actual_hyperplane_strictly_cuts_the_trust_region :
    0 < actualS ∧ c < 0 ∧ c ^ 2 / actualS < 2 * δ := by
  norm_num [actualS,c,δ]

theorem actual_source_reduced_radicands_and_four_decimal_roundings :
    actualQ - actualR^2/actualS = 196/725 ∧ 2*δ-c^2/actualS = 197/2320 ∧
    |(actualQ - actualR^2/actualS)-(2703/10000:ℝ)| < 1/20000 ∧
    |(2*δ-c^2/actualS)-(849/10000:ℝ)| < 1/20000 ∧
    |c^2/actualS-(151/10000:ℝ)| < 1/20000 := by
  norm_num [actualQ,actualR,actualS,c,δ,abs_lt]

theorem actual_TRPO_scale_and_strict_violation_are_certified :
    (43613/100000:ℝ) < actualTRPOScale ∧ actualTRPOScale < 43614/100000 ∧
    0 < c + actualR*actualTRPOScale ∧
    |(c + actualR*actualTRPOScale)-(79/1000:ℝ)| < 1/2000 := by
  have hs : actualTRPOScale^2=(35/184:ℝ) := by
    rw [actualTRPOScale,Real.sq_sqrt (by norm_num [δ,actualQ])]
    norm_num [δ,actualQ]
  have hn : 0 ≤ actualTRPOScale := Real.sqrt_nonneg _
  have hlo : (43613/100000:ℝ)<actualTRPOScale := by nlinarith
  have hhi : actualTRPOScale<(43614/100000:ℝ) := by nlinarith
  refine ⟨hlo,hhi,?_,?_⟩
  · dsimp [c,actualR];linarith
  · rw [abs_lt];dsimp [c,actualR];constructor <;> linarith

theorem actual_radical_price_equals_the_source_lambda_a :
    lam = Real.sqrt ((actualQ-actualR^2/actualS)/(2*δ-c^2/actualS)) := by
  have hp : 0 < root := lt_trans (by norm_num) actual_root_enclosure.1
  have hl : 0 ≤ lam := le_of_lt actual_multipliers_and_candidate_are_the_actual_inverse_optimizer.1
  have hs : lam^2=(3136/985:ℝ) := by
    dsimp [lam]
    rw [div_pow,actual_root_enclosure.2.2]
    norm_num
  have hr : (actualQ-actualR^2/actualS)/(2*δ-c^2/actualS)=(3136/985:ℝ) := by
    norm_num [actualQ,actualR,actualS,δ,c]
  rw [hr,←hs,Real.sqrt_sq hl]

theorem actual_lambda_a_domain_and_nu_equation :
    0 < lam ∧ lam < actualR / |c| ∧ 0 < nu ∧
    nu = (lam*c+actualR)/actualS := by
  have hp : 0 < root := lt_trans (by norm_num) actual_root_enclosure.1
  have hu : lam < 2 := by
    unfold lam
    exact (div_lt_iff₀ hp).mpr (by nlinarith [actual_root_enclosure.1])
  refine ⟨actual_multipliers_and_candidate_are_the_actual_inverse_optimizer.1,?_,
    actual_multipliers_and_candidate_are_the_actual_inverse_optimizer.2.1,?_⟩
  · norm_num [actualR,c];linarith
  · dsimp [nu,actualR,actualS,c];ring

theorem actual_lambda_b_projection_is_the_true_endpoint :
    actualR/|c|=(144/35:ℝ) ∧ actualProjectedLambda=144/35 ∧
    |Real.sqrt (actualQ/(2*δ))-(229/100:ℝ)|<1/200 ∧
    |actualProjectedLambda-(411/100:ℝ)|<1/200 := by
  have hn : 0 ≤ Real.sqrt (actualQ/(2*δ)) := Real.sqrt_nonneg _
  have hs : (Real.sqrt (actualQ/(2*δ)))^2=(184/35:ℝ) := by
    rw [Real.sq_sqrt (by norm_num [actualQ,δ])];norm_num [actualQ,δ]
  have hle : Real.sqrt (actualQ/(2*δ)) ≤ (144/35:ℝ) := by nlinarith
  have he : actualR/|c|=(144/35:ℝ) := by norm_num [actualR,c]
  refine ⟨he,?_,?_,?_⟩
  · dsimp [actualProjectedLambda];rw [he,max_eq_right hle]
  · rw [abs_lt];constructor <;> nlinarith
  · dsimp [actualProjectedLambda];rw [he,max_eq_right hle];norm_num

theorem actual_projected_dual_value_and_true_active_value :
    actualDual H g b c δ (actualProjectedLambda,0) = 3397/12600 ∧
    actualDual H g b c δ (lam,nu) = (7*root+90)/1450 ∧
    actualDual H g b c δ (lam,nu) < actualDual H g b c δ (actualProjectedLambda,0) := by
  have hb := actual_lambda_b_projection_is_the_true_endpoint.2.1
  have hD : actualDual H g b c δ (actualProjectedLambda,0)=(3397/12600:ℝ) := by
    rw [hb,actual_true_supremum_equals_closed_dual H actual_metric_positive_definite
      g b c δ (144/35) 0 (by norm_num)]
    simp only [closedDual,zero_smul,sub_zero,zero_mul,sub_zero]
    rw [actual_exact_q_r_s_and_reduced_radicands.1]
    norm_num [δ]
  have ha : actualDual H g b c δ (lam,nu)=(7*root+90)/1450 := by
    rw [actual_candidate_has_zero_true_primal_dual_gap]
    simp [g,candidate,dotProduct,Fin.sum_univ_two]
    ring
  refine ⟨hD,ha,?_⟩
  rw [ha,hD]
  nlinarith [actual_root_enclosure.2.1]

theorem actual_q_r_s_and_projected_dual_certified_decimal_roundings :
    |actualQ-(526/1000:ℝ)|<1/2000 ∧ |actualR-(411/1000:ℝ)|<1/2000 ∧
    |actualS-(663/1000:ℝ)|<1/2000 ∧
    |actualDual H g b c δ (actualProjectedLambda,0)-(270/1000:ℝ)|<1/2000 := by
  rw [actual_projected_dual_value_and_true_active_value.1]
  norm_num [actualQ,actualR,actualS,abs_lt]

end SafeLearning.CompletePolicyCPOExampleRegimes
