import SafeLearning.CompletePolicyCPOExampleRegimes

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix
namespace SafeLearning.CompletePolicyCPOPrintedDualValues
open CompletePolicyQuadraticDual CompletePolicyCPOExample CompletePolicyCPOExampleRegimes

theorem actual_printed_active_dual_radical_is_the_true_optimal_value :
    Real.sqrt ((actualQ-actualR^2/actualS)*(2*δ-c^2/actualS))-actualR*c/actualS =
      (7*root+90)/1450 ∧
    actualDual H g b c δ (lam,nu) =
      Real.sqrt ((actualQ-actualR^2/actualS)*(2*δ-c^2/actualS))-actualR*c/actualS := by
  have hp : 0 ≤ 7*root/1450 := by
    have hr : 0 ≤ root := Real.sqrt_nonneg _
    positivity
  have hs : (7*root/1450)^2=(actualQ-actualR^2/actualS)*(2*δ-c^2/actualS) := by
    dsimp [actualQ,actualR,actualS,δ,c]
    nlinarith [actual_root_enclosure.2.2]
  have he : Real.sqrt ((actualQ-actualR^2/actualS)*(2*δ-c^2/actualS))-actualR*c/actualS =
      (7*root+90)/1450 := by
    rw [←hs,Real.sqrt_sq hp]
    dsimp [actualR,actualS,c]
    ring
  exact ⟨he,actual_projected_dual_value_and_true_active_value.2.1.trans he.symm⟩

theorem actual_projected_dual_price_minimizes_the_literal_inactive_regime
    (price : ℝ) (hp : actualR/|c| ≤ price) :
    actualDual H g b c δ (actualProjectedLambda,0) ≤ actualDual H g b c δ (price,0) := by
  have hend : actualR/|c|=(144/35:ℝ) := actual_lambda_b_projection_is_the_true_endpoint.1
  have hprice : (144/35:ℝ) ≤ price := by rwa [hend] at hp
  have hpos : 0 < price := lt_of_lt_of_le (by norm_num) hprice
  have hcoeff : 0 ≤ δ-actualQ/(2*price*(144/35)) := by
    have hden : 2*(144/35:ℝ)*(144/35) ≤ 2*price*(144/35) := by nlinarith
    have hq : 0 ≤ actualQ := by norm_num [actualQ]
    have hbound := div_le_div_of_nonneg_left hq (by norm_num : (0:ℝ)<2*(144/35)*(144/35)) hden
    have hbase : actualQ/(2*(144/35)*(144/35)) ≤ δ := by norm_num [actualQ,δ]
    linarith
  have hproduct : 0 ≤ (price-144/35)*(δ-actualQ/(2*price*(144/35))) :=
    mul_nonneg (sub_nonneg.mpr hprice) hcoeff
  have he : actualQ/(2*price)+price*δ-(actualQ/(2*(144/35))+(144/35)*δ) =
      (price-144/35)*(δ-actualQ/(2*price*(144/35))) := by
    field_simp [ne_of_gt hpos]
    <;> ring
  rw [actual_lambda_b_projection_is_the_true_endpoint.2.1,
    actual_true_supremum_equals_closed_dual H actual_metric_positive_definite g b c δ (144/35) 0 (by norm_num),
    actual_true_supremum_equals_closed_dual H actual_metric_positive_definite g b c δ price 0 hpos]
  simp only [closedDual,zero_smul,sub_zero,zero_mul,sub_zero,
    actual_source_q_r_s_match_the_true_inverse_forms.1]
  linarith

end SafeLearning.CompletePolicyCPOPrintedDualValues
