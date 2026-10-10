import SafeLearning.CompleteModulesGPLinearInformationBounds
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPLinearInformationStrictness
open CompleteModulesGPLinearInformationBounds
variable {D T : Type*} [Fintype D] [DecidableEq D] [Fintype T] [DecidableEq T]

theorem actual_psd_information_bound_uses_any_true_trace_budget
    [Nonempty D] (G : Matrix D D ℝ) (hG : G.PosSemidef) (budget lambda : ℝ)
    (hlambda : 0 < lambda) (hbudget : G.trace ≤ budget) :
    information G lambda ≤ (Fintype.card D:ℝ)/2*
      Real.log (1+budget/(lambda*(Fintype.card D:ℝ))) := by
  have he := actual_nonnegative_psd_spectrum_sums_to_the_true_trace G hG
  have hj := actual_log_jensen_bound_for_every_nonnegative_spectrum hG.isHermitian.eigenvalues lambda hlambda he.1
  rw [he.2] at hj
  have hn : (0:ℝ) < (Fintype.card D:ℝ) := by exact_mod_cast Fintype.card_pos
  have hd := mul_pos hlambda hn
  have hl := Real.log_le_log (show 0 < 1+G.trace/(lambda*(Fintype.card D:ℝ)) by
      have ht0 := Matrix.PosSemidef.trace_nonneg hG;positivity)
    (add_le_add le_rfl ((div_le_div_iff_of_pos_right hd).mpr hbudget))
  unfold information
  rw [actual_positive_semidefinite_logdet_is_the_sum_of_its_true_spectral_logarithms _ hG lambda hlambda]
  have hh := hj.trans (mul_le_mul_of_nonneg_left hl hn.le)
  nlinarith

theorem actual_every_unit_ball_design_has_the_sample_dimension_information_bound
    [Nonempty T] (X : Matrix T D ℝ) (lambda : ℝ) (hlambda : 0 < lambda)
    (hX : ∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖ ≤ 1) :
    information (Xᵀ*X) lambda ≤ (Fintype.card T:ℝ)/2*Real.log (1+1/lambda) := by
  have hPSD : (X*Xᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose X
  have htrace : (X*Xᵀ).trace ≤ (Fintype.card T:ℝ) := by
    rw [Matrix.trace_mul_comm]
    exact actual_unit_ball_design_has_total_gram_trace_at_most_its_sample_count X hX
  have h := actual_psd_information_bound_uses_any_true_trace_budget
    (X*Xᵀ) hPSD (Fintype.card T:ℝ) lambda hlambda htrace
  have he : information (Xᵀ*X) lambda=information (X*Xᵀ) lambda := by
    unfold information
    rw [actual_weinstein_aronszajn_identity_for_the_linear_design]
  rw [he]
  have hn : (Fintype.card T:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hr : (Fintype.card T:ℝ)/(lambda*(Fintype.card T:ℝ))=1/lambda := by field_simp
  simpa only [hr] using h

theorem actual_positive_smaller_sample_cap_is_strictly_below_the_larger_dimension_cap
    (samples dimension lambda : ℝ) (hSamples : 0 < samples) (hOrder : samples < dimension)
    (hlambda : 0 < lambda) :
    samples/2*Real.log (1+1/lambda) <
      dimension/2*Real.log (1+samples/(lambda*dimension)) := by
  have hDim : 0 < dimension := hSamples.trans hOrder
  have ha : 0 < samples/dimension := div_pos hSamples hDim
  have hb : 0 < 1-samples/dimension := by
    have hratio := (div_lt_one hDim).mpr hOrder
    linarith
  have hx : 0 < 1+1/lambda := by positivity
  have hxy : 1+1/lambda≠(1:ℝ) := by have hp : 0 < 1/lambda := by positivity;linarith
  have hj := strictConcaveOn_log_Ioi.2 hx zero_lt_one hxy ha hb (by ring :
    samples/dimension+(1-samples/dimension)=1)
  simp only [smul_eq_mul,Real.log_one,mul_zero,add_zero] at hj
  have hm : samples/dimension*(1+1/lambda)+(1-samples/dimension)*1=
      1+samples/(lambda*dimension) := by field_simp;ring
  rw [hm] at hj
  have hh := mul_lt_mul_of_pos_left hj (div_pos hDim (by norm_num : (0:ℝ)<2))
  have hc : dimension/2*(samples/dimension)=samples/2 := by field_simp;ring
  simpa only [←mul_assoc,hc] using hh

theorem actual_positive_fewer_samples_than_dimensions_prevent_attaining_the_dimension_bound
    [Nonempty T] (X : Matrix T D ℝ) (lambda : ℝ) (hlambda : 0 < lambda)
    (hOrder : Fintype.card T < Fintype.card D)
    (hX : ∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖ ≤ 1) :
    information (Xᵀ*X) lambda < (Fintype.card D:ℝ)/2*
      Real.log (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ))) := by
  have hn : (0:ℝ) < (Fintype.card T:ℝ) := by exact_mod_cast Fintype.card_pos
  exact (actual_every_unit_ball_design_has_the_sample_dimension_information_bound X lambda hlambda hX).trans_lt
    (actual_positive_smaller_sample_cap_is_strictly_below_the_larger_dimension_cap
      (Fintype.card T:ℝ) (Fintype.card D:ℝ) lambda hn (by exact_mod_cast hOrder) hlambda)

theorem actual_design_gram_rank_is_at_most_the_number_of_samples (X : Matrix T D ℝ) :
    (Xᵀ*X).rank ≤ Fintype.card T :=
  (rank_mul_le_left Xᵀ X).trans (rank_le_card_width Xᵀ)

theorem actual_fewer_samples_than_dimensions_force_a_zero_gram_eigenvalue
    (X : Matrix T D ℝ) (hOrder : Fintype.card T < Fintype.card D) :
    ∃ i,(actual_design_gram_is_positive_semidefinite X).isHermitian.eigenvalues i=0 := by
  let hG := actual_design_gram_is_positive_semidefinite X
  have hnu : ¬IsUnit (Xᵀ*X) := by
    intro hu
    have hr := actual_design_gram_rank_is_at_most_the_number_of_samples X
    rw [rank_of_isUnit _ hu] at hr
    omega
  have hd : (Xᵀ*X).det=0 := by
    by_contra hd
    exact hnu ((Xᵀ*X).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd))
  rw [hG.isHermitian.det_eq_prod_eigenvalues] at hd
  obtain ⟨i,_,hi⟩ := Finset.prod_eq_zero_iff.mp hd
  exact ⟨i,hi⟩

theorem actual_zero_observation_design_is_the_boundary_exception_to_strict_nonattainment
    (lambda : ℝ) : information (0 : Matrix D D ℝ) lambda=0 ∧
      (Fintype.card D:ℝ)/2*Real.log (1+(0:ℝ)/(lambda*(Fintype.card D:ℝ)))=0 := by
  simp [information]

end SafeLearning.CompleteModulesGPLinearInformationStrictness
