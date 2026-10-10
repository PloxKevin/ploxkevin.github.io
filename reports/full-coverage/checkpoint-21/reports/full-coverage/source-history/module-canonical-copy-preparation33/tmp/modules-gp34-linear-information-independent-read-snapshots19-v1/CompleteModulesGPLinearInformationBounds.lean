import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPLinearInformationBounds
variable {D T : Type*} [Fintype D] [DecidableEq D] [Fintype T] [DecidableEq T]

def information (G : Matrix D D ℝ) (lambda : ℝ) : ℝ :=
  (1/2)*Real.log (1+lambda⁻¹ • G).det

theorem actual_weinstein_aronszajn_identity_for_the_linear_design
    (X : Matrix T D ℝ) (lambda : ℝ) :
    (1+lambda⁻¹ • (X*Xᵀ)).det=(1+lambda⁻¹ • (Xᵀ*X)).det := by
  simpa only [Matrix.smul_mul,Matrix.mul_smul] using det_one_add_mul_comm (lambda⁻¹ • X) Xᵀ

theorem actual_design_gram_is_positive_semidefinite (X : Matrix T D ℝ) :
    (Xᵀ*X).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self X

theorem actual_design_gram_trace_is_the_sum_of_actual_euclidean_squared_input_norms
    (X : Matrix T D ℝ) :
    (Xᵀ*X).trace=∑ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖^2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs]
  simp_rw [sq_abs]
  simp only [trace,mul_apply,diag,transpose_apply,pow_two]
  rw [Finset.sum_comm]

theorem actual_unit_ball_design_has_total_gram_trace_at_most_its_sample_count
    (X : Matrix T D ℝ)
    (hX : ∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖ ≤ 1) :
    (Xᵀ*X).trace ≤ (Fintype.card T:ℝ) := by
  rw [actual_design_gram_trace_is_the_sum_of_actual_euclidean_squared_input_norms]
  calc
    _  ≤  ∑ _t : T,(1:ℝ) := Finset.sum_le_sum (fun t _ => by
      have hp := hX t
      nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)])
    _ = _ := by simp

theorem actual_nonnegative_psd_spectrum_sums_to_the_true_trace
    (G : Matrix D D ℝ) (hG : G.PosSemidef) :
    (∀ i,0 ≤ hG.isHermitian.eigenvalues i) ∧
      (∑ i,hG.isHermitian.eigenvalues i)=G.trace :=
  ⟨hG.eigenvalues_nonneg,hG.isHermitian.trace_eq_sum_eigenvalues.symm⟩

theorem actual_orthogonal_spectral_ridge_determinant_is_the_product_of_shifted_eigenvalues
    (Q : Matrix D D ℝ) (mu : D → ℝ) (lambda : ℝ)
    (hQ : Q*Qᵀ=1) :
    (1+lambda⁻¹ • (Q*diagonal mu*Qᵀ)).det=∏ i,(1+mu i/lambda) := by
  have hd : diagonal (fun i => 1+mu i/lambda)=1+lambda⁻¹ • diagonal mu := by
    ext i j
    by_cases hij : i=j
    · subst j;simp [Matrix.one_apply,diagonal_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
    · simp [Matrix.one_apply,diagonal_apply,hij]
  have he : 1+lambda⁻¹ • (Q*diagonal mu*Qᵀ)=Q*diagonal (fun i => 1+mu i/lambda)*Qᵀ := by
    rw [hd,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,hQ,Matrix.mul_smul,Matrix.smul_mul]
  rw [he,det_mul,det_mul,det_diagonal]
  have hu : Q.det*Qᵀ.det=1 := by rw [←det_mul,hQ,det_one]
  calc
    Q.det*(∏ i : D,(1+mu i/lambda))*Qᵀ.det=(Q.det*Qᵀ.det)*(∏ i : D,(1+mu i/lambda)) := by ring
    _ = _ := by rw [hu,one_mul]

theorem actual_positive_semidefinite_logdet_is_the_sum_of_its_true_spectral_logarithms
    (G : Matrix D D ℝ) (hG : G.PosSemidef) (lambda : ℝ) (hlambda : 0  <  lambda) :
    Real.log (1+lambda⁻¹ • G).det=∑ i,Real.log (1+hG.isHermitian.eigenvalues i/lambda) := by
  let Q : Matrix D D ℝ := hG.isHermitian.eigenvectorUnitary
  have hQ : Q*Qᵀ=1 := by
    simpa only [Q,Unitary.coe_star,Matrix.star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_mul_star_self hG.isHermitian.eigenvectorUnitary
  have hs : G=Q*diagonal hG.isHermitian.eigenvalues*Qᵀ := by
    simpa [Q,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.spectral_theorem
  conv_lhs => rw [hs,actual_orthogonal_spectral_ridge_determinant_is_the_product_of_shifted_eigenvalues Q _ lambda hQ]
  exact Real.log_prod (fun i _ => (show 0 < 1+hG.isHermitian.eigenvalues i/lambda by
    have hp := hG.eigenvalues_nonneg i
    positivity).ne')

theorem actual_log_jensen_bound_for_every_nonnegative_spectrum
    [Nonempty D] (mu : D → ℝ) (lambda : ℝ) (hlambda : 0  <  lambda)
    (hmu : ∀ i,0 ≤ mu i) :
    (∑ i,Real.log (1+mu i/lambda)) ≤ 
      (Fintype.card D:ℝ)*Real.log (1+(∑ i,mu i)/(lambda*(Fintype.card D:ℝ))) := by
  have hn : (0:ℝ) < (Fintype.card D:ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : (∑ _i : D,1/(Fintype.card D:ℝ))=1 := by simp [hn.ne']
  have hm : (∑ i,(1/(Fintype.card D:ℝ))*(1+mu i/lambda))=
      1+(∑ i,mu i)/(lambda*(Fintype.card D:ℝ)) := by
    simp_rw [mul_add,Finset.sum_add_distrib,mul_one]
    rw [hw]
    rw [←Finset.mul_sum]
    congr 1
    rw [←Finset.sum_div]
    field_simp
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t:=Finset.univ) (w:=fun _ : D => 1/(Fintype.card D:ℝ))
    (p:=fun i => 1+mu i/lambda) (fun _ _ => by positivity) hw
    (fun i _ => by exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hmu i) hlambda.le))
  simp only [smul_eq_mul] at hj
  rw [hm,←Finset.mul_sum] at hj
  have he := mul_le_mul_of_nonneg_left hj hn.le
  simpa only [←mul_assoc,mul_one_div_cancel hn.ne',one_mul] using he

theorem actual_linear_design_information_has_the_dimension_trace_bound
    [Nonempty D] (X : Matrix T D ℝ) (lambda : ℝ) (hlambda : 0  <  lambda)
    (hX : ∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖ ≤ 1) :
    information (Xᵀ*X) lambda ≤ 
      (Fintype.card D:ℝ)/2*Real.log (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ))) := by
  let hG := actual_design_gram_is_positive_semidefinite X
  have he := actual_nonnegative_psd_spectrum_sums_to_the_true_trace (Xᵀ*X) hG
  have hj := actual_log_jensen_bound_for_every_nonnegative_spectrum hG.isHermitian.eigenvalues lambda hlambda he.1
  rw [he.2] at hj
  have ht := actual_unit_ball_design_has_total_gram_trace_at_most_its_sample_count X hX
  have hn : (0:ℝ) < (Fintype.card D:ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : 0 < lambda*(Fintype.card D:ℝ) := mul_pos hlambda hn
  have hl := Real.log_le_log (show 0 < 1+(Xᵀ*X).trace/(lambda*(Fintype.card D:ℝ)) by
      have ht0 := Matrix.PosSemidef.trace_nonneg hG;positivity)
    (add_le_add le_rfl ((div_le_div_iff_of_pos_right hd).mpr ht))
  unfold information
  rw [actual_positive_semidefinite_logdet_is_the_sum_of_its_true_spectral_logarithms _ hG lambda hlambda]
  have hh := hj.trans (mul_le_mul_of_nonneg_left hl hn.le)
  nlinarith

end SafeLearning.CompleteModulesGPLinearInformationBounds
