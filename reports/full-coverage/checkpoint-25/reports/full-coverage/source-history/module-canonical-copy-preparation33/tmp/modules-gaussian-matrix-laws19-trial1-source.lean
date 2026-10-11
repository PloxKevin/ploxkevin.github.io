import SafeLearning.CompleteModulesGaussianProductInformation
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianMatrixLaws
variable {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]

def matrixCLM (Q : Matrix I I ℝ) : (I → ℝ) →L[ℝ] (I → ℝ) :=
  LinearMap.toContinuousLinearMap Q.mulVecLin

theorem actual_every_finite_product_of_scalar_gaussians_is_jointly_gaussian
    (m : I → ℝ) (v : I → ℝ≥0) :
    HasGaussianLaw (id : (I → ℝ) → I → ℝ) (Measure.pi (fun i => gaussianReal (m i) (v i))) := by
  have hi := iIndepFun_pi (μ:=fun i => gaussianReal (m i) (v i))
    (X:=fun _i => (id:ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  exact hi.hasGaussianLaw (fun i => (measurePreserving_eval _ i).hasLaw.hasGaussianLaw)

theorem actual_finite_matrix_transform_preserves_joint_gaussianity
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Omega → I → ℝ)
    (hF : HasGaussianLaw F P) (Q : Matrix I I ℝ) :
    HasGaussianLaw (fun o => Q*ᵥ F o) P := by
  exact hF.map_fun (matrixCLM Q)

theorem actual_finite_matrix_transform_has_the_true_transformed_coordinate_means
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Omega → I → ℝ)
    (hF : HasGaussianLaw F P) (Q : Matrix I I ℝ) (i : I) :
    (∫ o,(Q*ᵥ F o) i ∂P)=∑ j,Q i j*(∫ o,F o j ∂P) := by
  change (∫ o,∑ j,Q i j*F o j ∂P)=_
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · exact fun j _ => (hF.eval j).integrable.const_mul _

theorem actual_finite_matrix_transform_has_the_true_covariance_matrix
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Omega → I → ℝ)
    (hF : HasGaussianLaw F P) (Q G : Matrix I I ℝ)
    (hG : ∀ i j,cov[fun o => F o i,fun o => F o j;P]=G i j) (i j : I) :
    cov[fun o => (Q*ᵥ F o) i,fun o => (Q*ᵥ F o) j;P]=(Q*G*Qᵀ) i j := by
  change cov[fun o => ∑ k,Q i k*F o k,fun o => ∑ l,Q j l*F o l;P]=_
  rw [covariance_fun_sum_fun_sum (fun k => (hF.eval k).memLp_two.const_mul _)
    (fun l => (hF.eval l).memLp_two.const_mul _)]
  simp_rw [covariance_const_mul_left,covariance_const_mul_right,hG]
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem actual_joint_gaussian_diagonal_covariance_derives_the_entire_product_gaussian_law
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Omega → I → ℝ)
    (hF : HasGaussianLaw F P) (m : I → ℝ) (v : I → ℝ≥0)
    (hm : ∀ i,(∫ o,F o i ∂P)=m i)
    (hv : ∀ i j,cov[fun o => F o i,fun o => F o j;P]=if i=j then (v i:ℝ) else 0) :
    P.map F=Measure.pi (fun i => gaussianReal (m i) (v i)) := by
  have hi := hF.iIndepFun_of_covariance_eq_zero (fun i j hij => by rw [hv];simp [hij])
  have h := hi.map_fun_eq_pi_map (fun i => (hF.eval i).aemeasurable)
  change P.map F=Measure.pi (fun i => P.map (fun o => F o i)) at h
  rw [h]
  congr 1
  funext i
  rw [(hF.eval i).map_eq_gaussianReal,hm i,
    ← covariance_self (hF.eval i).aemeasurable,hv i i]
  simp

theorem actual_independent_scalar_gaussian_coordinates_have_their_true_means_and_diagonal_covariance
    (m : I → ℝ) (v : I → ℝ≥0) :
    (∀ i,(∫ z : I → ℝ,z i ∂Measure.pi (fun j => gaussianReal (m j) (v j)))=m i) ∧
      (∀ i j,cov[fun z : I → ℝ => z i,fun z : I → ℝ => z j;
        Measure.pi (fun k => gaussianReal (m k) (v k))]=if i=j then (v i:ℝ) else 0) := by
  have hg := actual_every_finite_product_of_scalar_gaussians_is_jointly_gaussian m v
  have hl (i : I) := (measurePreserving_eval (fun j => gaussianReal (m j) (v j)) i).hasLaw
  constructor
  · intro i
    rw [integral_eval,integral_id_gaussianReal]
  · intro i j
    by_cases hij : i=j
    · subst j
      rw [covariance_self (hl i).aemeasurable,(hl i).variance_eq,variance_id_gaussianReal]
      simp
    · have hi := iIndepFun_pi (μ:=fun i => gaussianReal (m i) (v i))
        (X:=fun _i => (id:ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
      rw [(hi.indepFun hij).covariance_eq_zero (hg.eval i).memLp_two (hg.eval j).memLp_two]
      simp [hij]

theorem actual_orthogonal_transform_preserves_the_entire_isotropic_gaussian_noise_law
    (Q : Matrix I I ℝ) (hQ : Q*Qᵀ=1) (lambda : ℝ≥0) :
    (Measure.pi (fun _ : I => gaussianReal 0 lambda)).map (fun z => Q*ᵥ z)=
      Measure.pi (fun _ : I => gaussianReal 0 lambda) := by
  let P := Measure.pi (fun _ : I => gaussianReal 0 lambda)
  have hg := actual_every_finite_product_of_scalar_gaussians_is_jointly_gaussian
    (fun _ : I => 0) (fun _ : I => lambda)
  have hs := actual_independent_scalar_gaussian_coordinates_have_their_true_means_and_diagonal_covariance
    (fun _ : I => 0) (fun _ : I => lambda)
  apply actual_joint_gaussian_diagonal_covariance_derives_the_entire_product_gaussian_law
    P (fun z => Q*ᵥ z) (actual_finite_matrix_transform_preserves_joint_gaussianity P id hg Q)
    (fun _ : I => 0) (fun _ : I => lambda)
  · intro i
    rw [actual_finite_matrix_transform_has_the_true_transformed_coordinate_means P id hg Q i]
    simp only [id_eq,hs.1,mul_zero,Finset.sum_const_zero]
  · intro i j
    have hc : ∀ k l,cov[fun z => id z k,fun z => id z l;P]=
        ((lambda:ℝ) • (1:Matrix I I ℝ)) k l := by
      intro k l
      simpa only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]
        using hs.2 k l
    rw [actual_finite_matrix_transform_has_the_true_covariance_matrix P id hg Q _ hc i j]
    rw [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hQ]
    simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]

end SafeLearning.CompleteModulesGaussianMatrixLaws
