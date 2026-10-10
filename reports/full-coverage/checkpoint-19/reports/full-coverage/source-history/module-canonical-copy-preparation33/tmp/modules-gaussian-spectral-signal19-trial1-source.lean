import SafeLearning.CompleteModulesGaussianMatrixLaws
import SafeLearning.CompleteModulesGPLinearInformationBounds
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianSpectralSignal
open SafeLearning.CompleteModulesGaussianMatrixLaws
variable {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]

def eigenQ (G : Matrix I I ℝ) (hG : G.PosSemidef) : Matrix I I ℝ :=
  hG.isHermitian.eigenvectorUnitary
def eigenV (G : Matrix I I ℝ) (hG : G.PosSemidef) (i : I) : ℝ≥0 :=
  (hG.isHermitian.eigenvalues i).toNNReal
def signalLaw (G : Matrix I I ℝ) (hG : G.PosSemidef) : Measure (I → ℝ) :=
  (Measure.pi (fun i => gaussianReal 0 (eigenV G hG i))).map (fun z => eigenQ G hG*ᵥ z)

theorem actual_psd_spectral_signal_uses_orthogonal_eigenvectors_and_true_nonnegative_eigenvalues
    (G : Matrix I I ℝ) (hG : G.PosSemidef) :
    eigenQ G hG*(eigenQ G hG)ᵀ=1 ∧ (eigenQ G hG)ᵀ*eigenQ G hG=1 ∧
      (∀ i,(eigenV G hG i:ℝ)=hG.isHermitian.eigenvalues i) ∧
        G=eigenQ G hG*diagonal (fun i => (eigenV G hG i:ℝ))*(eigenQ G hG)ᵀ := by
  have h1 : eigenQ G hG*(eigenQ G hG)ᵀ=1 := by
    simpa only [eigenQ,Unitary.coe_star,Matrix.star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_mul_star_self hG.isHermitian.eigenvectorUnitary
  have h2 : (eigenQ G hG)ᵀ*eigenQ G hG=1 := by
    simpa only [eigenQ,Unitary.coe_star,Matrix.star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hG.isHermitian.eigenvectorUnitary
  have hv : ∀ i,(eigenV G hG i:ℝ)=hG.isHermitian.eigenvalues i := by
    intro i
    exact Real.coe_toNNReal _ (hG.eigenvalues_nonneg i)
  refine ⟨h1,h2,hv,?_⟩
  simp_rw [hv]
  simpa [eigenQ,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.spectral_theorem

instance signalLaw_probability (G : Matrix I I ℝ) (hG : G.PosSemidef) :
    IsProbabilityMeasure (signalLaw G hG) := by
  unfold signalLaw
  infer_instance

theorem actual_psd_spectral_signal_is_a_genuine_finite_gaussian_law_even_for_singular_covariance
    (G : Matrix I I ℝ) (hG : G.PosSemidef) :
    HasGaussianLaw (id : (I → ℝ) → I → ℝ) (signalLaw G hG) := by
  have hg := actual_finite_matrix_transform_preserves_joint_gaussianity
    (Measure.pi (fun i => gaussianReal 0 (eigenV G hG i))) id
    (actual_every_finite_product_of_scalar_gaussians_is_jointly_gaussian
      (fun _ => 0) (eigenV G hG)) (eigenQ G hG)
  haveI : IsGaussian (signalLaw G hG) := hg.isGaussian_map
  exact IsGaussian.hasGaussianLaw_id

theorem actual_arbitrary_centered_finite_gaussian_signal_with_covariance_G_has_the_entire_spectral_signal_law
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Omega → I → ℝ)
    (hF : HasGaussianLaw F P) (G : Matrix I I ℝ) (hG : G.PosSemidef)
    (hm : ∀ i,(∫ o,F o i ∂P)=0)
    (hc : ∀ i j,cov[fun o => F o i,fun o => F o j;P]=G i j) :
    P.map F=signalLaw G hG := by
  let Q := eigenQ G hG
  let v := eigenV G hG
  have hs := actual_psd_spectral_signal_uses_orthogonal_eigenvectors_and_true_nonnegative_eigenvalues G hG
  have hq : Q*Qᵀ=1 := hs.1
  have hqt : Qᵀ*Q=1 := hs.2.1
  have hd : Qᵀ*G*Q=diagonal (fun i => (v i:ℝ)) := by
    rw [hs.2.2.2]
    change Qᵀ*(Q*diagonal (fun i => (v i:ℝ))*Qᵀ)*Q=_
    simp only [← Matrix.mul_assoc]
    rw [hqt,Matrix.one_mul,Matrix.mul_assoc,hqt,Matrix.mul_one]
  have hrot := actual_joint_gaussian_diagonal_covariance_derives_the_entire_product_gaussian_law
    P (fun o => Qᵀ*ᵥ F o)
      (actual_finite_matrix_transform_preserves_joint_gaussianity P F hF Qᵀ)
      (fun _ => 0) v (fun i => by
        rw [actual_finite_matrix_transform_has_the_true_transformed_coordinate_means P F hF Qᵀ i]
        simp only [hm,mul_zero,Finset.sum_const_zero])
      (fun i j => by
        rw [actual_finite_matrix_transform_has_the_true_covariance_matrix P F hF Qᵀ G hc i j,
          Matrix.transpose_transpose,hd]
        simp only [Matrix.diagonal_apply])
  have hback : (P.map (fun o => Qᵀ*ᵥ F o)).map (fun z => Q*ᵥ z)=P.map F := by
    rw [Measure.map_map (by exact (matrixCLM Q).continuous.measurable) (by fun_prop)]
    congr 1
    funext o
    simp only [Function.comp_def,Matrix.mulVec_mulVec,hq,Matrix.one_mulVec]
  rw [hrot] at hback
  exact hback.symm

end SafeLearning.CompleteModulesGaussianSpectralSignal
