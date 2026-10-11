import SafeLearning.CompleteModulesGaussianSpectralSignal
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianPSDInformation
open SafeLearning.CompleteModulesGaussianChannelInformation
open SafeLearning.CompleteModulesGaussianProductInformation
open SafeLearning.CompleteModulesGaussianMatrixLaws
open SafeLearning.CompleteModulesGaussianSpectralSignal
open SafeLearning.CompleteModulesGPLinearInformationBounds
variable {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]

def orthogonalEquiv (Q : Matrix I I ℝ) (hQ : Q*Qᵀ=1) (hQT : Qᵀ*Q=1) :
    (I → ℝ) ≃ᵐ (I → ℝ) where
  toEquiv :=
    { toFun := fun z => Q*ᵥ z
      invFun := fun z => Qᵀ*ᵥ z
      left_inv := fun z => by simp only [Matrix.mulVec_mulVec,hQT,Matrix.one_mulVec]
      right_inv := fun z => by simp only [Matrix.mulVec_mulVec,hQ,Matrix.one_mulVec] }
  measurable_toFun := (matrixCLM Q).continuous.measurable
  measurable_invFun := (matrixCLM Qᵀ).continuous.measurable

def channelJoint (nu : Measure (I → ℝ)) (lambda : ℝ≥0) :
    Measure ((I → ℝ) × (I → ℝ)) :=
  (nu.prod (Measure.pi (fun _ : I => gaussianReal 0 lambda))).map
    (fun p => (p.1,p.2+p.1))
instance channelJoint_probability (nu : Measure (I → ℝ)) [IsProbabilityMeasure nu] (lambda : ℝ≥0) :
    IsProbabilityMeasure (channelJoint nu lambda) := by unfold channelJoint;infer_instance

theorem actual_official_mutual_information_KL_is_symmetric_under_swapping_the_joint_and_marginals
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (J : Measure (A × B)) [IsProbabilityMeasure J] :
    klDiv (J.map Prod.swap) ((J.map Prod.snd).prod (J.map Prod.fst))=
      klDiv J ((J.map Prod.fst).prod (J.map Prod.snd)) := by
  have h := actual_official_KL_is_invariant_under_any_measurable_equivalence
    J ((J.map Prod.fst).prod (J.map Prod.snd)) (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A)
  change klDiv (J.map Prod.swap)
    (((J.map Prod.fst).prod (J.map Prod.snd)).map Prod.swap)=_ at h
  rw [Measure.prod_swap] at h
  exact h

theorem actual_vector_channel_joint_has_the_true_input_marginal
    (nu : Measure (I → ℝ)) [IsProbabilityMeasure nu] (lambda : ℝ≥0) :
    (channelJoint nu lambda).map Prod.fst=nu := by
  unfold channelJoint
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def,Measure.map_fst_prod,measure_univ,one_smul]

theorem actual_orthogonal_rotation_of_the_finite_scalar_channel_joint_is_the_true_rotated_signal_channel_joint
    (Q : Matrix I I ℝ) (hQ : Q*Qᵀ=1) (hQT : Qᵀ*Q=1)
    (v : I → ℝ≥0) (lambda : ℝ≥0) :
    (vectorJoint (fun _ => 0) v lambda).map
        ((orthogonalEquiv Q hQ hQT).prodCongr (orthogonalEquiv Q hQ hQT))=
      channelJoint ((Measure.pi (fun i => gaussianReal 0 (v i))).map (fun z => Q*ᵥ z)) lambda := by
  let S := Measure.pi (fun i => gaussianReal 0 (v i))
  let N := Measure.pi (fun _ : I => gaussianReal 0 lambda)
  let e := orthogonalEquiv Q hQ hQT
  have hn : N.map e=N := actual_orthogonal_transform_preserves_the_entire_isotropic_gaussian_noise_law Q hQ lambda
  have hp := Measure.map_prod_map S N e.measurable e.measurable
  calc
    _=(S.prod N).map (fun p => (Q*ᵥ p.1,Q*ᵥ p.2+Q*ᵥ p.1)) := by
      unfold vectorJoint
      rw [Measure.map_map (e.prodCongr e).measurable (by fun_prop)]
      congr 1
      funext p
      simp only [Function.comp_def,MeasurableEquiv.prodCongr,orthogonalEquiv,
        Equiv.prodCongr_apply,Matrix.mulVec_add]
    _=((S.map e).prod (N.map e)).map (fun p => (p.1,p.2+p.1)) := by
      rw [hp,Measure.map_map (by fun_prop) (e.measurable.prodMap e.measurable)]
      rfl
    _=_ := by rw [hn];rfl

theorem actual_rotated_signal_channel_has_the_true_rotated_gaussian_output_law
    (Q : Matrix I I ℝ) (hQ : Q*Qᵀ=1) (hQT : Qᵀ*Q=1)
    (v : I → ℝ≥0) (lambda : ℝ≥0) :
    (channelJoint ((Measure.pi (fun i => gaussianReal 0 (v i))).map (fun z => Q*ᵥ z)) lambda).map Prod.snd=
      (Measure.pi (fun i => gaussianReal 0 (v i+lambda))).map (fun z => Q*ᵥ z) := by
  let e := orthogonalEquiv Q hQ hQT
  rw [← actual_orthogonal_rotation_of_the_finite_scalar_channel_joint_is_the_true_rotated_signal_channel_joint
    Q hQ hQT v lambda]
  have hm : ((vectorJoint (fun _ => 0) v lambda).map (e.prodCongr e)).map Prod.snd=
      ((vectorJoint (fun _ => 0) v lambda).map Prod.snd).map e := by
    rw [Measure.map_map (by fun_prop) (e.prodCongr e).measurable,
      Measure.map_map e.measurable (by fun_prop)]
    rfl
  rw [hm,(actual_independent_finite_gaussian_channel_has_the_true_input_and_output_marginals
    (fun _ => 0) v lambda).2]
  rfl

theorem actual_rotated_signal_channel_official_mutual_information_is_the_true_spectral_sum
    (Q : Matrix I I ℝ) (hQ : Q*Qᵀ=1) (hQT : Qᵀ*Q=1)
    (v : I → ℝ≥0) (lambda : ℝ≥0) (hlambda : lambda ≠ 0) :
    klDiv (channelJoint ((Measure.pi (fun i => gaussianReal 0 (v i))).map (fun z => Q*ᵥ z)) lambda)
      (((Measure.pi (fun i => gaussianReal 0 (v i))).map (fun z => Q*ᵥ z)).prod
        ((Measure.pi (fun i => gaussianReal 0 (v i+lambda))).map (fun z => Q*ᵥ z)))=
      ENNReal.ofReal ((1/2:ℝ)*(∑ i,Real.log (1+(v i:ℝ)/(lambda:ℝ)))) := by
  let e := orthogonalEquiv Q hQ hQT
  have h := actual_official_KL_is_invariant_under_any_measurable_equivalence
    (vectorJoint (fun _ => 0) v lambda)
    ((Measure.pi (fun i => gaussianReal 0 (v i))).prod
      (Measure.pi (fun i => gaussianReal 0 (v i+lambda)))) (e.prodCongr e)
  rw [actual_orthogonal_rotation_of_the_finite_scalar_channel_joint_is_the_true_rotated_signal_channel_joint] at h
  have hp := Measure.map_prod_map (Measure.pi (fun i => gaussianReal 0 (v i)))
    (Measure.pi (fun i => gaussianReal 0 (v i+lambda))) e.measurable e.measurable
  change _=((Measure.pi (fun i => gaussianReal 0 (v i))).prod
    (Measure.pi (fun i => gaussianReal 0 (v i+lambda)))).map (e.prodCongr e) at hp
  rw [← hp] at h
  exact h.trans (actual_independent_finite_gaussian_channel_official_mutual_information_is_the_sum_of_scalar_information
    (fun _ => 0) v lambda hlambda)

theorem actual_every_psd_finite_gaussian_channel_official_mutual_information_is_half_logdet_including_singular_signals
    (G : Matrix I I ℝ) (hG : G.PosSemidef) (lambda : ℝ≥0) (hlambda : lambda ≠ 0) :
    klDiv (channelJoint (signalLaw G hG) lambda)
      (((channelJoint (signalLaw G hG) lambda).map Prod.fst).prod
        ((channelJoint (signalLaw G hG) lambda).map Prod.snd))=
      ENNReal.ofReal (information G (lambda:ℝ)) := by
  have hs := actual_psd_spectral_signal_uses_orthogonal_eigenvectors_and_true_nonnegative_eigenvalues G hG
  rw [actual_vector_channel_joint_has_the_true_input_marginal]
  unfold signalLaw
  rw [actual_rotated_signal_channel_has_the_true_rotated_gaussian_output_law
    (eigenQ G hG) hs.1 hs.2.1 (eigenV G hG) lambda]
  rw [actual_rotated_signal_channel_official_mutual_information_is_the_true_spectral_sum
    (eigenQ G hG) hs.1 hs.2.1 (eigenV G hG) lambda hlambda]
  unfold information
  rw [actual_positive_semidefinite_logdet_is_the_sum_of_its_true_spectral_logarithms
    G hG (lambda:ℝ) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hlambda))]
  simp_rw [hs.2.2.1]

theorem actual_independent_gaussian_input_and_isotropic_noise_derive_the_true_channel_joint
    (P : Measure Omega) [IsProbabilityMeasure P] (F E : Omega → I → ℝ)
    (hF : AEMeasurable F P) (hE : AEMeasurable E P) (hi : IndepFun F E P)
    (lambda : ℝ≥0) (hnoise : P.map E=Measure.pi (fun _ : I => gaussianReal 0 lambda)) :
    P.map (fun o => (F o,E o+F o))=channelJoint (P.map F) lambda := by
  have hp := hi.map_prod_eq_prod_map_map hF hE
  unfold channelJoint
  rw [← hnoise,← hp,AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hF.prodMk hE)]
  rfl

theorem actual_arbitrary_centered_finite_gaussian_signal_and_independent_isotropic_noise_have_the_official_half_logdet_mutual_information
    (P : Measure Omega) [IsProbabilityMeasure P] (F E : Omega → I → ℝ)
    (hF : HasGaussianLaw F P) (hE : AEMeasurable E P) (hi : IndepFun F E P)
    (G : Matrix I I ℝ) (hG : G.PosSemidef)
    (hm : ∀ i,(∫ o,F o i ∂P)=0)
    (hc : ∀ i j,cov[fun o => F o i,fun o => F o j;P]=G i j)
    (lambda : ℝ≥0) (hlambda : lambda ≠ 0)
    (hnoise : P.map E=Measure.pi (fun _ : I => gaussianReal 0 lambda)) :
    klDiv (P.map (fun o => (F o,E o+F o)))
      ((P.map F).prod (P.map (fun o => E o+F o)))=
        ENNReal.ofReal (information G (lambda:ℝ)) := by
  have hj := actual_independent_gaussian_input_and_isotropic_noise_derive_the_true_channel_joint
    P F E hF.aemeasurable hE hi lambda hnoise
  have hf := actual_arbitrary_centered_finite_gaussian_signal_with_covariance_G_has_the_entire_spectral_signal_law
    P F hF G hG hm hc
  have hfst : (P.map (fun o => (F o,E o+F o))).map Prod.fst=P.map F := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop)
      (hF.aemeasurable.prodMk (hE.add hF.aemeasurable))]
    rfl
  have hsnd : (P.map (fun o => (F o,E o+F o))).map Prod.snd=P.map (fun o => E o+F o) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop)
      (hF.aemeasurable.prodMk (hE.add hF.aemeasurable))]
    rfl
  rw [← hfst,← hsnd,hj,hf]
  exact actual_every_psd_finite_gaussian_channel_official_mutual_information_is_half_logdet_including_singular_signals
    G hG lambda hlambda

end SafeLearning.CompleteModulesGaussianPSDInformation
