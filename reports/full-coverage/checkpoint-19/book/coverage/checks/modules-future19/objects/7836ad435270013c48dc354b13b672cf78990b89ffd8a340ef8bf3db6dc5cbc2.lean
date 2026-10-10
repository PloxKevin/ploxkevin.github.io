import SafeLearning.CompleteModulesGaussianChannelInformation
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianProductInformation
open SafeLearning.CompleteModulesGaussianChannelInformation

theorem actual_official_KL_is_invariant_under_any_measurable_equivalence
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) [IsFiniteMeasure mu] [IsFiniteMeasure nu] (e : A ≃ᵐ B) :
    klDiv (mu.map e) (nu.map e)=klDiv mu nu := by
  apply le_antisymm (klDiv_map_le mu nu e.measurable)
  have h := klDiv_map_le (mu.map e) (nu.map e) e.symm.measurable
  simpa only [MeasurableEquiv.map_map_symm] using h

theorem actual_official_KL_of_product_probability_laws_is_additive
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) (rho eta : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure rho] [IsProbabilityMeasure eta] :
    klDiv (mu.prod rho) (nu.prod eta)=klDiv mu nu+klDiv rho eta := by
  have h := klDiv_compProd_eq_add mu nu (Kernel.const A rho) (Kernel.const A eta)
  simp only [Measure.compProd_const] at h
  rw [h]
  congr 1
  have hs := actual_official_KL_is_invariant_under_any_measurable_equivalence
    (mu.prod rho) (mu.prod eta) (MeasurableEquiv.prodComm A B)
  simp only [MeasurableEquiv.coe_prodComm,Measure.prod_swap] at hs
  rw [← hs]
  simpa only [Measure.compProd_const] using
    klDiv_compProd_left rho eta (Kernel.const B mu)

theorem actual_official_KL_of_nat_finite_product_probability_laws_is_the_sum
    {A : Type*} [MeasurableSpace A] (n : ℕ)
    (mu nu : Fin n → Measure A)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)] :
    klDiv (Measure.pi mu) (Measure.pi nu)=∑ i,klDiv (mu i) (nu i) := by
  induction n with
  | zero => simp [Measure.pi_of_empty]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0
    have hmu := (measurePreserving_piFinSuccAbove mu 0).map_eq
    have hnu := (measurePreserving_piFinSuccAbove nu 0).map_eq
    have he := actual_official_KL_is_invariant_under_any_measurable_equivalence
      (Measure.pi mu) (Measure.pi nu) e
    change klDiv ((Measure.pi mu).map (MeasurableEquiv.piFinSuccAbove _ 0))
      ((Measure.pi nu).map (MeasurableEquiv.piFinSuccAbove _ 0))=_ at he
    rw [hmu,hnu,actual_official_KL_of_product_probability_laws_is_additive] at he
    rw [← he,ih]
    exact (Fin.sum_univ_succAbove (fun i => klDiv (mu i) (nu i)) 0).symm

theorem actual_official_KL_of_every_finite_product_probability_law_is_the_sum
    {I A : Type*} [Fintype I] [MeasurableSpace A]
    (mu nu : I → Measure A)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)] :
    klDiv (Measure.pi mu) (Measure.pi nu)=∑ i,klDiv (mu i) (nu i) := by
  let e := (Fintype.equivFin I).symm
  have hm := (measurePreserving_piCongrLeft (α:=fun _ : I => A) mu e).map_eq
  have hn := (measurePreserving_piCongrLeft (α:=fun _ : I => A) nu e).map_eq
  have h := actual_official_KL_is_invariant_under_any_measurable_equivalence
    (Measure.pi (fun i => mu (e i))) (Measure.pi (fun i => nu (e i)))
    (MeasurableEquiv.piCongrLeft (fun _ : I => A) e)
  rw [hm,hn,actual_official_KL_of_nat_finite_product_probability_laws_is_the_sum] at h
  exact h.trans (e.sum_comp (fun i => klDiv (mu i) (nu i)))

variable {I : Type*} [Fintype I]

def vectorJoint (m : I → ℝ) (v : I → ℝ≥0) (lambda : ℝ≥0) :
    Measure ((I → ℝ) × (I → ℝ)) :=
  ((Measure.pi (fun i => gaussianReal (m i) (v i))).prod
    (Measure.pi (fun _ : I => gaussianReal 0 lambda))).map
      (fun p => (p.1,fun i => p.2 i+p.1 i))

instance vectorJoint_probability (m : I → ℝ) (v : I → ℝ≥0) (lambda : ℝ≥0) :
    IsProbabilityMeasure (vectorJoint m v lambda) := by
  unfold vectorJoint
  infer_instance

theorem actual_independent_finite_gaussian_channel_joint_is_the_product_of_the_true_scalar_channel_joints
    (m : I → ℝ) (v : I → ℝ≥0) (lambda : ℝ≥0) :
    vectorJoint m v lambda=(Measure.pi (fun i => actualJoint (gaussianReal (m i) (v i)) lambda)).map
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I) := by
  have hb := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ I
    (fun i => gaussianReal (m i) (v i)) (fun _ => gaussianReal 0 lambda)).map_eq
  have hp := Measure.pi_map_pi
    (μ:=fun i => (gaussianReal (m i) (v i)).prod (gaussianReal 0 lambda))
    (f:=fun _i => fun p : ℝ × ℝ => (p.1,p.2+p.1)) (fun _ => by fun_prop)
  change (Measure.pi (fun i => (gaussianReal (m i) (v i)).prod (gaussianReal 0 lambda))).map
    (fun x i => ((x i).1,(x i).2+(x i).1))=
      Measure.pi (fun i => actualJoint (gaussianReal (m i) (v i)) lambda) at hp
  unfold vectorJoint
  rw [← hb,← hp,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem actual_independent_finite_gaussian_channel_has_the_true_input_and_output_marginals
    (m : I → ℝ) (v : I → ℝ≥0) (lambda : ℝ≥0) :
    (vectorJoint m v lambda).map Prod.fst=Measure.pi (fun i => gaussianReal (m i) (v i)) ∧
      (vectorJoint m v lambda).map Prod.snd=Measure.pi (fun i => gaussianReal (m i) (v i+lambda)) := by
  rw [actual_independent_finite_gaussian_channel_joint_is_the_product_of_the_true_scalar_channel_joints]
  constructor
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    change (Measure.pi (fun i => actualJoint (gaussianReal (m i) (v i)) lambda)).map
      (fun p i => (p i).1)=_
    rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
    simp only [(actual_channel_joint_has_exact_input_and_noise_marginals _ lambda).1]
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    change (Measure.pi (fun i => actualJoint (gaussianReal (m i) (v i)) lambda)).map
      (fun p i => (p i).2)=_
    rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
    simp only [actual_scalar_gaussian_channel_has_the_true_gaussian_output_law]

theorem actual_independent_finite_gaussian_channel_official_mutual_information_is_the_sum_of_scalar_information
    (m : I → ℝ) (v : I → ℝ≥0) (lambda : ℝ≥0) (hlambda : lambda ≠ 0) :
    klDiv (vectorJoint m v lambda)
      ((Measure.pi (fun i => gaussianReal (m i) (v i))).prod
        (Measure.pi (fun i => gaussianReal (m i) (v i+lambda))))=
      ENNReal.ofReal ((1/2:ℝ)*(∑ i,Real.log (1+(v i:ℝ)/(lambda:ℝ)))) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I
  have hd := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ I
    (fun i => gaussianReal (m i) (v i)) (fun i => gaussianReal (m i) (v i+lambda))).map_eq
  have h := actual_official_KL_is_invariant_under_any_measurable_equivalence
    (Measure.pi (fun i => actualJoint (gaussianReal (m i) (v i)) lambda))
    (Measure.pi (fun i => (gaussianReal (m i) (v i)).prod (gaussianReal (m i) (v i+lambda)))) e
  rw [← actual_independent_finite_gaussian_channel_joint_is_the_product_of_the_true_scalar_channel_joints,
    hd,actual_official_KL_of_every_finite_product_probability_law_is_the_sum] at h
  rw [h]
  simp_rw [actual_scalar_gaussian_channel_mutual_information_is_the_finite_official_KL_value
    _ _ lambda hlambda]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    exact (Finset.mul_sum _ _ _).symm
  · intro i _
    apply mul_nonneg (by norm_num)
    exact Real.log_nonneg (le_add_of_nonneg_right (div_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)))

end SafeLearning.CompleteModulesGaussianProductInformation
