import SafeLearning.CompleteModulesGaussianRegressionFinite

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianObservationModel
open CompleteModulesGaussianRegressionFinite
variable {I Omega : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Omega]
variable (P : Measure Omega) [IsProbabilityMeasure P]
variable (F E : Omega → I → ℝ) (Z : Omega → ℝ) (lambda : ℝ≥0)

def observation (o : Omega) : I → ℝ := F o+E o

theorem actual_independent_centered_gaussian_noise_has_the_true_diagonal_covariance
    (hnoise : ∀ i,HasLaw (fun o => E o i) (gaussianReal 0 lambda) P)
    (hindependent : iIndepFun (fun i o => E o i) P) (i j : I) :
    cov[fun o => E o i,fun o => E o j;P]=if i=j then (lambda : ℝ) else 0 := by
  by_cases hij : i=j
  · subst j
    rw [covariance_self (hnoise i).aemeasurable,(hnoise i).variance_eq,variance_id_gaussianReal]
    simp
  · rw [(hindependent.indepFun hij).covariance_eq_zero
      (hnoise i).hasGaussianLaw.memLp_two (hnoise j).hasGaussianLaw.memLp_two]
    simp [hij]

theorem actual_prior_plus_independent_gaussian_noise_and_query_are_jointly_gaussian
    (hprior : HasGaussianLaw (fun o => (F o,Z o)) P)
    (hnoise : ∀ i,HasLaw (fun o => E o i) (gaussianReal 0 lambda) P)
    (hnoises : iIndepFun (fun i o => E o i) P)
    (hindependent : IndepFun (fun o => (F o,Z o)) E P) :
    HasGaussianLaw (fun o => (observation F E o,Z o)) P := by
  have he : HasGaussianLaw E P := hnoises.hasGaussianLaw (fun i => (hnoise i).hasGaussianLaw)
  have hfull := hindependent.hasGaussianLaw hprior he
  let prior : (((I → ℝ) × ℝ) × (I → ℝ)) →L[ℝ] ((I → ℝ) × ℝ) :=
    ContinuousLinearMap.fst ℝ ((I → ℝ) × ℝ) (I → ℝ)
  let noise : (((I → ℝ) × ℝ) × (I → ℝ)) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.snd ℝ ((I → ℝ) × ℝ) (I → ℝ)
  let combine :=
    (((ContinuousLinearMap.fst ℝ (I → ℝ) ℝ).comp prior)+noise).prod
      ((ContinuousLinearMap.snd ℝ (I → ℝ) ℝ).comp prior)
  convert hfull.map_fun combine using 1 <;> rfl

theorem actual_source_observation_covariance_is_the_prior_gram_plus_noise_diagonal
    (hprior : HasGaussianLaw (fun o => (F o,Z o)) P)
    (hnoise : ∀ i,HasLaw (fun o => E o i) (gaussianReal 0 lambda) P)
    (hnoises : iIndepFun (fun i o => E o i) P)
    (hindependent : IndepFun (fun o => (F o,Z o)) E P) :
    observationCovariance P (observation F E)=
      observationCovariance P F+(lambda : ℝ) • (1 : Matrix I I ℝ) := by
  ext i j
  have hf : ∀ i,MemLp (fun o => F o i) 2 P := fun i => (hprior.fst.eval i).memLp_two
  have he : ∀ i,MemLp (fun o => E o i) 2 P := fun i => (hnoise i).hasGaussianLaw.memLp_two
  have hc (i j : I) : cov[fun o => F o i,fun o => E o j;P]=0 := by
    have h := hindependent.comp ((measurable_pi_apply i).comp measurable_fst) (measurable_pi_apply j)
    exact h.covariance_eq_zero (hf i) (he j)
  change cov[(fun o => F o i)+(fun o => E o i),(fun o => F o j)+(fun o => E o j);P]=_
  rw [covariance_add_left (hf i) (he i) ((hf j).add (he j)),
    covariance_add_right (hf i) (hf j) (he j),covariance_add_right (he i) (hf j) (he j),
    hc i j,covariance_comm (fun o => E o i) (fun o => F o j),hc j i,
    actual_independent_centered_gaussian_noise_has_the_true_diagonal_covariance P E lambda hnoise hnoises]
  simp [observationCovariance,Matrix.one_apply]

theorem actual_source_observation_query_cross_covariance_is_the_true_prior_query_vector
    (hprior : HasGaussianLaw (fun o => (F o,Z o)) P)
    (hnoise : ∀ i,HasLaw (fun o => E o i) (gaussianReal 0 lambda) P)
    (hindependent : IndepFun (fun o => (F o,Z o)) E P) :
    crossCovariance P (observation F E) Z=crossCovariance P F Z := by
  ext i
  have hf := (hprior.fst.eval i).memLp_two
  have he := (hnoise i).hasGaussianLaw.memLp_two
  have hz := hprior.snd.memLp_two
  have hc : cov[fun o => E o i,Z;P]=0 := by
    have h := hindependent.comp measurable_snd (measurable_pi_apply i)
    exact h.symm.covariance_eq_zero he hz
  change cov[(fun o => F o i)+(fun o => E o i),Z;P]=_
  rw [covariance_add_left hf he hz,hc,add_zero]
  rfl

theorem actual_centered_prior_and_centered_noise_give_the_true_zero_observation_mean
    (hprior : HasGaussianLaw (fun o => (F o,Z o)) P)
    (hnoise : ∀ i,HasLaw (fun o => E o i) (gaussianReal 0 lambda) P)
    (hF : ∀ i,(∫ o,F o i ∂P)=0) (i : I) :
    (∫ o,observation F E o i ∂P)=0 := by
  change (∫ o,F o i+E o i ∂P)=0
  rw [integral_add (hprior.fst.eval i).integrable (hnoise i).hasGaussianLaw.integrable,
    hF i,(hnoise i).integral_eq,integral_id_gaussianReal,zero_add]

theorem actual_covariance_gram_is_positive_semidefinite_from_true_second_moments
    (hF : ∀ i,MemLp (fun o => F o i) 2 P) :
    (observationCovariance P F).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial,observationCovariance]
    exact covariance_comm _ _
  · intro x
    have hsum : MemLp (fun o => ∑ i,x i*F o i) 2 P :=
      memLp_finsetSum _ (fun i _ => (hF i).const_mul _)
    have hc : cov[fun o => ∑ i,x i*F o i,fun o => ∑ i,x i*F o i;P]=
        x ⬝ᵥ (observationCovariance P F*ᵥx) := by
      rw [covariance_fun_sum_fun_sum (fun i => (hF i).const_mul _) (fun i => (hF i).const_mul _)]
      simp only [covariance_const_mul_left,covariance_const_mul_right,dotProduct,Matrix.mulVec,
        observationCovariance,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [covariance_self hsum.aemeasurable] at hc
    simpa only [star_trivial,← hc] using variance_nonneg (fun o => ∑ i,x i*F o i) P

theorem actual_positive_noise_makes_the_true_observation_covariance_positive_definite
    (hprior : HasGaussianLaw (fun o => (F o,Z o)) P)
    (hnoise : ∀ i,HasLaw (fun o => E o i) (gaussianReal 0 lambda) P)
    (hnoises : iIndepFun (fun i o => E o i) P)
    (hindependent : IndepFun (fun o => (F o,Z o)) E P) (hlambda : 0<lambda) :
    (observationCovariance P (observation F E)).PosDef := by
  rw [actual_source_observation_covariance_is_the_prior_gram_plus_noise_diagonal
    P F E Z lambda hprior hnoise hnoises hindependent]
  exact Matrix.PosDef.posSemidef_add
    (actual_covariance_gram_is_positive_semidefinite_from_true_second_moments P F
      (fun i => (hprior.fst.eval i).memLp_two))
    ((Matrix.PosDef.one : (1 : Matrix I I ℝ).PosDef).smul hlambda)

end SafeLearning.CompleteModulesGaussianObservationModel
