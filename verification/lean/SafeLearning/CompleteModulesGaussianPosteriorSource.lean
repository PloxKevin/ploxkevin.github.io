import SafeLearning.CompleteModulesGaussianSchurConsequences
import SafeLearning.CompleteModulesGaussianObservationModel
import SafeLearning.CompleteModulesGaussianRankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal BigOperators
namespace SafeLearning.CompleteModulesGaussianPosteriorSource
open CompleteModulesGaussianRegressionFinite CompleteModulesGaussianSchurConsequences
open CompleteModulesGaussianObservationModel

variable {I J Omega : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [MeasurableSpace Omega]

theorem actual_symmetric_schur_quadratic_has_the_literal_completing_square_identity
    (S : Matrix J J ℝ) (b m : J → ℝ) (hS : Sᵀ=S) :
    b ⬝ᵥ (S*ᵥb)-2*(b ⬝ᵥ (S*ᵥm))=
      (b-m) ⬝ᵥ (S*ᵥ(b-m))-m ⬝ᵥ (S*ᵥm) := by
  have hc : m ⬝ᵥ (S*ᵥb)=b ⬝ᵥ (S*ᵥm) := by
    rw [dotProduct_mulVec,← mulVec_transpose,hS,dotProduct_comm]
  simp only [Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub,hc]
  ring

theorem actual_gaussian_prior_with_independent_noise_derives_the_source_posterior_joint
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F E : Omega → I → ℝ) (Z : Omega → ℝ) (lambda : ℝ≥0)
    (hprior : HasGaussianLaw (fun o => (F o,Z o)) P)
    (hnoise : ∀ i,HasLaw (fun o => E o i) (gaussianReal 0 lambda) P)
    (hnoises : iIndepFun (fun i o => E o i) P)
    (hindependent : IndepFun (fun o => (F o,Z o)) E P)
    (hlambda : 0<lambda) (hF : ∀ i,(∫ o,F o i ∂P)=0) (hZ : (∫ o,Z o ∂P)=0) :
    let K := observationCovariance P F
    let C := crossCovariance P F Z
    P.map (fun o => (observation F E o,Z o))=(P.map (observation F E)) ⊗ₘ
      ⟨fun y => gaussianReal (C ⬝ᵥ ((K+(lambda : ℝ) • (1 : Matrix I I ℝ))⁻¹*ᵥy))
          (Var[Z;P]-C ⬝ᵥ ((K+(lambda : ℝ) • (1 : Matrix I I ℝ))⁻¹*ᵥC)).toNNReal,
        by fun_prop⟩ := by
  intro K C
  have hg := actual_prior_plus_independent_gaussian_noise_and_query_are_jointly_gaussian
    P F E Z lambda hprior hnoise hnoises hindependent
  have hcov := actual_source_observation_covariance_is_the_prior_gram_plus_noise_diagonal
    P F E Z lambda hprior hnoise hnoises hindependent
  have hcross := actual_source_observation_query_cross_covariance_is_the_true_prior_query_vector
    P F E Z lambda hprior hnoise hindependent
  have hpd := actual_positive_noise_makes_the_true_observation_covariance_positive_definite
    P F E Z lambda hprior hnoise hnoises hindependent hlambda
  have hu : IsUnit (K+(lambda : ℝ) • (1 : Matrix I I ℝ)) := by
    rw [← hcov]
    exact hpd.isUnit
  exact actual_gp_covariance_identification_translates_to_the_source_ridge_and_query_formula
    P (observation F E) Z K C (Var[Z;P]) lambda hg hcov hcross rfl hu
      (fun i => actual_centered_prior_and_centered_noise_give_the_true_zero_observation_mean
        P F E Z lambda hprior hnoise hF i) hZ

section RankOne
open CompleteModulesGaussianRankOne
variable (P : Measure Omega) [IsProbabilityMeasure P]
variable (U N : Omega → ℝ) (Z : Omega → I → ℝ) (lambda : ℝ≥0)

theorem actual_new_gaussian_observation_of_a_gaussian_query_family_is_jointly_gaussian
    (hprior : HasGaussianLaw (fun o => (U o,Z o)) P)
    (hnoise : HasLaw N (gaussianReal 0 lambda) P)
    (hindependent : IndepFun (fun o => (U o,Z o)) N P) :
    HasGaussianLaw (fun o => (U o+N o,Z o)) P := by
  have hf := hindependent.hasGaussianLaw hprior hnoise.hasGaussianLaw
  let latent : ((ℝ × (I → ℝ)) × ℝ) →L[ℝ] (ℝ × (I → ℝ)) :=
    ContinuousLinearMap.fst ℝ (ℝ × (I → ℝ)) ℝ
  let noise : ((ℝ × (I → ℝ)) × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ (ℝ × (I → ℝ)) ℝ
  let combine := (((ContinuousLinearMap.fst ℝ ℝ (I → ℝ)).comp latent)+noise).prod
    ((ContinuousLinearMap.snd ℝ ℝ (I → ℝ)).comp latent)
  convert hf.map_fun combine using 1 <;> rfl

theorem actual_new_observation_variance_equals_latent_variance_plus_noise
    (hprior : HasGaussianLaw (fun o => (U o,Z o)) P)
    (hnoise : HasLaw N (gaussianReal 0 lambda) P)
    (hindependent : IndepFun (fun o => (U o,Z o)) N P) :
    Var[fun o => U o+N o;P]=Var[U;P]+lambda := by
  have h := hindependent.comp measurable_fst measurable_id
  rw [h.variance_fun_add hprior.fst.memLp_two hnoise.hasGaussianLaw.memLp_two,
    hnoise.variance_eq,variance_id_gaussianReal]

theorem actual_new_observation_query_covariance_equals_the_latent_cross_covariance
    (hprior : HasGaussianLaw (fun o => (U o,Z o)) P)
    (hnoise : HasLaw N (gaussianReal 0 lambda) P)
    (hindependent : IndepFun (fun o => (U o,Z o)) N P) (i : I) :
    cov[fun o => U o+N o,fun o => Z o i;P]=cov[U,fun o => Z o i;P] := by
  have hz := (hprior.snd.eval i).memLp_two
  have hn := hnoise.hasGaussianLaw.memLp_two
  have h := hindependent.comp ((measurable_pi_apply i).comp measurable_snd) measurable_id
  have hc : cov[N,fun o => Z o i;P]=0 := h.symm.covariance_eq_zero hn hz
  change cov[U+N,fun o => Z o i;P]=_
  rw [covariance_add_left hprior.fst.memLp_two hn hz,hc,add_zero]

theorem actual_independent_noise_conditioning_gives_the_source_covariance_rank_one_update
    (hprior : HasGaussianLaw (fun o => (U o,Z o)) P)
    (hnoise : HasLaw N (gaussianReal 0 lambda) P)
    (hindependent : IndepFun (fun o => (U o,Z o)) N P) (hlambda : 0<lambda)
    (y : ℝ) (i j : I) :
    cov[fun r => r i,fun r => r j;conditionalKernel P (fun o => U o+N o) Z y]=
      cov[fun o => Z o i,fun o => Z o j;P]-
        cov[fun o => Z o i,U;P]*cov[U,fun o => Z o j;P]/(Var[U;P]+lambda) := by
  have hg := actual_new_gaussian_observation_of_a_gaussian_query_family_is_jointly_gaussian
    P U N Z lambda hprior hnoise hindependent
  have hv := actual_new_observation_variance_equals_latent_variance_plus_noise
    P U N Z lambda hprior hnoise hindependent
  have hp : 0<Var[fun o => U o+N o;P] := by
    rw [hv]
    exact add_pos_of_nonneg_of_pos (variance_nonneg U P) hlambda
  rw [actual_conditional_query_covariance_is_the_literal_rank_one_update_at_every_observed_value
    P (fun o => U o+N o) Z hg hp y i j,hv,
    covariance_comm (fun o => Z o i) (fun o => U o+N o),
    actual_new_observation_query_covariance_equals_the_latent_cross_covariance
      P U N Z lambda hprior hnoise hindependent i,
    actual_new_observation_query_covariance_equals_the_latent_cross_covariance
      P U N Z lambda hprior hnoise hindependent j,covariance_comm U (fun o => Z o i)]

theorem actual_independent_noise_conditioning_never_increases_any_query_variance
    (hprior : HasGaussianLaw (fun o => (U o,Z o)) P)
    (hnoise : HasLaw N (gaussianReal 0 lambda) P)
    (hindependent : IndepFun (fun o => (U o,Z o)) N P) (hlambda : 0<lambda)
    (y : ℝ) (i : I) :
    Var[fun r => r i;conditionalKernel P (fun o => U o+N o) Z y]≤Var[fun o => Z o i;P] := by
  have hg := actual_new_gaussian_observation_of_a_gaussian_query_family_is_jointly_gaussian
    P U N Z lambda hprior hnoise hindependent
  have hp : 0<Var[fun o => U o+N o;P] := by
    rw [actual_new_observation_variance_equals_latent_variance_plus_noise
      P U N Z lambda hprior hnoise hindependent]
    exact add_pos_of_nonneg_of_pos (variance_nonneg U P) hlambda
  exact actual_conditional_variance_never_increases_at_any_query_or_observed_value
    P (fun o => U o+N o) Z hg hp y i

end RankOne
end SafeLearning.CompleteModulesGaussianPosteriorSource
