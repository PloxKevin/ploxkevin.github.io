import SafeLearning.CompleteAppliedTemperatureSoftmax

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory InformationTheory

namespace SafeLearning.CompletePolicyFOCOPSModel20
open SafeLearning.CompleteAppliedTemperatureSoftmax
open SafeLearning.CompleteAppliedFiniteEntropy
open SafeLearning.CompleteAppliedFiniteKL
open SafeLearning.CompleteAppliedInformation

def oldLaw : PMF (Fin 2) := PMF.uniformOfFintype (Fin 2)
def reward (law : PMF (Fin 2)) : ℝ :=
  ∫ i, (![1, -1] : Fin 2 → ℝ) i ∂law.toMeasure
def cost (law : PMF (Fin 2)) : ℝ :=
  ∫ i, (![2, -2] : Fin 2 → ℝ) i ∂law.toMeasure
def trueKL (law : PMF (Fin 2)) : ℝ :=
  (klDiv law.toMeasure oldLaw.toMeasure).toReal
def scores (ν : ℝ) : Fin 2 → ℝ := ![1 - 2 * ν, -(1 - 2 * ν)]
def gibbs (lam ν : ℝ) : PMF (Fin 2) := actualTemperatureLaw (scores ν) lam
def probability (lam ν : ℝ) : ℝ :=
  Real.exp ((1 - 2 * ν) / lam) /
    (Real.exp ((1 - 2 * ν) / lam) + Real.exp (-((1 - 2 * ν) / lam)))
def regularizedReward (lam : ℝ) (law : PMF (Fin 2)) : ℝ :=
  reward law - lam * trueKL law
def lagrangian (lam ν : ℝ) (law : PMF (Fin 2)) : ℝ :=
  regularizedReward lam law - ν * (cost law - 1 / 2)

theorem actual_old_masses (i : Fin 2) : (oldLaw i).toReal = 1 / 2 := by
  simpa [oldLaw] using (actual_uniform_mass i)

theorem actual_finite_masses_sum (law : PMF (Fin 2)) :
    (law 0).toReal + (law 1).toReal = 1 := by
  simpa [Fin.sum_univ_two] using
    SafeLearning.CompleteAppliedFiniteEntropy.actual_finite_weights_sum law

theorem actual_reward_and_cost_expectations (law : PMF (Fin 2)) :
    reward law = 2 * (law 0).toReal - 1 ∧
      cost law = 4 * (law 0).toReal - 2 := by
  have h := actual_finite_masses_sum law
  constructor <;>
    simp only [reward, cost, PMF.integral_eq_sum, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] <;> linarith

theorem actual_cost_feasibility_iff (law : PMF (Fin 2)) :
    cost law ≤ 1 / 2 ↔ (law 0).toReal ≤ 5 / 8 := by
  rw [(actual_reward_and_cost_expectations law).2]
  constructor <;> intro h <;> linarith

theorem actual_uniform_prior_kl_entropy (law : PMF (Fin 2)) :
    trueKL law = Real.log 2 - shannonEntropy law := by
  exact actual_uniform_kl_entropy_identity law

theorem actual_gibbs_masses (lam ν : ℝ) :
    (gibbs lam ν 0).toReal = probability lam ν ∧
      (gibbs lam ν 1).toReal = 1 - probability lam ν := by
  have h0 : (gibbs lam ν 0).toReal = probability lam ν := by
    simp [gibbs, actual_temperature_law_has_the_literal_normalized_exponential_masses,
      actualPartition, scores, probability, Fin.sum_univ_two, neg_div]
  refine ⟨h0, ?_⟩
  have h := actual_finite_masses_sum (gibbs lam ν)
  rw [h0] at h
  linarith

theorem actual_gibbs_probability_in_open_unit_interval (lam ν : ℝ) :
    0 < probability lam ν ∧ probability lam ν < 1 := by
  have h0 := (actual_temperature_law_has_full_support_and_positive_real_masses
    (scores ν) lam (0 : Fin 2)).2
  have h1 := (actual_temperature_law_has_full_support_and_positive_real_masses
    (scores ν) lam (1 : Fin 2)).2
  change 0 < (gibbs lam ν 0).toReal at h0
  change 0 < (gibbs lam ν 1).toReal at h1
  rw [(actual_gibbs_masses lam ν).1] at h0
  rw [(actual_gibbs_masses lam ν).2] at h1
  constructor <;> linarith

theorem actual_gibbs_log_odds (lam ν : ℝ) :
    Real.log (probability lam ν / (1 - probability lam ν)) =
      2 * (1 - 2 * ν) / lam := by
  let u := (1 - 2 * ν) / lam
  have hratio : probability lam ν / (1 - probability lam ν) =
      Real.exp u / Real.exp (-u) := by
    dsimp [probability, u]
    field_simp
    ring
  rw [hratio, Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp]
  dsimp [u]
  ring

theorem actual_gibbs_cost_feasibility_exact_multiplier (lam ν : ℝ) (hlam : 0 < lam) :
    cost (gibbs lam ν) ≤ 1 / 2 ↔
      1 / 2 - lam / 4 * Real.log (5 / 3) ≤ ν := by
  rw [actual_cost_feasibility_iff, (actual_gibbs_masses lam ν).1]
  let u := (1 - 2 * ν) / lam
  have hd : 0 < Real.exp u + Real.exp (-u) :=
    add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hr : Real.exp u / Real.exp (-u) = Real.exp (2 * u) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hle : probability lam ν ≤ 5 / 8 ↔ Real.exp (2 * u) ≤ 5 / 3 := by
    rw [probability, div_le_iff₀ hd]
    rw [← hr, div_le_iff₀ (Real.exp_pos _)]
    constructor <;> intro h <;> linarith
  rw [hle, show (5 / 3 : ℝ) = Real.exp (Real.log (5 / 3)) from
    (Real.exp_log (by norm_num)).symm, Real.exp_le_exp]
  dsimp [u]
  rw [show 2 * ((1 - 2 * ν) / lam) = (2 - 4 * ν) / lam by ring,
    div_le_iff₀ hlam]
  constructor <;> intro h <;> nlinarith

theorem actual_score_expectation (ν : ℝ) (law : PMF (Fin 2)) :
    (∫ i, scores ν i ∂law.toMeasure) = reward law - ν * cost law := by
  simp only [scores, reward, cost, PMF.integral_eq_sum, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  ring

theorem actual_lagrangian_is_entropy_objective (lam ν : ℝ) (law : PMF (Fin 2)) :
    lagrangian lam ν law = actualTemperatureObjective (scores ν) lam law -
      lam * Real.log 2 + ν / 2 := by
  rw [lagrangian, regularizedReward, actual_uniform_prior_kl_entropy,
    actualTemperatureObjective, actual_score_expectation]
  ring

theorem actual_gibbs_is_unique_global_lagrangian_maximizer
    (lam ν : ℝ) (hlam : 0 < lam) (law : PMF (Fin 2)) :
    lagrangian lam ν law ≤ lagrangian lam ν (gibbs lam ν) ∧
      (lagrangian lam ν law = lagrangian lam ν (gibbs lam ν) ↔ law = gibbs lam ν) := by
  have h := actual_temperature_law_is_the_unique_global_entropy_regularized_optimizer
    (scores ν) lam hlam law
  have hself := actual_temperature_law_is_the_unique_global_entropy_regularized_optimizer
    (scores ν) lam hlam (gibbs lam ν)
  have he := hself.2.mpr rfl
  simp only [actual_lagrangian_is_entropy_objective]
  rw [he]
  refine ⟨by linarith [h.1], ?_⟩
  constructor
  · intro hh
    apply h.2.mp
    linarith
  · intro hh
    rw [h.2.mpr hh]

theorem actual_feasible_complementary_gibbs_is_unique_constrained_regularized_optimizer
    (lam ν : ℝ) (hlam : 0 < lam) (hν : 0 ≤ ν)
    (hg : cost (gibbs lam ν) ≤ 1 / 2)
    (hc : ν * (cost (gibbs lam ν) - 1 / 2) = 0)
    (law : PMF (Fin 2)) (hlaw : cost law ≤ 1 / 2) :
    regularizedReward lam law ≤ regularizedReward lam (gibbs lam ν) ∧
      (regularizedReward lam law = regularizedReward lam (gibbs lam ν) ↔ law = gibbs lam ν) := by
  have hm := actual_gibbs_is_unique_global_lagrangian_maximizer lam ν hlam law
  have hn : ν * (cost law - 1 / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hν (by linarith)
  simp only [lagrangian, hc, sub_zero] at hm
  refine ⟨by linarith [hm.1], ?_⟩
  constructor
  · intro he
    apply hm.2.mp
    linarith [hm.1]
  · rintro rfl
    rfl

end SafeLearning.CompletePolicyFOCOPSModel20
