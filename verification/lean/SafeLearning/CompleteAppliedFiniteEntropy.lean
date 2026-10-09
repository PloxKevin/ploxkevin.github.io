import SafeLearning.CompleteAppliedInformation
import SafeLearning.CompleteAppliedFiniteKLSupport
import Mathlib.Probability.Distributions.Uniform
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedFiniteEntropy
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedFiniteKL
open SafeLearning.CompleteAppliedFiniteKLSupport
open scoped ENNReal NNReal Classical

theorem actual_finite_weights_sum {n : ℕ} (p : PMF (Fin n)) :
    (∑ i,(p i).toReal)=1 := by
  rw [← ENNReal.toReal_sum (fun i _ => p.apply_ne_top i)]
  have h:=p.tsum_coe
  rw [tsum_fintype] at h
  rw [h]
  norm_num

theorem actual_entropy_sum {n : ℕ} (p : PMF (Fin n)) :
    shannonEntropy p=∑ i,-(p i).toReal*Real.log (p i).toReal := by
  rw [shannonEntropy,PMF.integral_eq_sum]
  simp only [smul_eq_mul,Finset.sum_neg_distrib,neg_mul]

theorem actual_entropy_nonnegative {n : ℕ} (p : PMF (Fin n)) : 0 ≤ shannonEntropy p := by
  rw [actual_entropy_sum]
  apply Finset.sum_nonneg
  intro i _
  have hp:(p i).toReal≤1 := by
    exact (ENNReal.toReal_le_toReal (p.apply_ne_top i) ENNReal.one_ne_top).mpr (p.coe_le_one i)
  have hlog:=Real.log_nonpos ENNReal.toReal_nonneg hp
  nlinarith [ENNReal.toReal_nonneg (a:=p i)]

theorem actual_uniform_mass {n : ℕ} [NeZero n] (i : Fin n) :
    (PMF.uniformOfFintype (Fin n) i).toReal=(n:ℝ)⁻¹ := by
  simp [PMF.uniformOfFintype_apply,ENNReal.toReal_inv]

theorem actual_uniform_kl_entropy_identity {n : ℕ} [NeZero n] (p : PMF (Fin n)) :
    (klDiv p.toMeasure (PMF.uniformOfFintype (Fin n)).toMeasure).toReal=
      Real.log (n:ℝ)-shannonEntropy p := by
  have hq:∀ i,PMF.uniformOfFintype (Fin n) i≠0 := by
    intro i
    exact PMF.mem_support_uniformOfFintype i
  rw [actual_finite_kl_sum p _ hq,actual_entropy_sum]
  have hi (i : Fin n) : (p i).toReal*Real.log ((p i).toReal/
      (PMF.uniformOfFintype (Fin n) i).toReal)=
      (p i).toReal*Real.log (p i).toReal+(p i).toReal*Real.log (n:ℝ) := by
    rw [actual_uniform_mass]
    by_cases hp:(p i).toReal=0
    · simp [hp]
    · rw [Real.log_div hp (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n))),Real.log_inv]
      ring
  simp only [hi,Finset.sum_add_distrib,← Finset.sum_mul,actual_finite_weights_sum,one_mul,
    neg_mul,Finset.sum_neg_distrib]
  ring

theorem actual_entropy_upper_bound {n : ℕ} [NeZero n] (p : PMF (Fin n)) :
    shannonEntropy p≤Real.log (n:ℝ) := by
  have h:=ENNReal.toReal_nonneg
    (a:=klDiv p.toMeasure (PMF.uniformOfFintype (Fin n)).toMeasure)
  rw [actual_uniform_kl_entropy_identity] at h
  linarith

theorem actual_maximum_entropy_iff_uniform {n : ℕ} [NeZero n] (p : PMF (Fin n)) :
    shannonEntropy p=Real.log (n:ℝ) ↔ p=PMF.uniformOfFintype (Fin n) := by
  have hq:∀ i,PMF.uniformOfFintype (Fin n) i≠0 := fun i=>PMF.mem_support_uniformOfFintype i
  have hfin:=actual_finite_kl_is_finite p _ hq
  have hz:(klDiv p.toMeasure (PMF.uniformOfFintype (Fin n)).toMeasure).toReal=0 ↔
      klDiv p.toMeasure (PMF.uniformOfFintype (Fin n)).toMeasure=0 := by
    rw [ENNReal.toReal_eq_zero_iff]
    simp only [hfin,or_false]
  rw [← actual_finite_gibbs_equality p (PMF.uniformOfFintype (Fin n)),
    ← hz,actual_uniform_kl_entropy_identity]
  constructor <;> intro h <;> linarith

end SafeLearning.CompleteAppliedFiniteEntropy
