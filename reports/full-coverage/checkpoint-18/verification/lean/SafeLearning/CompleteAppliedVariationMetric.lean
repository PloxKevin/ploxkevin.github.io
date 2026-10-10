import SafeLearning.CompleteAppliedFiniteVariation
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedVariationMetric
open MeasureTheory
open SafeLearning.CompleteAppliedInformation SafeLearning.CompleteAppliedFiniteVariation
open SafeLearning.CompleteAppliedFiniteEntropy
open scoped ENNReal NNReal Classical

theorem actual_finite_tv_zero_iff {n : ℕ} (p q : PMF (Fin n)) :
    totalVariation p q=0 ↔ p=q := by
  constructor
  · intro h
    have hs:(∑ i,|(p i).toReal-(q i).toReal|)=0 := by
      rw [actual_finite_total_variation] at h
      linarith
    have hi:∀ i,(p i).toReal=(q i).toReal := by
      intro i
      have ha:|(p i).toReal-(q i).toReal|≤∑ j,|(p j).toReal-(q j).toReal| :=
        Finset.single_le_sum (f:=fun j=>|(p j).toReal-(q j).toReal|) (fun j _=>abs_nonneg _) (Finset.mem_univ i)
      rw [hs] at ha
      have hz:|(p i).toReal-(q i).toReal|=0:=le_antisymm ha (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    apply PMF.ext
    intro i
    exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top i) (q.apply_ne_top i)).mp (hi i)
  · rintro rfl
    simp [actual_finite_total_variation]

theorem actual_finite_tv_triangle {n : ℕ} (p q r : PMF (Fin n)) :
    totalVariation p r≤totalVariation p q+totalVariation q r := by
  rw [actual_finite_total_variation,actual_finite_total_variation,actual_finite_total_variation]
  have hs:(∑ i,|(p i).toReal-(r i).toReal|)≤
      (∑ i,|(p i).toReal-(q i).toReal|)+(∑ i,|(q i).toReal-(r i).toReal|) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _=>abs_sub_le _ _ _)
  linarith

theorem weighted_zero_sum_bound {n : ℕ} (d : Fin n→ℝ) (hd : ∑ i,d i=0)
    (g : Fin n→ℝ) (hg : ∀ i,g i∈Set.Icc (0:ℝ) 1) :
    |∑ i,d i*g i|≤∑ i,max (d i) 0 := by
  have hu (a : Fin n→ℝ) (ha : ∀ i,a i∈Set.Icc (0:ℝ) 1) :
      (∑ i,d i*a i)≤∑ i,max (d i) 0 := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi:0≤d i
    · rw [max_eq_left hi]
      nlinarith [(ha i).1,(ha i).2]
    · rw [max_eq_right (le_of_not_ge hi)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hi) (ha i).1
  have hcomp:∀ i,1-g i∈Set.Icc (0:ℝ) 1 := by
    intro i
    constructor <;> linarith [(hg i).1,(hg i).2]
  have he:(∑ i,d i*g i)+(∑ i,d i*(1-g i))=0 := by
    rw [← Finset.sum_add_distrib]
    convert hd using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [abs_le]
  constructor
  · rw [eq_neg_of_add_eq_zero_left he]
    exact neg_le_neg (hu _ hcomp)
  · exact hu g hg

theorem actual_bounded_expectation_difference {n : ℕ} (p q : PMF (Fin n))
    (g : Fin n→ℝ) (hg : ∀ i,g i∈Set.Icc (0:ℝ) 1) :
    |(∫ i,g i ∂p.toMeasure)-(∫ i,g i ∂q.toMeasure)|≤totalVariation p q := by
  have hz:∑ i,((p i).toReal-(q i).toReal)=0 := by
    rw [Finset.sum_sub_distrib,actual_finite_weights_sum,actual_finite_weights_sum]
    ring
  rw [PMF.integral_eq_sum,PMF.integral_eq_sum,actual_finite_total_variation,
    ← zero_sum_positive_mass _ hz]
  simp only [smul_eq_mul,← Finset.sum_sub_distrib]
  have he:(∑ i,((p i).toReal*g i-(q i).toReal*g i))=
      ∑ i,((p i).toReal-(q i).toReal)*g i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact weighted_zero_sum_bound _ hz g hg

end SafeLearning.CompleteAppliedVariationMetric
