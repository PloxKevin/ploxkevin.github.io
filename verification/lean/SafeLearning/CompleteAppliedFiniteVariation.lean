import SafeLearning.CompleteAppliedFiniteEntropy
import SafeLearning.CompleteAppliedFiniteClaims
import SafeLearning.CompleteAppliedAlarmModel
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedFiniteVariation
open MeasureTheory
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedInformation
open SafeLearning.CompleteAppliedFiniteEntropy SafeLearning.CompleteAppliedFiniteClaims
open SafeLearning.CompleteAppliedAlarmModel
open scoped ENNReal NNReal Classical

theorem actual_finite_event_sum {n : ℕ} (p : PMF (Fin n)) (E : Set (Fin n)) :
    p.toMeasure.real E=∑ i,if i∈E then (p i).toReal else 0 := by
  rw [actual_finite_event_probability,← finite_indicator_expectation]
  unfold finiteExpectation
  apply Finset.sum_congr rfl
  intro i _
  by_cases h:i∈E <;> simp [Set.indicator,h]

theorem zero_sum_positive_mass {n : ℕ} (d : Fin n→ℝ) (hd : ∑ i,d i=0) :
    (∑ i,max (d i) 0)=(1/2)*∑ i,|d i| := by
  have hx:∑ i,|d i|=2*∑ i,max (d i) 0-∑ i,d i := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:0≤d i
    · rw [abs_of_nonneg hi,max_eq_left hi]
      ring
    · have hn:d i≤0:=le_of_not_ge hi
      rw [abs_of_nonpos hn,max_eq_right hn]
      ring
  rw [hd] at hx
  linarith

theorem actual_event_difference_sum {n : ℕ} (p q : PMF (Fin n)) (E : Set (Fin n)) :
    p.toMeasure.real E-q.toMeasure.real E=
      ∑ i,if i∈E then (p i).toReal-(q i).toReal else 0 := by
  rw [actual_finite_event_sum,actual_finite_event_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h:i∈E <;> simp [h]

theorem arbitrary_event_zero_sum_bound {n : ℕ} (d : Fin n→ℝ) (hd : ∑ i,d i=0)
    (E : Set (Fin n)) : |∑ i,if i∈E then d i else 0|≤∑ i,max (d i) 0 := by
  have hu (A : Set (Fin n)) : (∑ i,if i∈A then d i else 0)≤∑ i,max (d i) 0 := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h:i∈A
    · simp only [h,ite_true]
      exact le_max_left _ _
    · simp only [h,ite_false]
      exact le_max_right _ _
  have hsum:(∑ i,if i∈E then d i else 0)+(∑ i,if i∈Eᶜ then d i else 0)=0 := by
    rw [← Finset.sum_add_distrib]
    convert hd using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases h:i∈E <;> simp [h]
  rw [abs_le]
  constructor
  · rw [eq_neg_of_add_eq_zero_left hsum]
    apply neg_le_neg
    simpa using hu Eᶜ
  · exact hu E

theorem actual_finite_event_tv_bound {n : ℕ} (p q : PMF (Fin n)) (E : Set (Fin n)) :
    |p.toMeasure.real E-q.toMeasure.real E|≤(1/2)*∑ i,|(p i).toReal-(q i).toReal| := by
  have hz:∑ i,((p i).toReal-(q i).toReal)=0 := by
    rw [Finset.sum_sub_distrib,actual_finite_weights_sum,actual_finite_weights_sum]
    ring
  rw [actual_event_difference_sum,← zero_sum_positive_mass _ hz]
  exact arbitrary_event_zero_sum_bound _ hz E

theorem actual_finite_total_variation {n : ℕ} (p q : PMF (Fin n)) :
    totalVariation p q=(1/2)*∑ i,|(p i).toReal-(q i).toReal| := by
  have hz:∑ i,((p i).toReal-(q i).toReal)=0 := by
    rw [Finset.sum_sub_distrib,actual_finite_weights_sum,actual_finite_weights_sum]
    ring
  let A:Set (Fin n):={i|(q i).toReal≤(p i).toReal}
  have hatt:|p.toMeasure.real A-q.toMeasure.real A|=(1/2)*∑ i,|(p i).toReal-(q i).toReal| := by
    rw [actual_event_difference_sum]
    have he:(∑ i,if i∈A then (p i).toReal-(q i).toReal else 0)=
        ∑ i,max ((p i).toReal-(q i).toReal) 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h:(q i).toReal≤(p i).toReal
      · simp [A,h,max_eq_left (sub_nonneg.mpr h)]
      · simp [A,h,max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    rw [he,abs_of_nonneg (Finset.sum_nonneg (fun i _=>le_max_right _ _)),
      zero_sum_positive_mass _ hz]
  unfold totalVariation
  apply IsLUB.csSup_eq
  · constructor
    · rintro d ⟨E,rfl⟩
      exact actual_finite_event_tv_bound p q E
    · intro b hb
      apply hb
      exact ⟨A,hatt.symm⟩
  · exact ⟨|p.toMeasure.real A-q.toMeasure.real A|,A,rfl⟩

theorem actual_finite_tv_symmetric {n : ℕ} (p q : PMF (Fin n)) :
    totalVariation p q=totalVariation q p := by
  rw [actual_finite_total_variation,actual_finite_total_variation]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact abs_sub_comm _ _

theorem actual_finite_tv_range {n : ℕ} (p q : PMF (Fin n)) :
    0≤totalVariation p q ∧ totalVariation p q≤1 := by
  rw [actual_finite_total_variation]
  constructor
  · positivity
  · have hs:(∑ i,|(p i).toReal-(q i).toReal|)≤
        (∑ i,(p i).toReal)+(∑ i,(q i).toReal) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      rw [abs_le]
      constructor <;> linarith [ENNReal.toReal_nonneg (a:=p i),ENNReal.toReal_nonneg (a:=q i)]
    rw [actual_finite_weights_sum,actual_finite_weights_sum] at hs
    linarith

end SafeLearning.CompleteAppliedFiniteVariation
