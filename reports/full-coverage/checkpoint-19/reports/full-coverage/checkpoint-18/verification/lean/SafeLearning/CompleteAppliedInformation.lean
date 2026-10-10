import SafeLearning.CompleteAppliedFiniteKL
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedInformation
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedProbability SafeLearning.CompleteAppliedBandit
open SafeLearning.CompleteAppliedTwoAtomRisk SafeLearning.CompleteAppliedFiniteKL
open scoped ENNReal NNReal Classical

def fair : unitInterval:=⟨1/2,by norm_num⟩
def biased : unitInterval:=⟨1/4,by norm_num⟩
def certain : unitInterval:=⟨0,by norm_num⟩
def shannonEntropy {n : ℕ} (p : PMF (Fin n)) : ℝ :=
  -(∫ i,Real.log ((p i).toReal) ∂p.toMeasure)
def totalVariation {n : ℕ} (p q : PMF (Fin n)) : ℝ :=
  sSup {d | ∃ E : Set (Fin n),d=|p.toMeasure.real E-q.toMeasure.real E|}

theorem actual_binary_entropy (q : unitInterval) :
    shannonEntropy (costLaw q)=Real.binEntropy (q:ℝ) := by
  unfold shannonEntropy
  rw [← finite_expectation_is_actual_integral,actual_two_atom_expectation]
  simp only [costLaw,PMF.ofFintype_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    ENNReal.toReal_ofReal (sub_nonneg.mpr q.2.2),ENNReal.toReal_ofReal q.2.1,
    Real.binEntropy,Real.log_inv]
  ring

theorem source_binary_entropy_formula (q : unitInterval) :
    shannonEntropy (costLaw q)=-(q:ℝ)*Real.log (q:ℝ)-
      (1-(q:ℝ))*Real.log (1-(q:ℝ)) := by
  rw [actual_binary_entropy,Real.binEntropy,Real.log_inv,Real.log_inv]
  ring

theorem actual_fair_entropy : shannonEntropy (costLaw fair)=Real.log 2 := by
  rw [actual_binary_entropy]
  simpa [fair] using Real.binEntropy_two_inv

theorem actual_biased_entropy : shannonEntropy (costLaw biased)=
    2*Real.log 2-(3/4)*Real.log 3 := by
  rw [source_binary_entropy_formula]
  norm_num [biased,Real.log_div]
  rw [Real.log_four_eq]
  ring

theorem fair_entropy_strictly_larger :
    shannonEntropy (costLaw biased)<shannonEntropy (costLaw fair) := by
  rw [actual_binary_entropy,actual_fair_entropy]
  exact Real.binEntropy_lt_log_two.mpr (by norm_num [biased])

theorem actual_entropy_in_bits {n : ℕ} (p : PMF (Fin n)) :
    -(∫ i,Real.logb 2 ((p i).toReal) ∂p.toMeasure)=shannonEntropy p/Real.log 2 := by
  simp only [Real.logb,integral_div,shannonEntropy]
  ring

theorem actual_finite_kl_reconstruction {n : ℕ} (p q : PMF (Fin n))
    (hq : ∀ i,q i≠0) : klDiv p.toMeasure q.toMeasure=
      ENNReal.ofReal (∑ i,(p i).toReal*Real.log ((p i).toReal/(q i).toReal)) := by
  calc
    _=ENNReal.ofReal (klDiv p.toMeasure q.toMeasure).toReal :=
      (ENNReal.ofReal_toReal (actual_finite_kl_is_finite p q hq)).symm
    _=_ := congrArg ENNReal.ofReal (actual_finite_kl_sum p q hq)

theorem actual_binary_event_probability (q : unitInterval) (E : Set (Fin 2)) :
    (costLaw q).toMeasure.real E=
      (if (0:Fin 2)∈E then 1-(q:ℝ) else 0)+(if (1:Fin 2)∈E then (q:ℝ) else 0) := by
  classical
  unfold Measure.real
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.toFinite E).measurableSet]
  by_cases h0:(0:Fin 2)∈E <;> by_cases h1:(1:Fin 2)∈E
  all_goals simp [PMF.toOuterMeasure_ofFintype_apply,tsum_fintype,costLaw,
    Fin.sum_univ_two,Set.indicator,h0,h1,

    ENNReal.toReal_ofReal (sub_nonneg.mpr q.2.2),ENNReal.toReal_ofReal q.2.1]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr q.2.2) q.2.1]
  simp

theorem actual_binary_event_difference_bound (q r : unitInterval) (E : Set (Fin 2)) :
    |(costLaw q).toMeasure.real E-(costLaw r).toMeasure.real E|≤|(q:ℝ)-(r:ℝ)| := by
  classical
  rw [actual_binary_event_probability,actual_binary_event_probability]
  by_cases h0:(0:Fin 2)∈E <;> by_cases h1:(1:Fin 2)∈E
  · simp [h0,h1]
  · simp only [h0,h1,ite_true,ite_false,add_zero]
    rw [show 1-(q:ℝ)-(1-(r:ℝ))=-((q:ℝ)-(r:ℝ)) by ring,abs_neg]
  · simp [h0,h1]
  · simp [h0,h1]

theorem actual_binary_total_variation (q r : unitInterval) :
    totalVariation (costLaw q) (costLaw r)=|(q:ℝ)-(r:ℝ)| := by
  apply IsLUB.csSup_eq
  · constructor
    · rintro d ⟨E,rfl⟩
      exact actual_binary_event_difference_bound q r E
    · intro b hb
      apply hb
      refine ⟨{1},?_⟩
      simp [actual_binary_event_probability]
  · exact ⟨|(q:ℝ)-(r:ℝ)|,{1},by simp [actual_binary_event_probability]⟩

theorem source_total_variations :
    totalVariation (costLaw biased) (costLaw fair)=1/4 ∧
      totalVariation (costLaw certain) (costLaw fair)=1/2 := by
  simp only [actual_binary_total_variation]
  norm_num [biased,fair,certain]

theorem actual_source_kl_directions :
    (klDiv (costLaw biased).toMeasure (costLaw fair).toMeasure).toReal=
      (3/4)*Real.log (3/2)+(1/4)*Real.log (1/2) ∧
    (klDiv (costLaw fair).toMeasure (costLaw biased).toMeasure).toReal=
      (1/2)*Real.log (2/3)+(1/2)*Real.log 2 := by
  constructor
  all_goals rw [actual_finite_kl_sum _ _ (by intro i;fin_cases i <;> norm_num [costLaw,fair,biased])]
  all_goals norm_num [costLaw,biased,fair,Fin.sum_univ_two]

theorem actual_source_kl_log_forms :
    (klDiv (costLaw biased).toMeasure (costLaw fair).toMeasure).toReal=
      (3/4)*Real.log 3-Real.log 2 ∧
    (klDiv (costLaw fair).toMeasure (costLaw biased).toMeasure).toReal=
      Real.log 2-(1/2)*Real.log 3 := by
  rw [actual_source_kl_directions.1,actual_source_kl_directions.2]
  norm_num [Real.log_div]
  constructor <;> ring

theorem actual_support_mismatch_directions :
    (klDiv (costLaw certain).toMeasure (costLaw fair).toMeasure).toReal=Real.log 2 ∧
      klDiv (costLaw fair).toMeasure (costLaw certain).toMeasure=⊤ := by
  constructor
  · rw [actual_finite_kl_sum _ _ (by intro i;fin_cases i <;> norm_num [costLaw,fair])]
    norm_num [costLaw,certain,fair,Fin.sum_univ_two]
  · exact actual_missing_support_infinite_kl _ _ 1
      (by norm_num [costLaw,fair]) (by norm_num [costLaw,certain])

theorem source_entropy_and_kl_rounding :
    |shannonEntropy (costLaw fair)-(693147/1000000:ℝ)|<1/2000000 ∧
      |shannonEntropy (costLaw biased)-(562335/1000000:ℝ)|<1/2000000 ∧
      |(klDiv (costLaw biased).toMeasure (costLaw fair).toMeasure).toReal-
        (130812/1000000:ℝ)|<1/2000000 ∧
      |(klDiv (costLaw fair).toMeasure (costLaw biased).toMeasure).toReal-
        (143841/1000000:ℝ)|<1/2000000 := by
  rw [actual_fair_entropy,actual_biased_entropy,
    actual_source_kl_log_forms.1,actual_source_kl_log_forms.2]
  have h2l:=Real.log_two_gt_d9
  have h2u:=Real.log_two_lt_d9
  have h3l:=Real.log_three_gt_d9
  have h3u:=Real.log_three_lt_d9
  repeat' constructor
  all_goals rw [abs_lt]
  all_goals constructor <;> linarith

theorem actual_kl_directions_unequal :
    klDiv (costLaw biased).toMeasure (costLaw fair).toMeasure≠
      klDiv (costLaw fair).toMeasure (costLaw biased).toMeasure := by
  intro he
  have hn:=congrArg ENNReal.toReal he
  rw [actual_source_kl_log_forms.1,actual_source_kl_log_forms.2] at hn
  linarith [Real.log_two_gt_d9,Real.log_three_lt_d9]

theorem source_finite_direction_pinsker_and_rounding :
    totalVariation (costLaw certain) (costLaw fair)≤Real.sqrt (Real.log 2/2) ∧
      |Real.sqrt (Real.log 2/2)-(588705/1000000:ℝ)|<1/2000000 ∧
      totalVariation (costLaw certain) (costLaw fair)<Real.sqrt (Real.log 2/2) := by
  have hl:=Real.log_two_gt_d9
  have hu:=Real.log_two_lt_d9
  have hs:=Real.sq_sqrt (show 0≤Real.log 2/2 by linarith)
  have hn:=Real.sqrt_nonneg (Real.log 2/2)
  rw [source_total_variations.2]
  refine ⟨?_,?_,?_⟩
  · nlinarith
  · rw [abs_lt]
    constructor <;> nlinarith
  · nlinarith

end SafeLearning.CompleteAppliedInformation
