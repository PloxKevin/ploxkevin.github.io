import Mathlib

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology ENNReal

namespace SafeLearning.CompleteStudyGuideModels

theorem genuine_algebra_check (x : ℝ) :
    (2 * x + 3 = 7 ↔ 2 * x = 4) ∧ (2 * x = 4 ↔ x = 2) ∧ 2 * (2 : ℝ) + 3 = 7 := by
  constructor
  · constructor <;> intro h <;> linarith
  constructor
  · constructor <;> intro h <;> linarith
  norm_num

def vector (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a, b]
def oneNorm (x : EuclideanSpace ℝ (Fin 2)) : ℝ := ∑ i, |x i|

theorem genuine_Euclidean_coordinate_norm (a b : ℝ) :
    ‖vector a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, vector, Fin.sum_univ_two]

theorem actual_distinct_source_norms :
    ‖vector 3 4‖ = 5 ∧ oneNorm (vector 3 4) = 7 ∧
      (3 : ℝ) ^ 2 + 4 ^ 2 = 25 ∧ Real.sqrt 25 = 5 := by
  have hs := genuine_Euclidean_coordinate_norm 3 4
  have hn := norm_nonneg (vector 3 4)
  constructor
  · nlinarith
  constructor
  · norm_num [oneNorm, vector, Fin.sum_univ_two]
  constructor
  · norm_num
  norm_num

theorem genuine_matrix_row_check :
    (!![1, 2; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 3] = ![7, 3] := by
  ext i
  fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two]

theorem genuine_square_derivative (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

theorem actual_value_and_derivative :
    (3 : ℝ) ^ 2 = 9 ∧ HasDerivAt (fun y : ℝ => y ^ 2) 6 3 := by
  constructor
  · norm_num
  convert genuine_square_derivative 3 using 1
  norm_num

theorem true_first_order_error_and_limit :
    (∀ h : ℝ, (3 + h) ^ 2 - 9 - 6 * h = h ^ 2) ∧
      Tendsto (fun h : ℝ => ((3 + h) ^ 2 - 9 - 6 * h) / h) (𝓝 0) (𝓝 0) := by
  have he : ∀ h : ℝ, (3 + h) ^ 2 - 9 - 6 * h = h ^ 2 := by intro h; ring
  refine ⟨he, ?_⟩
  have hf : (fun h : ℝ => ((3 + h) ^ 2 - 9 - 6 * h) / h) = id := by
    funext h
    rw [he]
    by_cases hh : h = 0
    · simp [hh]
    · simp only [id_eq]
      field_simp
  rw [hf]
  exact tendsto_id

theorem genuine_independent_coin_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H K : Set Ω)
    (hind : IndepSet H K μ) (hH : (μ H).toReal = 1 / 4)
    (hK : (μ K).toReal = 1 / 4) :
    (μ (H ∩ K)).toReal = 1 / 16 := by
  rw [hind.measure_inter_eq_mul, ENNReal.toReal_mul, hH, hK]
  norm_num

theorem genuine_general_independent_joint_rule {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H K : Set Ω) (hind : IndepSet H K μ) :
    (μ (H ∩ K)).toReal = (μ H).toReal * (μ K).toReal := by
  rw [hind.measure_inter_eq_mul, ENNReal.toReal_mul]

theorem genuine_general_complement_rule {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Set Ω) (hHm : MeasurableSet H) :
    (μ H).toReal + (μ Hᶜ).toReal = 1 := by
  have hc := measureReal_add_measureReal_compl (μ := μ) hHm
  change (μ H).toReal + (μ Hᶜ).toReal = (μ Set.univ).toReal at hc
  simpa only [measure_univ, ENNReal.toReal_one] using hc

theorem genuine_complementary_coin_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Set Ω) (hHm : MeasurableSet H)
    (hH : (μ H).toReal = 1 / 4) : (μ Hᶜ).toReal = 3 / 4 := by
  have hc := measureReal_add_measureReal_compl (μ := μ) hHm
  change (μ H).toReal + (μ Hᶜ).toReal = (μ Set.univ).toReal at hc
  simp only [measure_univ, ENNReal.toReal_one] at hc
  linarith

theorem genuine_dependent_counterexample {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Set Ω)
    (hH : (μ H).toReal = 1 / 4) :
    (μ (H ∩ H)).toReal = 1 / 4 ∧ (μ (H ∩ H)).toReal ≠ 1 / 16 := by
  simp only [inter_self, hH]
  norm_num

end SafeLearning.CompleteStudyGuideModels
