import SafeLearning.CompleteFoundationsSixMatrixSpectral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Set
open scoped BigOperators ENNReal
namespace SafeLearning.CompleteFoundationsSixMatrixNumerics
open CompleteFoundationsSixMatrixNorms CompleteFoundationsSixMatrixSpectral

theorem actual_gram_all_characteristic_roots (r : ℝ) :
    (sourceB.transpose*sourceB).charpoly.eval r=0 ↔ r=upperRoot ∨ r=lowerRoot := by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have he : (sourceB.transpose*sourceB).charpoly.eval r=r^2-30*r+100 := by
    rw [actual_source_entry_sums_gram_and_determinant.2.2.2.2.2.1,Matrix.charpoly_fin_two]
    norm_num [Matrix.det_fin_two,Matrix.trace,Fin.sum_univ_succ]
  have hf : r^2-30*r+100=(r-upperRoot)*(r-lowerRoot) := by
    dsimp [upperRoot,lowerRoot]
    linear_combination 25*hs
  rw [he,hf]
  simp only [mul_eq_zero,sub_eq_zero]

theorem actual_spectral_norm_is_first_singular_value :
    ‖twoMap‖=sourceB.toEuclideanLin.singularValues 0 := by
  rw [actual_euclidean_operator_norm,actual_first_and_second_singular_values.1]

theorem actual_sqrt_five_narrow_enclosure :
    (2.236067 : ℝ)<Real.sqrt 5 ∧ Real.sqrt 5<(2.236068 : ℝ) := by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith [Real.sqrt_nonneg 5]

theorem actual_gram_eigenvalue_roundings :
    |upperRoot-(26.18 : ℝ)|<0.005 ∧ |lowerRoot-(3.82 : ℝ)|<0.005 := by
  have hs := actual_sqrt_five_narrow_enclosure
  dsimp [upperRoot,lowerRoot]
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

theorem actual_six_norm_and_singular_value_roundings :
    |Real.sqrt 30-(5.477 : ℝ)|<0.0005 ∧
    |‖twoMap‖-(5.117 : ℝ)|<0.0005 ∧
    |sourceB.toEuclideanLin.singularValues 1-(1.954 : ℝ)|<0.0005 ∧
    |Real.sqrt 42-(6.48 : ℝ)|<0.005 := by
  have h5 := actual_sqrt_five_narrow_enclosure
  have hr := actual_roots_positive_and_relations
  have h30 : (Real.sqrt 30)^2=30 := Real.sq_sqrt (by norm_num)
  have h42 : (Real.sqrt 42)^2=42 := Real.sq_sqrt (by norm_num)
  have hu : (Real.sqrt upperRoot)^2=upperRoot := Real.sq_sqrt (le_of_lt (lt_trans hr.1 hr.2.1))
  have hl : (Real.sqrt lowerRoot)^2=lowerRoot := Real.sq_sqrt (le_of_lt hr.1)
  rw [actual_euclidean_operator_norm,actual_first_and_second_singular_values.2]
  dsimp [upperRoot,lowerRoot] at *
  refine ⟨?_,?_,?_,?_⟩
  all_goals rw [abs_lt];constructor
  all_goals nlinarith [Real.sqrt_nonneg 30,Real.sqrt_nonneg 42,
    Real.sqrt_nonneg (15+5*Real.sqrt 5),Real.sqrt_nonneg (15-5*Real.sqrt 5)]

theorem actual_source_spectral_norm_strictly_below_quoted_bounds :
    ‖twoMap‖<(5.477 : ℝ) ∧ ‖twoMap‖<(6.48 : ℝ) := by
  rw [actual_euclidean_operator_norm]
  have h5 := actual_sqrt_five_narrow_enclosure
  have hr := actual_roots_positive_and_relations
  have hu := Real.sq_sqrt (le_of_lt (lt_trans hr.1 hr.2.1))
  dsimp [upperRoot] at *
  constructor <;> nlinarith [Real.sqrt_nonneg (15+5*Real.sqrt 5)]

end SafeLearning.CompleteFoundationsSixMatrixNumerics
