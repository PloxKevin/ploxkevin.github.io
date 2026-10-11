import SafeLearning.CompleteModulesSafeOptGaussianGapPosterior
import SafeLearning.CompleteModulesGaussianExpTable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Matrix
namespace SafeLearning.CompleteModulesGaussianNumericData
open CompleteModulesSafeOptGaussianGapSeries CompleteModulesSafeOptGaussianGapGram
open CompleteModulesSafeOptGaussianGapPosterior CompleteModulesGaussianExpTable
open CompleteModulesMatrixGP

def actualGramLag (i j : Fin 11) : Fin 13 :=
  ⟨if i.val ≤ j.val then j.val-i.val else i.val-j.val,by split_ifs <;> omega⟩
def actualCrossLag (i : Fin 11) : Fin 13 := ⟨12-i.val,by omega⟩
def actualLabelLag (i : Fin 11) : Fin 13 := ⟨10-i.val,by omega⟩
def actualGramApproximation : Matrix (Fin 11) (Fin 11) ℝ :=
  Matrix.of (fun i j => actualExpApproximation (actualGramLag i j))
def actualCrossApproximation (i : Fin 11) : ℝ := actualExpApproximation (actualCrossLag i)
def actualLabelApproximation (i : Fin 11) : ℝ :=
  (actualSourceInput i-1/20)*(actualSourceInput i-3/20)*actualExpApproximation (actualLabelLag i)
def actualWeightApproximation : Fin 11 → ℝ := ![(1887700977855538966070685212890/1000000000000000000000000000000:ℝ),
  (-6243532552975041315442284534374/1000000000000000000000000000000:ℝ),
  (3485474642327348114968476838020/1000000000000000000000000000000:ℝ),
  (6674289575253204334519574861853/1000000000000000000000000000000:ℝ),
  (-2157181522067849056402301708706/1000000000000000000000000000000:ℝ),
  (-9507472040295871999340197599657/1000000000000000000000000000000:ℝ),
  (-2210902403753310679334475489363/1000000000000000000000000000000:ℝ),
  (12576290362144585518605789248466/1000000000000000000000000000000:ℝ),
  (8027375558118424883606197198144/1000000000000000000000000000000:ℝ),
  (-23744776313152967262660797587655/1000000000000000000000000000000:ℝ),
  (12212658988101292920708652624968/1000000000000000000000000000000:ℝ)]

theorem actual_source_gram_and_cross_entries_have_rigorous_table_error_bounds :
    (∀ i j, |actualGaussianGram actualSourceInput i j-actualGramApproximation i j| ≤
      1/10000000000000000000000000000000) ∧
    (∀ i, |actualGaussianCross actualSourceInput (1/5) i-actualCrossApproximation i| ≤
      1/10000000000000000000000000000000) := by
  constructor
  · intro i j
    have he := actual_thirteen_gaussian_exponential_table_entries_have_rigorous_error_bounds
      (actualGramLag i j)
    have hx : actualGaussianGram actualSourceInput i j=Real.exp (actualExpArgument (actualGramLag i j)) := by
      fin_cases i <;> fin_cases j <;>
        norm_num [actualGaussianGram,actualGaussianKernel,actualSourceInput,actualExpArgument,actualGramLag]
    rw [hx]
    exact he
  · intro i
    have he := actual_thirteen_gaussian_exponential_table_entries_have_rigorous_error_bounds
      (actualCrossLag i)
    have hx : actualGaussianCross actualSourceInput (1/5) i=Real.exp (actualExpArgument (actualCrossLag i)) := by
      fin_cases i <;>
        norm_num [actualGaussianCross,actualGaussianKernel,actualSourceInput,actualExpArgument,actualCrossLag]
    rw [hx]
    exact he

theorem actual_source_labels_have_rigorous_table_error_bounds (i : Fin 11) :
    |actualGapFunction (actualSourceInput i)-actualLabelApproximation i| ≤
      2/10000000000000000000000000000000 := by
  have he := actual_thirteen_gaussian_exponential_table_entries_have_rigorous_error_bounds
    (actualLabelLag i)
  have hx : -(actualSourceInput i)^2/2=actualExpArgument (actualLabelLag i) := by
    fin_cases i <;> norm_num [actualSourceInput,actualExpArgument,actualLabelLag]
  have hp : |(actualSourceInput i-1/20)*(actualSourceInput i-3/20)| ≤ 2 := by
    fin_cases i <;> norm_num [actualSourceInput]
  rw [actualGapFunction,actualLabelApproximation,hx,← mul_sub,abs_mul]
  exact le_trans (mul_le_mul hp he (abs_nonneg _) (by norm_num)) (by norm_num)

theorem actual_rational_approximate_weights_have_small_true_table_system_residuals :
    (∀ i, |actualCrossApproximation i-
      (ridgeMatrix actualGramApproximation (1/10000000000) *ᵥ actualWeightApproximation) i| ≤
      1/100000000000000000000000000000) ∧
    (∑ i, |actualWeightApproximation i|) ≤ 90 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [actualCrossApproximation,actualCrossLag,ridgeMatrix,
      actualGramApproximation,actualGramLag,actualExpApproximation,actualWeightApproximation,
      Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.one_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · norm_num [actualWeightApproximation,Fin.sum_univ_succ]

theorem actual_rational_approximate_prediction_and_variance_have_tight_enclosures :
    (7347943/1000000000:ℝ) < (∑ i, actualWeightApproximation i*actualLabelApproximation i) ∧
      (∑ i, actualWeightApproximation i*actualLabelApproximation i) < 7347944/1000000000 ∧
      (1935340/10000000000000:ℝ) < 1-(∑ i, actualCrossApproximation i*actualWeightApproximation i) ∧
      1-(∑ i, actualCrossApproximation i*actualWeightApproximation i) < 1935342/10000000000000 := by
  norm_num [actualWeightApproximation,actualLabelApproximation,actualCrossApproximation,
    actualLabelLag,actualCrossLag,actualExpApproximation,actualSourceInput,Fin.sum_univ_succ]

end SafeLearning.CompleteModulesGaussianNumericData
