import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesDesignFiniteGramian

def sourceA : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;0,0]
def sourceB : Fin 2 → ℝ := ![0,1]
def sourceInputCovariance : Matrix (Fin 2) (Fin 2) ℝ := Matrix.vecMulVec sourceB sourceB
def sourceGramianTerm (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  sourceA^k*sourceInputCovariance*(sourceAᵀ)^k
def sourceGramian : Matrix (Fin 2) (Fin 2) ℝ := ∑' k:ℕ, sourceGramianTerm k

theorem actual_source_nilpotence_input_covariance_and_reached_column :
    sourceA^2=0 ∧ sourceA≠0 ∧ sourceInputCovariance=diagonal ![(0:ℝ),1] ∧
      sourceA *ᵥ sourceB=![(1:ℝ),0] := by
  refine ⟨?_,?_,?_,?_⟩
  · ext i j;fin_cases i <;>fin_cases j <;>norm_num [sourceA,pow_two,Matrix.mul_apply,Fin.sum_univ_two]
  · intro h;have hh:=congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ=>A 0 1) h;norm_num [sourceA] at hh
  · ext i j;fin_cases i <;>fin_cases j <;>norm_num [sourceInputCovariance,sourceB,Matrix.vecMulVec,diagonal_apply]
  · ext i;fin_cases i <;>norm_num [sourceA,sourceB,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem actual_source_all_later_gramian_terms_vanish (k : ℕ) (hk : 2≤k) :
    sourceGramianTerm k=0 := by
  have hp : sourceA^k=0 := pow_eq_zero_of_le hk actual_source_nilpotence_input_covariance_and_reached_column.1
  simp [sourceGramianTerm,hp]

theorem actual_source_two_initial_terms_and_genuine_infinite_sum :
    sourceGramianTerm 0=diagonal ![(0:ℝ),1] ∧
      sourceGramianTerm 1=diagonal ![(1:ℝ),0] ∧ sourceGramian=1 := by
  have h0 : sourceGramianTerm 0=diagonal ![(0:ℝ),1] := by
    simpa [sourceGramianTerm] using actual_source_nilpotence_input_covariance_and_reached_column.2.2.1
  have h1 : sourceGramianTerm 1=diagonal ![(1:ℝ),0] := by
    ext i j;fin_cases i <;>fin_cases j <;>norm_num [sourceGramianTerm,sourceA,sourceInputCovariance,
      sourceB,Matrix.vecMulVec,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.transpose_apply,
      Fin.sum_univ_two,diagonal_apply]
  refine ⟨h0,h1,?_⟩
  have hs : sourceGramian=∑ k ∈ Finset.range 2,sourceGramianTerm k := by
    apply tsum_eq_sum
    intro k hk
    exact actual_source_all_later_gramian_terms_vanish k (by
      simp only [Finset.mem_range] at hk
      omega)
  rw [hs]
  norm_num [Finset.sum_range_succ,h0,h1]
  ext i j;fin_cases i <;>fin_cases j <;>norm_num [diagonal_apply,Matrix.one_apply]

theorem actual_source_gramian_equation_positive_definiteness_and_inverse :
    sourceGramian=sourceA*sourceGramian*sourceAᵀ+sourceInputCovariance ∧
      sourceGramian.PosDef ∧ IsUnit sourceGramian ∧ sourceGramian⁻¹=1 := by
  have hg:=actual_source_two_initial_terms_and_genuine_infinite_sum.2.2
  rw [hg]
  refine ⟨?_,Matrix.PosDef.one,isUnit_one,by simp⟩
  ext i j;fin_cases i <;>fin_cases j <;>norm_num [sourceA,sourceInputCovariance,sourceB,
    Matrix.vecMulVec,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.transpose_apply,
    Fin.sum_univ_two,Matrix.one_apply]

theorem actual_source_controllability_columns_are_independent :
    IsUnit (!![sourceB 0,(sourceA *ᵥ sourceB) 0;
      sourceB 1,(sourceA *ᵥ sourceB) 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  norm_num [sourceB,actual_source_nilpotence_input_covariance_and_reached_column.2.2.2,Matrix.det_fin_two]

end SafeLearning.CompleteModulesDesignFiniteGramian
