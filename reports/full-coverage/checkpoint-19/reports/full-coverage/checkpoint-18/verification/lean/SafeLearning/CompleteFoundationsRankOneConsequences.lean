import SafeLearning.CompleteFoundationsRankOneSchur

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Matrix

namespace SafeLearning.CompleteFoundationsRankOneConsequences

open SafeLearning.CompleteFoundationsRankOneSchur

theorem actual_outer_unit_projection_and_residual :
    Matrix.vecMulVec unitDirection unitDirection=rangeProjection ∧
      sourceB-Matrix.vecMulVec unitDirection unitDirection *ᵥ sourceB=![4/5,-2/5] := by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 5≠0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have he : Matrix.vecMulVec unitDirection unitDirection=rangeProjection := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unitDirection,rangeProjection,Matrix.vecMulVec] <;> field_simp <;> nlinarith
  refine ⟨he,?_⟩
  rw [he]
  ext i
  fin_cases i <;>
    norm_num [sourceB,rangeProjection,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_nullspace_range_condition_equivalence (β : Fin 2 → ℝ) :
    (1-sourceC*sourcePlus) *ᵥ β=0 ↔ ∃ s : ℝ,β=s • direction := by
  rw [actual_range_projection.1]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [rangeProjection,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0
    refine ⟨β 0,?_⟩
    ext i
    fin_cases i <;> simp [direction] <;> linarith
  · rintro ⟨s,rfl⟩
    ext i
    fin_cases i <;>
      norm_num [rangeProjection,direction,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
        Matrix.one_apply,Fin.succ] <;> ring

end SafeLearning.CompleteFoundationsRankOneConsequences
