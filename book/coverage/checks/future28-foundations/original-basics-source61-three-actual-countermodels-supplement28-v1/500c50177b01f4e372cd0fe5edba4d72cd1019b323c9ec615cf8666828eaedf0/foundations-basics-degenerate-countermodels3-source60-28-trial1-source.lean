import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace SafeLearning.CompleteFoundationsBasicsDegenerateCountermodels28

theorem actual_zero_normal_affine_level_is_the_real_line_of_infinite_volume :
    {x : ℝ | (0 : ℝ)*x+0=0}=Set.univ ∧
      volume {x : ℝ | (0 : ℝ)*x+0=0}=∞ := by
  have h : {x : ℝ | (0 : ℝ)*x+0=0}=Set.univ := by ext x; simp
  exact ⟨h, by rw [h]; exact volume_univ⟩

theorem actual_zero_dimensional_singleton_has_volume_one :
    volume ({0} : Set (EuclideanSpace ℝ (Fin 0)))=1 := by
  rw [volume_euclideanSpace_eq_dirac]
  simp

theorem actual_zero_dimensional_whole_space_is_compact :
    IsCompact (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := by
  have h : (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))={0} := by
    ext x
    simp only [Set.mem_univ,Set.mem_singleton_iff,true_iff]
    exact Subsingleton.elim x 0
  rw [h]
  exact isCompact_singleton

end SafeLearning.CompleteFoundationsBasicsDegenerateCountermodels28
