import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix Set
open scoped BigOperators ENNReal
namespace SafeLearning.CompleteFoundationsSixMatrixNorms
abbrev E := EuclideanSpace ℝ (Fin 2)
abbrev One := PiLp 1 (fun _ : Fin 2 => ℝ)
abbrev InfinitySpace := PiLp ∞ (fun _ : Fin 2 => ℝ)
def sourceB : Matrix (Fin 2) (Fin 2) ℝ := !![1,-2;3,4]
def oneMap : One →L[ℝ] One := (sourceB.toLpLin 1 1).toContinuousLinearMap
def mixedOneMap : One →L[ℝ] InfinitySpace := (sourceB.toLpLin 1 ∞).toContinuousLinearMap
def mixedTwoMap : E →L[ℝ] InfinitySpace := (sourceB.toLpLin 2 ∞).toContinuousLinearMap

theorem actual_two_coordinate_supnorm (a b : ℝ) : ‖(![a,b] : Fin 2 → ℝ)‖=max |a| |b| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg a))).mpr
    intro i; fin_cases i
    · simpa using le_max_left |a| |b|
    · simpa using le_max_right |a| |b|
  · apply max_le
    · simpa using norm_le_pi_norm (![a,b] : Fin 2 → ℝ) (0 : Fin 2)
    · simpa using norm_le_pi_norm (![a,b] : Fin 2 → ℝ) (1 : Fin 2)

theorem actual_source_matrix_action (x : Fin 2 → ℝ) : sourceB *ᵥ x=![x 0-2*x 1,3*x 0+4*x 1] := by
  ext i; fin_cases i <;> simp [sourceB,mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem actual_source_entry_sums_gram_and_determinant :
    (∑ i : Fin 2,|sourceB i 0|)=4 ∧ (∑ i : Fin 2,|sourceB i 1|)=6 ∧
    (∑ j : Fin 2,|sourceB 0 j|)=3 ∧ (∑ j : Fin 2,|sourceB 1 j|)=7 ∧
    (∑ i : Fin 2,∑ j : Fin 2,sourceB i j^2)=30 ∧
    sourceB.transpose*sourceB=!![10,10;10,20] ∧ sourceB.det=10 := by
  refine ⟨by norm_num [sourceB,Fin.sum_univ_succ],by norm_num [sourceB,Fin.sum_univ_succ],
    by norm_num [sourceB,Fin.sum_univ_succ],by norm_num [sourceB,Fin.sum_univ_succ],
    by norm_num [sourceB,Fin.sum_univ_succ],?_,by norm_num [sourceB,Matrix.det_fin_two]⟩
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [sourceB,transpose_apply,mul_apply,Fin.sum_univ_succ]

theorem actual_one_map_coordinates (x : One) : oneMap x=WithLp.toLp 1 ![x 0-2*x 1,3*x 0+4*x 1] := by
  ext i
  change (sourceB *ᵥ (x : Fin 2 → ℝ)) i=_
  rw [actual_source_matrix_action]

theorem actual_one_map_spectral_one_norm : ‖oneMap‖=6 := by
  apply le_antisymm
  · apply oneMap.opNorm_le_bound (by norm_num)
    intro x
    rw [actual_one_map_coordinates]
    simp only [PiLp.norm_eq_of_L1,Fin.sum_univ_two,PiLp.toLp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Real.norm_eq_abs]
    have h1 : |x 0-2*x 1|≤|x 0|+2*|x 1| := by
      simpa [sub_eq_add_neg,abs_neg,abs_mul] using abs_add_le (x 0) (-(2*x 1))
    have h2 : |3*x 0+4*x 1|≤3*|x 0|+4*|x 1| := by
      simpa [abs_mul] using abs_add_le (3*x 0) (4*x 1)
    nlinarith [abs_nonneg (x 0)]
  · let x : One := WithLp.toLp 1 ![0,1]
    have hx : ‖x‖=1 := by norm_num [x,PiLp.norm_eq_of_L1,Fin.sum_univ_succ]
    have ho : ‖oneMap x‖=6 := by
      rw [actual_one_map_coordinates]
      norm_num [x,PiLp.norm_eq_of_L1,Fin.sum_univ_succ]
    have hb := oneMap.le_opNorm x
    rwa [hx,ho,mul_one] at hb

section InfinityNorm
open scoped Matrix.Norms.Operator
theorem actual_matrix_infinity_norm : ‖sourceB‖=7 := by
  norm_num [Matrix.linfty_opNorm_def,sourceB,Fin.sum_univ_succ,Finset.univ_fin2]
end InfinityNorm
section FrobeniusNorm
open scoped Matrix.Norms.Frobenius
theorem actual_matrix_frobenius_norm : ‖sourceB‖=Real.sqrt 30 := by
  rw [Matrix.frobenius_norm_def]
  norm_num [sourceB,Fin.sum_univ_succ,Real.norm_eq_abs,Real.sqrt_eq_rpow]
end FrobeniusNorm

theorem actual_mixed_one_coordinates (x : One) : mixedOneMap x=WithLp.toLp ∞ ![x 0-2*x 1,3*x 0+4*x 1] := by
  ext i
  change (sourceB *ᵥ (x : Fin 2 → ℝ)) i=_
  rw [actual_source_matrix_action]

theorem actual_mixed_one_to_infinity_norm : ‖mixedOneMap‖=4 := by
  apply le_antisymm
  · apply mixedOneMap.opNorm_le_bound (by norm_num)
    intro x
    rw [actual_mixed_one_coordinates,PiLp.norm_toLp,actual_two_coordinate_supnorm]
    simp only [PiLp.norm_eq_of_L1,Fin.sum_univ_two,Real.norm_eq_abs]
    apply max_le
    · have h : |x 0-2*x 1|≤|x 0|+2*|x 1| := by
        simpa [sub_eq_add_neg,abs_neg,abs_mul] using abs_add_le (x 0) (-(2*x 1))
      nlinarith [abs_nonneg (x 0),abs_nonneg (x 1)]
    · have h : |3*x 0+4*x 1|≤3*|x 0|+4*|x 1| := by
        simpa [abs_mul] using abs_add_le (3*x 0) (4*x 1)
      nlinarith [abs_nonneg (x 0)]
  · let x : One := WithLp.toLp 1 ![0,1]
    have hx : ‖x‖=1 := by norm_num [x,PiLp.norm_eq_of_L1,Fin.sum_univ_succ]
    have ho : ‖mixedOneMap x‖=4 := by
      rw [actual_mixed_one_coordinates,PiLp.norm_toLp,actual_two_coordinate_supnorm]
      norm_num [x]
    have hb := mixedOneMap.le_opNorm x
    rwa [hx,ho,mul_one] at hb

theorem actual_mixed_two_coordinates (x : E) : mixedTwoMap x=WithLp.toLp ∞ ![x 0-2*x 1,3*x 0+4*x 1] := by
  ext i
  change (sourceB *ᵥ (x : Fin 2 → ℝ)) i=_
  rw [actual_source_matrix_action]

theorem actual_two_coordinate_euclidean_norm_squared (x : E) : ‖x‖^2=(x 0)^2+(x 1)^2 := by
  rw [←real_inner_self_eq_norm_sq]
  change (∑ i : Fin 2,x i*x i)=(x 0)^2+(x 1)^2
  simp [Fin.sum_univ_succ];ring

theorem actual_mixed_two_to_infinity_norm : ‖mixedTwoMap‖=5 := by
  apply le_antisymm
  · apply mixedTwoMap.opNorm_le_bound (by norm_num)
    intro x
    rw [actual_mixed_two_coordinates,PiLp.norm_toLp,actual_two_coordinate_supnorm]
    have hn := actual_two_coordinate_euclidean_norm_squared x
    apply max_le
    · apply le_of_sq_le_sq _ (by positivity)
      rw [sq_abs]
      nlinarith [sq_nonneg (2*x 0+x 1)]
    · apply le_of_sq_le_sq _ (by positivity)
      rw [sq_abs]
      nlinarith [sq_nonneg (4*x 0-3*x 1)]
  · let x : E := WithLp.toLp 2 ![3/5,4/5]
    have hn : ‖x‖=1 := by
      have h : ‖x‖^2=1 := by
        rw [actual_two_coordinate_euclidean_norm_squared]
        norm_num [x]
      nlinarith [norm_nonneg x]
    have ho : ‖mixedTwoMap x‖=5 := by
      rw [actual_mixed_two_coordinates,PiLp.norm_toLp,actual_two_coordinate_supnorm]
      norm_num [x]
    have hb := mixedTwoMap.le_opNorm x
    rwa [hn,ho,mul_one] at hb

theorem actual_source_row_lengths_and_maximum_entry :
    ‖(WithLp.toLp 2 (sourceB 0) : E)‖=Real.sqrt 5 ∧
    ‖(WithLp.toLp 2 (sourceB 1) : E)‖=5 ∧
    max (Real.sqrt 5) 5=5 ∧
    IsGreatest {entry : ℝ | ∃ i j,entry=|sourceB i j|} 4 := by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  refine ⟨?_,?_,?_,⟨⟨1,1,by norm_num [sourceB]⟩,?_⟩⟩
  · have hn : ‖(WithLp.toLp 2 (sourceB 0) : E)‖^2=5 := by
      rw [actual_two_coordinate_euclidean_norm_squared]
      norm_num [sourceB]
    nlinarith [norm_nonneg (WithLp.toLp 2 (sourceB 0)),Real.sqrt_nonneg 5]
  · have hn : ‖(WithLp.toLp 2 (sourceB 1) : E)‖^2=25 := by
      rw [actual_two_coordinate_euclidean_norm_squared]
      norm_num [sourceB]
    nlinarith [norm_nonneg (WithLp.toLp 2 (sourceB 1))]
  · apply max_eq_right
    nlinarith [Real.sqrt_nonneg 5]
  · rintro e ⟨i,j,rfl⟩
    fin_cases i <;> fin_cases j <;> norm_num [sourceB]

end SafeLearning.CompleteFoundationsSixMatrixNorms
