import Mathlib

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPDesign

def designFeature (input : Fin 3) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (if input=0 then ![1,0,0,0] else
    if input=1 then ![1/2,1/2,1/2,1/2] else ![0,1,0,0])

def designKernel : Matrix (Fin 3) (Fin 3) ℝ := Matrix.gram ℝ designFeature

theorem actual_design_kernel_positive_semidefinite : designKernel.PosSemidef :=
  Matrix.posSemidef_gram ℝ designFeature

theorem actual_design_kernel_entries :
    designKernel=!![1,1/2,0;1/2,1,1/2;0,1/2,1] := by
  ext i j
  change inner ℝ (designFeature i) (designFeature j)=_
  rw [PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [designFeature,Fin.sum_univ_four,RCLike.inner_apply,conj_trivial]

def twoObservationGram (first second : Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
  designKernel.submatrix (fun i => if i=0 then first else second)
    (fun i => if i=0 then first else second)

def realizedInformation (first second : Fin 3) : ℝ :=
  (1/2)*Real.log ((1 : Matrix (Fin 2) (Fin 2) ℝ)+twoObservationGram first second).det

def maximumInformation : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun design : Fin 3 × Fin 3 => realizedInformation design.1 design.2)

theorem actual_first_design_gram : twoObservationGram 0 1=!![1,1/2;1/2,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoObservationGram,actual_design_kernel_entries]

theorem actual_alternative_design_gram : twoObservationGram 0 2=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoObservationGram,actual_design_kernel_entries]

theorem actual_first_design_information :
    realizedInformation 0 1=(1/2)*Real.log (15/4) := by
  norm_num [realizedInformation,actual_first_design_gram,Matrix.det_fin_two]

theorem actual_alternative_design_information :
    realizedInformation 0 2=(1/2)*Real.log 4 := by
  unfold realizedInformation
  rw [actual_alternative_design_gram]
  have hd : ((1 : Matrix (Fin 2) (Fin 2) ℝ)+1).det=4 := by
    rw [Matrix.det_fin_two]
    norm_num [Matrix.add_apply,Matrix.one_apply]
  rw [hd]

theorem same_kernel_admissible_design_has_larger_information :
    realizedInformation 0 1<realizedInformation 0 2 := by
  rw [actual_first_design_information,actual_alternative_design_information]
  exact mul_lt_mul_of_pos_left (Real.log_lt_log (by norm_num) (by norm_num)) (by norm_num)

theorem realized_information_le_actual_maximum (first second : Fin 3) :
    realizedInformation first second≤ maximumInformation := by
  exact Finset.le_sup' (fun design : Fin 3 × Fin 3 => realizedInformation design.1 design.2)
    (Finset.mem_univ (first,second))

theorem displayed_information_is_not_actual_maximum :
    realizedInformation 0 1< maximumInformation :=
  lt_of_lt_of_le same_kernel_admissible_design_has_larger_information
    (realized_information_le_actual_maximum 0 2)

end SafeLearning.CompleteModulesGPDesign
