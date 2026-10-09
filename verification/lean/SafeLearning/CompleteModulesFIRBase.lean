import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesFIRBase

/-- The state is the genuine previous input of the two-tap FIR filter. -/
def actualFIRMemory (input : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | time+1 => input time

def actualFIROutput (currentGain delayedGain state input : ℝ) : ℝ := delayedGain*state+currentGain*input

def actualFIRResponse (currentGain delayedGain : ℝ) (input : ℕ → ℝ) (time : ℕ) : ℝ :=
  actualFIROutput currentGain delayedGain (actualFIRMemory input time) (input time)

theorem actual_fir_state_space_realization (currentGain delayedGain : ℝ) (input : ℕ → ℝ) :
    actualFIRMemory input 0=0 ∧
    (∀ time,actualFIRMemory input (time+1)=0*actualFIRMemory input time+1*input time) ∧
    actualFIRResponse currentGain delayedGain input 0=currentGain*input 0 ∧
    (∀ time,actualFIRResponse currentGain delayedGain input (time+1)=
      delayedGain*input time+currentGain*input (time+1)) := by
  simp [actualFIRMemory,actualFIRResponse,actualFIROutput]

def actualFIRStateMatrix : Matrix (Fin 1) (Fin 1) ℝ := 0

theorem actual_fir_state_matrix_is_nilpotent_of_index_one :
    actualFIRStateMatrix^1=0 ∧ actualFIRStateMatrix^0≠0 := by
  constructor
  · simp [actualFIRStateMatrix]
  · intro h
    have he := congrArg (fun m : Matrix (Fin 1) (Fin 1) ℝ => m 0 0) h
    norm_num at he

def actualFIRGramian (gain freeParameter regularizer : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  ∑ power ∈ Finset.range 1,actualFIRStateMatrix^power*
    ((gain^2)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ)+
      (freeParameter • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ*
        (freeParameter • (1 : Matrix (Fin 1) (Fin 1) ℝ))+
      regularizer • (1 : Matrix (Fin 1) (Fin 1) ℝ))*(actualFIRStateMatrixᵀ)^power

theorem actual_fir_controllability_gramian_formula (gain freeParameter regularizer : ℝ) :
    actualFIRGramian gain freeParameter regularizer=
      ((1/gain^2+freeParameter^2+regularizer):ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext row column
  fin_cases row
  fin_cases column
  simp [actualFIRGramian,actualFIRStateMatrix,Matrix.smul_mul,Matrix.mul_smul]
  ring

def actualFIRStorage (gain freeParameter regularizer : ℝ) : ℝ :=
  (1/gain^2+freeParameter^2+regularizer)⁻¹

theorem actual_fir_inverse_gramian_storage_formula
    (gain freeParameter regularizer : ℝ) (hgain : 0 < gain) (hregularizer : 0 ≤ regularizer) :
    actualFIRStorage gain freeParameter regularizer=
      gain^2/(1+gain^2*(freeParameter^2+regularizer)) := by
  unfold actualFIRStorage
  have hg : 0 < gain^2 := sq_pos_of_pos hgain
  have hd : 0 < 1/gain^2+freeParameter^2+regularizer := by positivity
  have hh : 0 < 1+gain^2*(freeParameter^2+regularizer) := by positivity
  field_simp
  <;> ring

theorem actual_fir_storage_is_actual_matrix_inverse
    (gain freeParameter regularizer : ℝ) (hgain : 0 < gain) (hregularizer : 0 ≤ regularizer) :
    (actualFIRGramian gain freeParameter regularizer)⁻¹=
      actualFIRStorage gain freeParameter regularizer • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [actual_fir_controllability_gramian_formula]
  have hd : 0 < 1/gain^2+freeParameter^2+regularizer := by positivity
  have hn : (gain^2)⁻¹+freeParameter^2+regularizer≠0 := by simpa only [one_div] using hd.ne'
  apply Matrix.inv_eq_right_inv
  simp [actualFIRStorage,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hn]

theorem actual_fir_storage_strictly_between_zero_and_gain_squared
    (gain freeParameter regularizer : ℝ) (hgain : 0 < gain)
    (hregularizer : 0 ≤ regularizer) (hstrict : 0 < freeParameter^2+regularizer) :
    0 < actualFIRStorage gain freeParameter regularizer ∧
      actualFIRStorage gain freeParameter regularizer < gain^2 := by
  rw [actual_fir_inverse_gramian_storage_formula gain freeParameter regularizer hgain hregularizer]
  have hg : 0 < gain^2 := sq_pos_of_pos hgain
  have hd : 0 < 1+gain^2*(freeParameter^2+regularizer) := by positivity
  constructor
  · positivity
  · rw [div_lt_iff₀ hd]
    nlinarith [mul_pos hg hstrict]

def actualFIRDissipationMatrix (gain storage : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![storage,gain^2]-(!![0,(1:ℝ)])ᵀ*
    (storage • (1 : Matrix (Fin 1) (Fin 1) ℝ))*!![0,(1:ℝ)]

theorem actual_fir_dissipation_matrix_is_source_diagonal (gain storage : ℝ) :
    actualFIRDissipationMatrix gain storage=Matrix.diagonal ![storage,gain^2-storage] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [actualFIRDissipationMatrix,Matrix.mul_apply,Fin.sum_univ_one]

theorem actual_fir_dissipation_matrix_is_positive_definite
    (gain freeParameter regularizer : ℝ) (hgain : 0 < gain)
    (hregularizer : 0 ≤ regularizer) (hstrict : 0 < freeParameter^2+regularizer) :
    (actualFIRDissipationMatrix gain (actualFIRStorage gain freeParameter regularizer)).PosDef := by
  rw [actual_fir_dissipation_matrix_is_source_diagonal,Matrix.posDef_diagonal_iff]
  have hs := actual_fir_storage_strictly_between_zero_and_gain_squared gain freeParameter regularizer hgain hregularizer hstrict
  intro coordinate
  fin_cases coordinate
  · exact hs.1
  · exact sub_pos.mpr hs.2

theorem actual_fir_zero_free_parameter_storage_endpoint (gain : ℝ) (hgain : 0 < gain) :
    actualFIRStorage gain 0 0=gain^2 := by
  rw [actual_fir_inverse_gramian_storage_formula gain 0 0 hgain (by norm_num)]
  simp

theorem actual_fir_zero_free_parameter_certificate_is_only_semidefinite (gain : ℝ) (hgain : 0 < gain) :
    (actualFIRDissipationMatrix gain (actualFIRStorage gain 0 0)).PosSemidef ∧
      ¬(actualFIRDissipationMatrix gain (actualFIRStorage gain 0 0)).PosDef := by
  rw [actual_fir_zero_free_parameter_storage_endpoint gain hgain,
    actual_fir_dissipation_matrix_is_source_diagonal]
  constructor
  · rw [Matrix.posSemidef_diagonal_iff]
    intro coordinate
    fin_cases coordinate <;> simp [sq_nonneg]
  · rw [Matrix.posDef_diagonal_iff]
    intro h
    have hc := h 1
    simp at hc

theorem actual_fir_source_unit_parameters :
    actualFIRGramian 1 1 0=(2:ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
    actualFIRStorage 1 1 0=(1/2:ℝ) ∧
    actualFIRDissipationMatrix 1 (actualFIRStorage 1 1 0)=
      (1/2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [actual_fir_controllability_gramian_formula]
  norm_num [actualFIRStorage]
  rw [actual_fir_dissipation_matrix_is_source_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num

end SafeLearning.CompleteModulesFIRBase
