import SafeLearning.CompleteModulesFIRBase
import SafeLearning.CompleteModulesLipSDP

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesFIROperator
open CompleteModulesFIRBase CompleteModulesLipSDP

variable {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]

def actualUnitRow (unitVector : K → ℝ) : Matrix (Fin 1) K ℝ := Matrix.replicateRow (Fin 1) unitVector

theorem actual_unit_vector_complement_is_positive_semidefinite
    (unitVector : K → ℝ) (hunit : ∑ coordinate,unitVector coordinate^2=1) :
    ((1 : Matrix K K ℝ)-(actualUnitRow unitVector)ᵀ*actualUnitRow unitVector).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · exact Matrix.isHermitian_one.sub (Matrix.posSemidef_conjTranspose_mul_self (actualUnitRow unitVector)).isHermitian
  · intro vector
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ unitVector vector
    rw [hunit,one_mul] at hc
    have hg := quadratic_gram (actualUnitRow unitVector) vector
    simp only [actualUnitRow,Matrix.mulVec,Matrix.replicateRow_apply,Fin.sum_univ_one] at hg
    simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.one_mulVec]
    change 0 ≤ (∑ coordinate,vector coordinate*vector coordinate)-quadratic ((actualUnitRow unitVector)ᵀ*actualUnitRow unitVector) vector
    simp only [actualUnitRow]
    rw [hg]
    simpa only [pow_two,dotProduct] using sub_nonneg.mpr hc

theorem actual_unit_row_cholesky_certificate_identity
    (unitVector : K → ℝ) (factor : Matrix K N ℝ) :
    factorᵀ*factor-(actualUnitRow unitVector*factor)ᵀ*(actualUnitRow unitVector*factor)=
      factorᵀ*((1 : Matrix K K ℝ)-(actualUnitRow unitVector)ᵀ*actualUnitRow unitVector)*factor := by
  simp only [Matrix.transpose_mul,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.mul_assoc]

theorem actual_unit_row_cholesky_certificate_is_positive_semidefinite
    (unitVector : K → ℝ) (hunit : ∑ coordinate,unitVector coordinate^2=1)
    (factor : Matrix K N ℝ) :
    (factorᵀ*factor-(actualUnitRow unitVector*factor)ᵀ*(actualUnitRow unitVector*factor)).PosSemidef := by
  rw [actual_unit_row_cholesky_certificate_identity]
  exact (actual_unit_vector_complement_is_positive_semidefinite unitVector hunit).conjTranspose_mul_mul_same factor

def actualFIRKernelRow (currentGain delayedGain : ℝ) : Matrix (Fin 1) (Fin 2) ℝ := !![delayedGain,currentGain]

theorem actual_fir_certificate_has_literal_dissipation_quadratic
    (gain storage currentGain delayedGain state input : ℝ) :
    quadratic (actualFIRDissipationMatrix gain storage-
      (actualFIRKernelRow currentGain delayedGain)ᵀ*actualFIRKernelRow currentGain delayedGain) ![state,input]=
      storage*state^2+(gain^2-storage)*input^2-(actualFIROutput currentGain delayedGain state input)^2 := by
  rw [actual_fir_dissipation_matrix_is_source_diagonal,quadratic_sub,quadratic_gram]
  simp [quadratic,actualFIRKernelRow,actualFIROutput,Matrix.mulVec,Matrix.mul_apply,
    Fin.sum_univ_two,Fin.sum_univ_one,dotProduct]
  ring

theorem actual_fir_certificate_implies_storage_dissipation
    (gain storage currentGain delayedGain : ℝ)
    (hcertificate : (actualFIRDissipationMatrix gain storage-
      (actualFIRKernelRow currentGain delayedGain)ᵀ*actualFIRKernelRow currentGain delayedGain).PosSemidef)
    (state input : ℝ) :
    storage*input^2-storage*state^2 ≤ gain^2*input^2-(actualFIROutput currentGain delayedGain state input)^2 := by
  have h := hcertificate.dotProduct_mulVec_nonneg ![state,input]
  change 0 ≤ quadratic _ ![state,input] at h
  rw [actual_fir_certificate_has_literal_dissipation_quadratic] at h
  nlinarith

theorem actual_zero_initial_fir_finite_horizon_energy_bound
    (gain storage currentGain delayedGain : ℝ) (hstorage : 0 ≤ storage)
    (hcertificate : (actualFIRDissipationMatrix gain storage-
      (actualFIRKernelRow currentGain delayedGain)ᵀ*actualFIRKernelRow currentGain delayedGain).PosSemidef)
    (input : ℕ → ℝ) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,(actualFIRResponse currentGain delayedGain input time)^2)+
        storage*(actualFIRMemory input horizon)^2 ≤
      gain^2*(∑ time ∈ Finset.range horizon,(input time)^2) := by
  induction horizon with
  | zero => simp [actualFIRMemory]
  | succ horizon ih =>
    have h := actual_fir_certificate_implies_storage_dissipation gain storage currentGain delayedGain hcertificate
      (actualFIRMemory input horizon) (input horizon)
    simp only [Finset.sum_range_succ,actualFIRMemory,actualFIRResponse] at *
    nlinarith

theorem actual_zero_initial_fir_output_energy_bound
    (gain storage currentGain delayedGain : ℝ) (hstorage : 0 ≤ storage)
    (hcertificate : (actualFIRDissipationMatrix gain storage-
      (actualFIRKernelRow currentGain delayedGain)ᵀ*actualFIRKernelRow currentGain delayedGain).PosSemidef)
    (input : ℕ → ℝ) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,(actualFIRResponse currentGain delayedGain input time)^2) ≤
      gain^2*(∑ time ∈ Finset.range horizon,(input time)^2) := by
  have h := actual_zero_initial_fir_finite_horizon_energy_bound gain storage currentGain delayedGain hstorage hcertificate input horizon
  have hs := mul_nonneg hstorage (sq_nonneg (actualFIRMemory input horizon))
  linarith

end SafeLearning.CompleteModulesFIROperator
