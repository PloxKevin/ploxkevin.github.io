import SafeLearning.CompleteFoundationsSixMatrixNorms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Set
open scoped BigOperators ENNReal Matrix.Norms.Operator
namespace SafeLearning.CompleteFoundationsSixMatrixComplex
open CompleteFoundationsSixMatrixNorms

def complexB : Matrix (Fin 2) (Fin 2) ℂ := sourceB.map Complex.ofReal
def eigenPlus : ℂ := ⟨5/2,Real.sqrt 15/2⟩
def eigenMinus : ℂ := ⟨5/2,-Real.sqrt 15/2⟩

theorem actual_complex_characteristic_polynomial (z : ℂ) :
    complexB.charpoly.eval z=z^2-5*z+10 := by
  rw [Matrix.charpoly_fin_two]
  norm_num [complexB,sourceB,Matrix.det_fin_two,Matrix.trace,Fin.sum_univ_succ]

theorem actual_complex_root_factorization (z : ℂ) :
    z^2-5*z+10=(z-eigenPlus)*(z-eigenMinus) := by
  have hs : (Real.sqrt 15)^2=15 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [eigenPlus,eigenMinus,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,pow_two] <;> nlinarith

theorem actual_all_complex_characteristic_roots (z : ℂ) :
    complexB.charpoly.eval z=0 ↔ z=eigenPlus ∨ z=eigenMinus := by
  rw [actual_complex_characteristic_polynomial,actual_complex_root_factorization]
  simp only [mul_eq_zero,sub_eq_zero]

theorem actual_complete_complex_spectrum (z : ℂ) :
    z ∈ spectrum ℂ complexB ↔ z=eigenPlus ∨ z=eigenMinus := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  exact actual_all_complex_characteristic_roots z

theorem actual_both_source_values_are_eigenvalues :
    Module.End.HasEigenvalue complexB.toLin' eigenPlus ∧
    Module.End.HasEigenvalue complexB.toLin' eigenMinus := by
  constructor
  · apply Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    rw [Matrix.spectrum_toLin']
    exact (actual_complete_complex_spectrum eigenPlus).mpr (Or.inl rfl)
  · apply Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    rw [Matrix.spectrum_toLin']
    exact (actual_complete_complex_spectrum eigenMinus).mpr (Or.inr rfl)

theorem actual_both_eigenvalue_moduli :
    ‖eigenPlus‖=Real.sqrt 10 ∧ ‖eigenMinus‖=Real.sqrt 10 := by
  have hs : (Real.sqrt 15)^2=15 := Real.sq_sqrt (by norm_num)
  have hp : Complex.normSq eigenPlus=10 := by
    simp [Complex.normSq_apply,eigenPlus]
    nlinarith
  have hm : Complex.normSq eigenMinus=10 := by
    simp [Complex.normSq_apply,eigenMinus]
    nlinarith
  constructor
  · rw [Complex.norm_def,hp]
  · rw [Complex.norm_def,hm]

theorem actual_standard_complex_spectral_radius :
    spectralRadius ℂ complexB=(‖eigenPlus‖₊ : ℝ≥0∞) ∧
    (spectralRadius ℂ complexB).toReal=Real.sqrt 10 := by
  have heq : spectralRadius ℂ complexB=(‖eigenPlus‖₊ : ℝ≥0∞) := by
    rw [spectralRadius_eq_of_unital]
    apply le_antisymm
    · apply iSup_le
      intro z
      apply iSup_le
      intro hz
      rcases (actual_complete_complex_spectrum z).mp hz with rfl|rfl
      · rfl
      · have he : ‖eigenMinus‖₊=‖eigenPlus‖₊ := Subtype.ext
          (actual_both_eigenvalue_moduli.2.trans actual_both_eigenvalue_moduli.1.symm)
        rw [he]
    · have hz := (actual_complete_complex_spectrum eigenPlus).mpr (Or.inl rfl)
      exact le_iSup_of_le eigenPlus (le_iSup_of_le hz le_rfl)
  refine ⟨heq,?_⟩
  rw [heq]
  simpa using actual_both_eigenvalue_moduli.1

theorem actual_imaginary_part_rounding_and_strict_non_equality :
    |eigenPlus.im-(1.936 : ℝ)|<0.0005 ∧ (1.936 : ℝ)<eigenPlus.im := by
  have hs : (Real.sqrt 15)^2=15 := Real.sq_sqrt (by norm_num)
  have hp := Real.sqrt_nonneg 15
  change |Real.sqrt 15/2-1.936|<0.0005 ∧ 1.936<Real.sqrt 15/2
  constructor
  · rw [abs_lt]
    constructor <;> nlinarith
  · nlinarith

theorem actual_spectral_radius_rounding :
    |(spectralRadius ℂ complexB).toReal-(3.16 : ℝ)|<0.005 := by
  rw [actual_standard_complex_spectral_radius.2,abs_lt]
  have hs : (Real.sqrt 10)^2=10 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith [Real.sqrt_nonneg 10]

end SafeLearning.CompleteFoundationsSixMatrixComplex
