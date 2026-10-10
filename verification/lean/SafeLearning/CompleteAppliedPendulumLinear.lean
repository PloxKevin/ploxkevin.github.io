import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteAppliedPendulumLinear

def field (x:ℝ×ℝ) : ℝ×ℝ := (x.2,10*Real.sin x.1-x.2/10)
def derivativeMap (theta:ℝ) : (ℝ×ℝ)→L[ℝ](ℝ×ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((10*Real.cos theta) • ContinuousLinearMap.fst ℝ ℝ ℝ-
      (1/10:ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
def matrix (h:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;h,-1/10]
def complexMatrix (h:ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (matrix h).map Complex.ofReal

def uprightPlus : ℝ := (-1+Real.sqrt 4001)/20
def uprightMinus : ℝ := (-1-Real.sqrt 4001)/20
def hangingPlus : ℂ := (-1/20:ℂ)+(Real.sqrt 3999/20:ℝ)*Complex.I
def hangingMinus : ℂ := (-1/20:ℂ)-(Real.sqrt 3999/20:ℝ)*Complex.I

theorem actual_source_pendulum_field_equilibria (x:ℝ×ℝ) :
    field x=0 ↔ x.2=0 ∧ ∃n:ℤ,(n:ℝ)*Real.pi=x.1 := by
  constructor
  · intro h
    have hv:=congrArg Prod.fst h
    have ha:=congrArg Prod.snd h
    change x.2=0 at hv
    change 10*Real.sin x.1-x.2/10=0 at ha
    refine ⟨hv,Real.sin_eq_zero_iff.mp ?_⟩
    rw [hv] at ha
    linarith
  · rintro ⟨hv,hn⟩
    have hs:=Real.sin_eq_zero_iff.mpr hn
    apply Prod.ext <;> simp [field,hv,hs]

theorem actual_source_pendulum_field_has_its_true_frechet_linearization (x:ℝ×ℝ) :
    HasFDerivAt field (derivativeMap x.1) x := by
  have hs := (Real.hasDerivAt_sin x.1).hasFDerivAt.comp x
    (hasFDerivAt_fst : HasFDerivAt (@Prod.fst ℝ ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) x)
  have hv := (hasFDerivAt_snd : HasFDerivAt (@Prod.snd ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) x)
  have h:=hv.prodMk ((hs.const_mul 10).sub (hv.const_mul (1/10)))
  convert h using 1
  · funext y
    apply Prod.ext <;> simp [field,div_eq_mul_inv,mul_comm]
  · apply ContinuousLinearMap.ext
    intro y
    apply Prod.ext <;> simp [derivativeMap,ContinuousLinearMap.toSpanSingleton] <;> ring

theorem actual_equilibrium_derivative_maps_are_the_printed_matrices (y:ℝ×ℝ) :
    derivativeMap 0 y=(y.2,10*y.1-y.2/10) ∧
      derivativeMap Real.pi y=(y.2,-10*y.1-y.2/10) ∧
      matrix 10=!![0,1;10,-1/10] ∧ matrix (-10)=!![0,1;-10,-1/10] := by
  simp [derivativeMap,matrix,div_eq_mul_inv,mul_comm]

theorem actual_source_linearization_trace_determinant (h:ℝ) :
    (matrix h).trace=-1/10 ∧ (matrix h).det=-h := by
  norm_num [matrix,Matrix.trace,Fin.sum_univ_two,Matrix.det_fin_two]

theorem actual_source_official_complex_spectrum (h:ℝ) (z:ℂ) :
    z∈spectrum ℂ (complexMatrix h) ↔ z^2+z/10-(h:ℂ)=0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (complexMatrix h).charpoly.eval z=0 ↔ _
  have he : (complexMatrix h).charpoly.eval z=z^2+z/10-(h:ℂ) := by
    rw [Matrix.charpoly_fin_two]
    simp [complexMatrix,matrix,Matrix.trace,Fin.sum_univ_two,Matrix.det_fin_two]
    ring
  rw [he]

theorem actual_upright_official_spectrum_is_exactly_the_two_real_roots (z:ℂ) :
    z∈spectrum ℂ (complexMatrix 10) ↔
      z=(uprightPlus:ℂ) ∨ z=(uprightMinus:ℂ) := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤4001)
  have hf : z^2+z/10-((10:ℝ):ℂ)=(z-(uprightPlus:ℂ))*(z-(uprightMinus:ℂ)) := by
    apply Complex.ext <;>
      simp [uprightPlus,uprightMinus,Complex.mul_re,Complex.mul_im,pow_two] <;> nlinarith
  rw [actual_source_official_complex_spectrum]
  rw [hf,mul_eq_zero,sub_eq_zero,sub_eq_zero]

theorem actual_hanging_official_spectrum_is_exactly_the_two_nonreal_roots (z:ℂ) :
    z∈spectrum ℂ (complexMatrix (-10)) ↔ z=hangingPlus ∨ z=hangingMinus := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3999)
  have hf : z^2+z/10-((-10:ℝ):ℂ)=(z-hangingPlus)*(z-hangingMinus) := by
    apply Complex.ext <;>
      simp [hangingPlus,hangingMinus,Complex.mul_re,Complex.mul_im,pow_two] <;> nlinarith
  rw [actual_source_official_complex_spectrum]
  rw [hf,mul_eq_zero,sub_eq_zero,sub_eq_zero]

theorem actual_upright_roots_have_opposite_signs :
    0<uprightPlus ∧ uprightMinus<0 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤4001)
  have hp:=Real.sqrt_nonneg (4001:ℝ)
  dsimp [uprightPlus,uprightMinus]
  constructor <;> nlinarith

theorem actual_hanging_roots_have_negative_real_parts_and_nonzero_imaginary_parts :
    hangingPlus.re=-1/20 ∧ hangingMinus.re=-1/20 ∧
      0<hangingPlus.im ∧ hangingMinus.im<0 ∧
      Complex.normSq hangingPlus=10 ∧ Complex.normSq hangingMinus=10 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3999)
  have hp:=Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3999)
  simp only [hangingPlus,hangingMinus,Complex.add_re,Complex.sub_re,Complex.mul_re,
    Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,mul_one,zero_add]
  norm_num [Complex.normSq_apply] <;> nlinarith


theorem actual_source_equilibrium_angles_are_zero_or_pi_modulo_two_pi (x:ℝ×ℝ) :
    field x=0 ↔ x.2=0 ∧ ((x.1:Real.Angle)=0 ∨ (x.1:Real.Angle)=(Real.pi:Real.Angle)) := by
  rw [actual_source_pendulum_field_equilibria]
  constructor
  · rintro ⟨hv,hs⟩
    refine ⟨hv,Real.Angle.sin_eq_zero_iff.mp ?_⟩
    rw [Real.Angle.sin_coe]
    exact Real.sin_eq_zero_iff.mpr hs
  · rintro ⟨hv,ha⟩
    refine ⟨hv,Real.sin_eq_zero_iff.mp ?_⟩
    rw [←Real.Angle.sin_coe]
    exact Real.Angle.sin_eq_zero_iff.mpr ha

end SafeLearning.CompleteAppliedPendulumLinear
