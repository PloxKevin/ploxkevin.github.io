import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace SafeLearning.CompleteModulesGPExamples

def twoGram (correlation : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,correlation;correlation,1]

theorem two_gram_eigenvectors (r : ℝ) :
    twoGram r *ᵥ ![1,1]=(1+r) • ![1,1] ∧
    twoGram r *ᵥ ![1,-1]=(1-r) • ![1,-1] := by
  constructor <;> ext i <;> fin_cases i <;> simp [twoGram,Matrix.mulVec,Fin.sum_univ_two] <;> ring

theorem two_gram_characteristic_roots (r eigenvalue : ℝ) :
    (twoGram r-eigenvalue • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det=0 ↔
      eigenvalue=1+r ∨ eigenvalue=1-r := by
  have hid : (twoGram r-eigenvalue • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det=
      (eigenvalue-(1+r))*(eigenvalue-(1-r)) := by
    simp [twoGram,Matrix.det_fin_two]
    ring
  rw [hid,mul_eq_zero]
  simp only [sub_eq_zero]

theorem two_gram_half_characteristic :
    (twoGram (1/2)-((3/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))).det=0 ∧
    (twoGram (1/2)-((1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))).det=0 ∧
    ∀ eigenvalue : ℝ, (twoGram (1/2)-eigenvalue • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det=0 ↔
      eigenvalue=3/2 ∨ eigenvalue=1/2 := by
  simp only [two_gram_characteristic_roots]
  norm_num

theorem two_gram_half_positive (x y : ℝ) (hne : x≠0 ∨ y≠0) :
    0 < x^2+x*y+y^2 := by
  have hs := sq_nonneg (x+y)
  rcases hne with hx | hy
  · have hxpos := sq_pos_of_ne_zero hx
    nlinarith [sq_nonneg y]
  · have hypos := sq_pos_of_ne_zero hy
    nlinarith [sq_nonneg x]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem section_difference_values (a b : H) (r : ℝ)
    (haa : inner ℝ a a=1) (hbb : inner ℝ b b=1) (hab : inner ℝ a b=r) :
    inner ℝ (a-b) a=1-r ∧ inner ℝ (a-b) b=r-1 ∧ ‖a-b‖^2=2*(1-r) := by
  have hba : inner ℝ b a=r := by rw [real_inner_comm,hab]
  constructor
  · simp only [inner_sub_left,haa,hba]
  constructor
  · simp only [inner_sub_left,hab,hbb]
  · rw [← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,inner_sub_right,
      haa,hbb,hab,hba]
    ring

theorem section_difference_half (a b : H)
    (haa : inner ℝ a a=1) (hbb : inner ℝ b b=1) (hab : inner ℝ a b=1/2) :
    inner ℝ (a-b) a=1/2 ∧ inner ℝ (a-b) b= -1/2 ∧ ‖a-b‖^2=1 ∧ ‖a-b‖=1 := by
  obtain ⟨ha,hb,hn⟩ := section_difference_values a b (1/2) haa hbb hab
  have hn' : ‖a-b‖^2=1 := by linarith [hn]
  refine ⟨by linarith [ha],by linarith [hb],hn',?_⟩
  nlinarith [norm_nonneg (a-b)]

def conflictingInterpolant (a b : H) (r : ℝ) : H := (1/(1-r)) • (a-b)

theorem conflicting_interpolant_values (a b : H) (r : ℝ) (hr : r<1)
    (haa : inner ℝ a a=1) (hbb : inner ℝ b b=1) (hab : inner ℝ a b=r) :
    inner ℝ (conflictingInterpolant a b r) a=1 ∧
    inner ℝ (conflictingInterpolant a b r) b= -1 := by
  obtain ⟨ha,hb,hn⟩ := section_difference_values a b r haa hbb hab
  have hne : 1-r≠0 := by linarith
  simp only [conflictingInterpolant,real_inner_smul_left,ha,hb]
  constructor <;> field_simp <;> ring

theorem conflicting_interpolant_squared_norm (a b : H) (r : ℝ) (hr : r<1)
    (haa : inner ℝ a a=1) (hbb : inner ℝ b b=1) (hab : inner ℝ a b=r) :
    ‖conflictingInterpolant a b r‖^2=2/(1-r) := by
  have hd := (section_difference_values a b r haa hbb hab).2.2
  have hp : 0 < 1-r := by linarith
  rw [conflictingInterpolant,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hp),
    mul_pow,hd]
  field_simp
  <;> ring

theorem conflicting_interpolation_norm_gap (a b candidate : H) (r : ℝ) (hr : r<1)
    (haa : inner ℝ a a=1) (hbb : inner ℝ b b=1) (hab : inner ℝ a b=r)
    (hca : inner ℝ candidate a=1) (hcb : inner ℝ candidate b= -1) :
    ‖candidate‖^2 = 2/(1-r)+‖candidate-conflictingInterpolant a b r‖^2 := by
  obtain ⟨hfa,hfb⟩ := conflicting_interpolant_values a b r hr haa hbb hab
  have ho : inner ℝ (conflictingInterpolant a b r) (candidate-conflictingInterpolant a b r)=0 := by
    rw [real_inner_comm,conflictingInterpolant,real_inner_smul_right,inner_sub_left,
      inner_sub_right,inner_sub_right,hca,hcb]
    have hvals : inner ℝ ((1/(1-r)) • (a-b)) a=1 ∧
        inner ℝ ((1/(1-r)) • (a-b)) b= -1 := ⟨hfa,hfb⟩
    rw [hvals.1,hvals.2]
    ring
  have hn := norm_add_sq_real (conflictingInterpolant a b r) (candidate-conflictingInterpolant a b r)
  rw [add_sub_cancel,ho,mul_zero,add_zero,
    conflicting_interpolant_squared_norm a b r hr haa hbb hab] at hn
  exact hn

theorem conflicting_interpolant_global_minimum (a b candidate : H) (r : ℝ) (hr : r<1)
    (haa : inner ℝ a a=1) (hbb : inner ℝ b b=1) (hab : inner ℝ a b=r)
    (hca : inner ℝ candidate a=1) (hcb : inner ℝ candidate b= -1) :
    2/(1-r) ≤ ‖candidate‖^2 := by
  rw [conflicting_interpolation_norm_gap a b candidate r hr haa hbb hab hca hcb]
  linarith [sq_nonneg ‖candidate-conflictingInterpolant a b r‖]

theorem conflicting_interpolant_unique (a b candidate : H) (r : ℝ) (hr : r<1)
    (haa : inner ℝ a a=1) (hbb : inner ℝ b b=1) (hab : inner ℝ a b=r)
    (hca : inner ℝ candidate a=1) (hcb : inner ℝ candidate b= -1)
    (hmin : ‖candidate‖^2=2/(1-r)) : candidate=conflictingInterpolant a b r := by
  have hgap := conflicting_interpolation_norm_gap a b candidate r hr haa hbb hab hca hcb
  rw [hmin] at hgap
  have hz : ‖candidate-conflictingInterpolant a b r‖^2=0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem conflicting_norm_specializations : (2:ℝ)/(1-1/2)=4 ∧ (2:ℝ)/(1-99/100)=200 := by norm_num

def singleMean (prior cross noise observation : ℝ) : ℝ := cross*observation/(prior+noise)
def singleVariance (prior cross queryDiagonal noise : ℝ) : ℝ := queryDiagonal-cross^2/(prior+noise)

theorem single_observation_solve (prior noise observation : ℝ) (hden : prior+noise≠0) :
    ∃! coefficient : ℝ, (prior+noise)*coefficient=observation := by
  refine ⟨observation/(prior+noise),?_,?_⟩
  · field_simp
  · intro other hother
    apply (eq_div_iff hden).mpr
    simpa only [mul_comm] using hother

theorem one_observation_posteriors :
    singleMean 1 1 (1/4) 2=8/5 ∧ singleVariance 1 1 1 (1/4)=1/5 ∧
    singleMean 1 (1/2) (1/4) 2=4/5 ∧ singleVariance 1 (1/2) 1 (1/4)=4/5 := by
  norm_num [singleMean,singleVariance]

theorem variance_standard_deviation : Real.sqrt (4/100)=1/5 := by
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
  norm_num

theorem posterior_band_and_failure :
    1-3*Real.sqrt (4/100)=2/5 ∧ 1+3*Real.sqrt (4/100)=8/5 ∧
    (2/5 : ℝ)<1/2 ∧ (2/5 : ℝ)∈Set.Icc (2/5) (8/5) := by
  rw [variance_standard_deviation]
  norm_num

theorem confidence_convention : Real.sqrt 9=3 ∧
    ∀ norm : ℝ, 0≤norm → (norm^2≤16 ↔ norm≤4) := by
  constructor
  · norm_num
  · intro norm hnorm
    constructor <;> intro h <;> nlinarith

theorem power_function_numeric :
    Real.sqrt (1-(3/5:ℝ)^2)=4/5 ∧ 2*Real.sqrt (1-(3/5:ℝ)^2)=8/5 ∧
    Real.sqrt (1-(1:ℝ)^2)=0 := by norm_num

theorem repeated_scalar_system (n : ℕ) :
    (∀ i : Fin n, (∑ _j : Fin n, 1/(n+1:ℝ))+1/(n+1:ℝ)=1) ∧
    (1-(∑ _j : Fin n, 1/(n+1:ℝ)))=1/(n+1:ℝ) := by
  have hden : (n+1:ℝ)≠0 := by positivity
  constructor
  · intro i
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    <;> ring
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    <;> ring

theorem repeated_variance_examples : (1:ℝ)/(1+1)=1/2 ∧ (1:ℝ)/(3+1)=1/4 := by norm_num

theorem two_point_regularized_solves (a b v w : ℝ) :
    ((3/2)*a+(1/2)*b=1 ∧ (1/2)*a+(3/2)*b= -1 ↔ a=1 ∧ b= -1) ∧
    ((3/2)*v+(1/2)*w=1/2 ∧ (1/2)*v+(3/2)*w=0 ↔ v=3/8 ∧ w= -1/8) := by
  constructor <;> constructor
  · rintro ⟨ha,hb⟩; constructor <;> linarith
  · rintro ⟨rfl,rfl⟩; norm_num
  · rintro ⟨hv,hw⟩; constructor <;> linarith
  · rintro ⟨rfl,rfl⟩; norm_num

theorem two_point_query_posterior : (1/2:ℝ)*1+0*(-1)=1/2 ∧
    1-((1/2:ℝ)*(3/8)+0*(-1/8))=13/16 ∧
    1-((1/2:ℝ)*(2/3)+0*(-1/3))=2/3 := by norm_num

theorem misspecification_transfer (truth surrogate mean idealMean epsilon beta sigma correction : ℝ)
    (htruth : |truth-surrogate|≤epsilon) (hmodel : |surrogate-mean|≤beta*sigma)
    (hmean : |mean-idealMean|≤epsilon*correction*sigma) :
    |truth-idealMean|≤epsilon+(beta+epsilon*correction)*sigma := by
  have ht1 := abs_add_le (truth-surrogate) (surrogate-mean)
  have ht2 := abs_add_le (truth-mean) (mean-idealMean)
  have he1 : truth-surrogate+(surrogate-mean)=truth-mean := by ring
  have he2 : truth-mean+(mean-idealMean)=truth-idealMean := by ring
  rw [he1] at ht1
  rw [he2] at ht2
  linarith

theorem misspecification_numeric :
    (1/20:ℝ)+(2+(1/20)*Real.sqrt (16/(1/4)))*(1/10)=29/100 := by norm_num

theorem information_gain_determinant :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ)+twoGram (1/2)).det=15/4 := by
  norm_num [twoGram,Matrix.det_fin_two]

theorem realized_information_not_maximum :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ)+twoGram (1/2)).det <
      ((1 : Matrix (Fin 2) (Fin 2) ℝ)+twoGram 0).det := by
  norm_num [twoGram,Matrix.det_fin_two]

theorem confidence_multiplier_exact :
    2+((1/10:ℝ)/Real.sqrt (4/100))*Real.sqrt (3+2*Real.log (1/(1/20)))=
      2+(1/2)*Real.sqrt (3+2*Real.log 20) := by
  rw [variance_standard_deviation]
  norm_num

end SafeLearning.CompleteModulesGPExamples
