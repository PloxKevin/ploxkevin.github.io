import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsSpectralModels

abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
def applyMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : E →L[ℝ] E :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A
def quadratic (A : Matrix (Fin 2) (Fin 2) ℝ) (x : E) : ℝ := inner ℝ x (applyMatrix A x)
def rayleigh (A : Matrix (Fin 2) (Fin 2) ℝ) (x : E) : ℝ := quadratic A x/‖x‖^2
def sourceA : Matrix (Fin 2) (Fin 2) ℝ := !![3,1;1,3]
def qPlus : E := point (1/Real.sqrt 2) (1/Real.sqrt 2)
def qMinus : E := point (1/Real.sqrt 2) (-1/Real.sqrt 2)

theorem matrix_coordinate_action (A : Matrix (Fin 2) (Fin 2) ℝ) (x : E) :
    applyMatrix A x=point (A 0 0*x 0+A 0 1*x 1) (A 1 0*x 0+A 1 1*x 1) := by
  ext i
  change (A *ᵥ (x : Fin 2 → ℝ)) i=(![A 0 0*x 0+A 0 1*x 1,A 1 0*x 0+A 1 1*x 1] : Fin 2 → ℝ) i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem inner_coordinate_formula (x y : E) : inner ℝ x y=x 0*y 0+x 1*y 1 := by
  simp [PiLp.inner_apply,Fin.sum_univ_succ]
  ring

theorem norm_squared_coordinates (x : E) : ‖x‖^2=(x 0)^2+(x 1)^2 := by
  rw [← real_inner_self_eq_norm_sq,inner_coordinate_formula]
  ring

theorem source_A_action (x : E) : applyMatrix sourceA x=point (3*x 0+x 1) (x 0+3*x 1) := by
  rw [matrix_coordinate_action]
  simp [sourceA]

theorem source_eigenvectors : applyMatrix sourceA qPlus=(4 : ℝ) • qPlus ∧
    applyMatrix sourceA qMinus=(2 : ℝ) • qMinus := by
  rw [source_A_action,source_A_action]
  constructor <;> ext i <;> fin_cases i <;> simp [qPlus,qMinus,point] <;> ring

theorem source_orthonormal : Orthonormal ℝ (![qPlus,qMinus] : Fin 2 → E) := by
  have hr : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (1/Real.sqrt 2 : ℝ)^2=1/2 := by rw [div_pow,one_pow,hs]
  have hpp : inner ℝ qPlus qPlus=1 := by
    rw [inner_coordinate_formula]
    change (1/Real.sqrt 2)*(1/Real.sqrt 2)+(1/Real.sqrt 2)*(1/Real.sqrt 2)=1
    simp only [one_div] at hi ⊢
    nlinarith [hi]
  have hpm : inner ℝ qPlus qMinus=0 := by
    rw [inner_coordinate_formula]
    change (1/Real.sqrt 2)*(1/Real.sqrt 2)+(1/Real.sqrt 2)*(-1/Real.sqrt 2)=0
    ring
  have hmp : inner ℝ qMinus qPlus=0 := by
    rw [real_inner_comm]
    exact hpm
  have hmm : inner ℝ qMinus qMinus=1 := by
    rw [inner_coordinate_formula]
    change (1/Real.sqrt 2)*(1/Real.sqrt 2)+(-1/Real.sqrt 2)*(-1/Real.sqrt 2)=1
    simp only [neg_div,one_div] at hi ⊢
    nlinarith [hi]
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  · simpa using hpp
  · simpa using hpm
  · simpa using hmp
  · simpa using hmm

theorem source_eigenbasis_spans (x : E) :
    x=inner ℝ qPlus x • qPlus+inner ℝ qMinus x • qMinus := by
  have hr : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> simp [inner_coordinate_formula,qPlus,qMinus,point] <;>
    field_simp [hr] <;> rw [hs] <;> ring

theorem source_spectral_matrix_decomposition :
    sourceA=4 • Matrix.vecMulVec (qPlus : Fin 2 → ℝ) (qPlus : Fin 2 → ℝ)+
      2 • Matrix.vecMulVec (qMinus : Fin 2 → ℝ) (qMinus : Fin 2 → ℝ) := by
  have hr : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceA,qPlus,qMinus,point,Matrix.vecMulVec] <;> field_simp <;> nlinarith

theorem source_all_eigenvalues (lambda : ℝ) :
    (∃ x : E,x≠0 ∧ applyMatrix sourceA x=lambda • x) ↔ lambda=2 ∨ lambda=4 := by
  constructor
  · rintro ⟨x,hx,h⟩
    have h0 := congrArg (fun u : E => u 0) h
    have h1 := congrArg (fun u : E => u 1) h
    rw [source_A_action] at h0 h1
    simp [point] at h0 h1
    by_contra hn
    push Not at hn
    have hp : (lambda-4)*(x 0+x 1)=0 := by nlinarith
    have hm : (lambda-2)*(x 0-x 1)=0 := by nlinarith
    have hsum : x 0+x 1=0 := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hn.2)
    have hdiff : x 0-x 1=0 := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hn.1)
    apply hx
    ext i
    fin_cases i <;> simp <;> linarith
  · rintro (rfl|rfl)
    · refine ⟨qMinus,?_,source_eigenvectors.2⟩
      intro h
      have hh := congrArg (fun u : E => u 0) h
      simp [qMinus,point] at hh
    · refine ⟨qPlus,?_,source_eigenvectors.1⟩
      intro h
      have hh := congrArg (fun u : E => u 0) h
      simp [qPlus,point] at hh

theorem source_quadratic_expansion (x : E) :
    quadratic sourceA x=3*(x 0)^2+2*x 0*x 1+3*(x 1)^2 := by
  rw [quadratic,source_A_action,inner_coordinate_formula]
  simp [point]
  ring

theorem rayleigh_bounds_and_equality (x : E) :
    2*‖x‖^2≤quadratic sourceA x ∧ quadratic sourceA x≤4*‖x‖^2 ∧
    (quadratic sourceA x=2*‖x‖^2 ↔ x 0= -x 1) ∧
    (quadratic sourceA x=4*‖x‖^2 ↔ x 0=x 1) := by
  rw [norm_squared_coordinates,source_quadratic_expansion]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith [sq_nonneg (x 0+x 1)]
  · nlinarith [sq_nonneg (x 0-x 1)]
  · constructor <;> intro h <;> nlinarith [sq_nonneg (x 0+x 1)]
  · constructor <;> intro h <;> nlinarith [sq_nonneg (x 0-x 1)]

theorem source_rayleigh_numerics :
    applyMatrix sourceA (point 1 2)=point 5 7 ∧ quadratic sourceA (point 1 2)=19 ∧
    ‖point 1 2‖^2=5 ∧ rayleigh sourceA (point 1 2)=19/5 ∧
    2*‖point 1 2‖^2<quadratic sourceA (point 1 2) ∧
    quadratic sourceA (point 1 2)<4*‖point 1 2‖^2 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [source_A_action]
    norm_num [point]
  · norm_num [source_quadratic_expansion,point]
  · norm_num [norm_squared_coordinates,point]
  · norm_num [rayleigh,source_quadratic_expansion,norm_squared_coordinates,point]
  · norm_num [source_quadratic_expansion,norm_squared_coordinates,point]
  · norm_num [source_quadratic_expansion,norm_squared_coordinates,point]

theorem source_rayleigh_attainers (t : ℝ) (ht : t≠0) :
    rayleigh sourceA (t • point 1 (-1))=2 ∧ rayleigh sourceA (t • point 1 1)=4 := by
  simp [rayleigh,source_quadratic_expansion,norm_squared_coordinates,point]
  constructor <;> field_simp <;> ring

theorem source_both_eigencomponents_nonzero :
    inner ℝ qPlus (point 1 2)≠0 ∧ inner ℝ qMinus (point 1 2)≠0 := by
  have hr : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  constructor <;> simp [inner_coordinate_formula,qPlus,qMinus,point] <;>
    field_simp <;> norm_num

def sourceN : Matrix (Fin 2) (Fin 2) ℝ := !![1,4;0,1]
def symmetricPart : Matrix (Fin 2) (Fin 2) ℝ := (1/2 : ℝ) • (sourceN+sourceN.transpose)
def skewPart : Matrix (Fin 2) (Fin 2) ℝ := sourceN-symmetricPart

theorem source_N_action (x : E) : applyMatrix sourceN x=point (x 0+4*x 1) (x 1) := by
  rw [matrix_coordinate_action]
  simp [sourceN]

theorem source_N_characteristic_polynomial : sourceN.charpoly=(Polynomial.X-1)^2 := by
  rw [Matrix.charpoly_fin_two]
  norm_num [sourceN,Matrix.det_fin_two,Matrix.trace,Fin.sum_univ_succ]
  rw [show Polynomial.C (2 : ℝ)=(2 : Polynomial ℝ) by exact Polynomial.C_ofNat 2]
  ring

theorem source_N_eigenvector_characterization (lambda : ℝ) (x : E) (hx : x≠0) :
    applyMatrix sourceN x=lambda • x ↔ lambda=1 ∧ x 1=0 := by
  constructor
  · intro h
    have h0 := congrArg (fun u : E => u 0) h
    have h1 := congrArg (fun u : E => u 1) h
    rw [source_N_action] at h0 h1
    simp [point] at h0 h1
    have hl : lambda=1 := by
      by_contra hn
      have hz1 : x 1=0 := (mul_eq_zero.mp (show (lambda-1)*x 1=0 by nlinarith)).resolve_left
        (sub_ne_zero.mpr hn)
      have hz0 : x 0=0 := (mul_eq_zero.mp (show (lambda-1)*x 0=0 by rw [hz1] at h0;nlinarith)).resolve_left
        (sub_ne_zero.mpr hn)
      apply hx
      ext i
      fin_cases i <;> simp [hz0,hz1]
    exact ⟨hl,by rw [hl] at h0;nlinarith⟩
  · rintro ⟨rfl,h1⟩
    rw [source_N_action]
    ext i
    fin_cases i <;> simp [point,h1]

theorem source_N_negative_form : applyMatrix sourceN (point 1 (-1))=point (-3) (-1) ∧
    quadratic sourceN (point 1 (-1))= -2 := by
  rw [source_N_action]
  constructor
  · norm_num [point]
  · rw [quadratic,source_N_action,inner_coordinate_formula]
    norm_num [point]

theorem source_symmetric_and_skew_parts :
    symmetricPart=!![1,2;2,1] ∧ skewPart.transpose= -skewPart ∧ sourceN=symmetricPart+skewPart := by
  refine ⟨?_,?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [symmetricPart,sourceN,Matrix.transpose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [skewPart,symmetricPart,sourceN,Matrix.transpose_apply]
  · simp [skewPart]

theorem general_real_skew_quadratic_zero {n : Type*} [Fintype n]
    (K : Matrix n n ℝ) (hK : K.transpose= -K) (x : n → ℝ) : x ⬝ᵥ (K *ᵥ x)=0 := by
  have ht : x ⬝ᵥ (K.transpose *ᵥ x)=x ⬝ᵥ (K *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,Matrix.transpose_transpose,dotProduct_comm]
  rw [hK,Matrix.neg_mulVec,dotProduct_neg] at ht
  linarith

theorem source_forms_equal (x : E) : quadratic sourceN x=quadratic symmetricPart x ∧
    quadratic skewPart x=0 := by
  constructor
  · rw [quadratic,quadratic,matrix_coordinate_action,matrix_coordinate_action,
      inner_coordinate_formula,inner_coordinate_formula]
    simp [symmetricPart,sourceN,point,Matrix.transpose_apply]
    ring
  · have hh := general_real_skew_quadratic_zero _ source_symmetric_and_skew_parts.2.1 (x : Fin 2 → ℝ)
    rw [quadratic,matrix_coordinate_action,inner_coordinate_formula]
    simpa [point,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh

theorem symmetric_part_eigenvalues (lambda : ℝ) :
    (∃ x : E,x≠0 ∧ applyMatrix symmetricPart x=lambda • x) ↔ lambda= -1 ∨ lambda=3 := by
  have haction : ∀x : E,applyMatrix symmetricPart x=point (x 0+2*x 1) (2*x 0+x 1) := by
    intro x
    rw [matrix_coordinate_action,source_symmetric_and_skew_parts.1]
    simp
  constructor
  · rintro ⟨x,hx,h⟩
    have h0 := congrArg (fun u : E => u 0) h
    have h1 := congrArg (fun u : E => u 1) h
    rw [haction] at h0 h1
    simp [point] at h0 h1
    by_contra hn
    push Not at hn
    have hp : (lambda-3)*(x 0+x 1)=0 := by nlinarith
    have hm : (lambda+1)*(x 0-x 1)=0 := by nlinarith
    have hsum : x 0+x 1=0 := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hn.2)
    have hdiff : x 0-x 1=0 := (mul_eq_zero.mp hm).resolve_left (by simpa using sub_ne_zero.mpr hn.1)
    apply hx
    ext i
    fin_cases i <;> simp <;> linarith
  · rintro (rfl|rfl)
    · refine ⟨point 1 (-1),?_,?_⟩
      · intro h
        have hh := congrArg (fun u : E => u 0) h
        norm_num [point] at hh
      · rw [haction]
        ext i
        fin_cases i <;> norm_num [point]
    · refine ⟨point 1 1,?_,?_⟩
      · intro h
        have hh := congrArg (fun u : E => u 0) h
        norm_num [point] at hh
      · rw [haction]
        ext i
        fin_cases i <;> norm_num [point]

theorem source_N_not_symmetric : sourceN.transpose≠sourceN := by
  intro h
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
  norm_num [sourceN,Matrix.transpose_apply] at hh

theorem source_N_eigenvectors_never_orthogonal (u v : E) (hu : u≠0) (hv : v≠0)
    (lambda mu : ℝ) (hEu : applyMatrix sourceN u=lambda • u)
    (hEv : applyMatrix sourceN v=mu • v) : inner ℝ u v≠0 := by
  have hu1 := (source_N_eigenvector_characterization lambda u hu).mp hEu |>.2
  have hv1 := (source_N_eigenvector_characterization mu v hv).mp hEv |>.2
  have hu0 : u 0≠0 := by
    intro h
    apply hu
    ext i
    fin_cases i <;> simp [h,hu1]
  have hv0 : v 0≠0 := by
    intro h
    apply hv
    ext i
    fin_cases i <;> simp [h,hv1]
  rw [inner_coordinate_formula,hu1,hv1]
  simpa using mul_ne_zero hu0 hv0

theorem source_N_has_no_orthonormal_eigenbasis :
    ¬ ∃ b : OrthonormalBasis (Fin 2) ℝ E,∀ i,∃ lambda : ℝ,applyMatrix sourceN (b i)=lambda • b i := by
  rintro ⟨b,hb⟩
  obtain ⟨lambda,hl⟩ := hb 0
  obtain ⟨mu,hm⟩ := hb 1
  have hn0 : b 0≠0 := by
    intro h
    have hh := b.norm_eq_one (0 : Fin 2)
    rw [h,norm_zero] at hh
    norm_num at hh
  have hn1 : b 1≠0 := by
    intro h
    have hh := b.norm_eq_one (1 : Fin 2)
    rw [h,norm_zero] at hh
    norm_num at hh
  have hne := source_N_eigenvectors_never_orthogonal _ _ hn0 hn1 lambda mu hl hm
  apply hne
  have hh := orthonormal_iff_ite.mp b.orthonormal (0 : Fin 2) (1 : Fin 2)
  simpa using hh

end SafeLearning.CompleteFoundationsSpectralModels
