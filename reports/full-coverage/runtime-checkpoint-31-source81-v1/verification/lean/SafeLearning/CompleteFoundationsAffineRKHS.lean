import SafeLearning.CompleteFoundationsSpectralModels
import SafeLearning.CompleteFoundationsFunctionExamples

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set
open scoped BigOperators Matrix

namespace SafeLearning.CompleteFoundationsAffineRKHS

abbrev E := EuclideanSpace ℝ (Fin 2)
open SafeLearning.CompleteFoundationsSpectralModels (point inner_coordinate_formula norm_squared_coordinates)
open SafeLearning.CompleteFoundationsFunctionExamples (affineGram affine_gram_quadratic affine_gram_pd)

def coefficient (i : Fin 2) : E →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i
def evaluation (w : E) (x : ℝ) : ℝ := (w : Fin 2 → ℝ) 0+(w : Fin 2 → ℝ) 1*x
def feature (x : ℝ) : E := point 1 x
def scalarKernel (x y : ℝ) : ℝ := 1+x*y
def fitted : E := point 1 2

@[instance_reducible]
def affineRKHS : RKHS ℝ E ℝ ℝ where
  coeCLM := ContinuousLinearMap.pi (fun x : ℝ => coefficient 0+x • coefficient 1)
  coeCLM_injective := by
    intro w z h
    have h0 := congrFun h (0 : ℝ)
    have h1 := congrFun h (1 : ℝ)
    change (w : Fin 2 → ℝ) 0+0*(w : Fin 2 → ℝ) 1=(z : Fin 2 → ℝ) 0+0*(z : Fin 2 → ℝ) 1 at h0
    change (w : Fin 2 → ℝ) 0+1*(w : Fin 2 → ℝ) 1=(z : Fin 2 → ℝ) 0+1*(z : Fin 2 → ℝ) 1 at h1
    ext i
    fin_cases i
    · change (w : Fin 2 → ℝ) 0=(z : Fin 2 → ℝ) 0
      linarith
    · change (w : Fin 2 → ℝ) 1=(z : Fin 2 → ℝ) 1
      linarith

theorem actual_rkhs_evaluation (w : E) (x : ℝ) :
    letI : RKHS ℝ E ℝ ℝ := affineRKHS
    (RKHS.coeCLM ℝ) w x=evaluation w x := by
  change (w : Fin 2 → ℝ) 0+x*(w : Fin 2 → ℝ) 1=(w : Fin 2 → ℝ) 0+(w : Fin 2 → ℝ) 1*x
  ring

theorem actual_feature_inner (x y : ℝ) : inner ℝ (feature x) (feature y)=scalarKernel x y := by
  simp [inner_coordinate_formula,feature,scalarKernel,point]

theorem actual_reproducing_identity (w : E) (x : ℝ) :
    inner ℝ w (feature x)=evaluation w x := by
  simp [inner_coordinate_formula,feature,evaluation,point]

theorem actual_kernel_section (x : ℝ) :
    letI : RKHS ℝ E ℝ ℝ := affineRKHS
    RKHS.kerFun E x (1 : ℝ)=feature x := by
  letI : RKHS ℝ E ℝ ℝ := affineRKHS
  apply ext_inner_right ℝ
  intro w
  have hrepr := actual_reproducing_identity w x
  rw [real_inner_comm] at hrepr
  rw [RKHS.kerFun_inner,hrepr]
  change inner ℝ (1 : ℝ) ((RKHS.coeCLM ℝ) w x)=evaluation w x
  rw [actual_rkhs_evaluation]
  simp [RCLike.inner_apply]

theorem actual_rkhs_kernel (x y : ℝ) :
    letI : RKHS ℝ E ℝ ℝ := affineRKHS
    (RKHS.kernel E x y) (1 : ℝ)=scalarKernel x y := by
  letI : RKHS ℝ E ℝ ℝ := affineRKHS
  rw [← RKHS.kerFun_apply,← RKHS.coeCLM_apply,actual_rkhs_evaluation,actual_kernel_section]
  simp [evaluation,feature,point,scalarKernel,mul_comm]

theorem actual_sample_gram :
    Matrix.gram ℝ (fun i : Fin 2 => feature ((![0,1] : Fin 2 → ℝ) i))=affineGram := by
  ext i j
  change inner ℝ (feature ((![0,1] : Fin 2 → ℝ) i)) (feature ((![0,1] : Fin 2 → ℝ) j))=affineGram i j
  rw [actual_feature_inner]
  fin_cases i <;> fin_cases j <;> norm_num [scalarKernel,affineGram]

theorem actual_feature_sum (a : Fin 2 → ℝ) :
    a 0 • feature 0+a 1 • feature 1=point (a 0+a 1) (a 1) := by
  ext i
  fin_cases i <;> simp [feature,point]

theorem actual_gram_sum_of_squares (a : Fin 2 → ℝ) :
    ‖a 0 • feature 0+a 1 • feature 1‖^2=(a 0+a 1)^2+(a 1)^2 ∧
    ‖a 0 • feature 0+a 1 • feature 1‖^2=a ⬝ᵥ (affineGram *ᵥ a) := by
  have h : ‖a 0 • feature 0+a 1 • feature 1‖^2=(a 0+a 1)^2+(a 1)^2 := by
    rw [actual_feature_sum,norm_squared_coordinates]
    simp [point]
  exact ⟨h,by rw [h,affine_gram_quadratic]⟩

theorem actual_sample_gram_positive : affineGram.PosSemidef ∧ affineGram.PosDef ∧ affineGram.det=1 ∧
    LinearIndependent ℝ (fun i : Fin 2 => feature ((![0,1] : Fin 2 → ℝ) i)) := by
  refine ⟨affine_gram_pd.posSemidef,affine_gram_pd,?_,?_⟩
  · norm_num [affineGram,Matrix.det_fin_two]
  · apply Matrix.linearIndependent_of_posDef_gram
    rw [actual_sample_gram]
    exact affine_gram_pd

theorem actual_interpolation_unique (w : E) :
    (evaluation w 0=1 ∧ evaluation w 1=3) ↔ w=fitted := by
  constructor
  · rintro ⟨h0,h1⟩
    simp [evaluation] at h0 h1
    ext i
    fin_cases i <;> simp [fitted,point] <;> linarith
  · intro h
    rw [h]
    norm_num [evaluation,fitted,point]

theorem actual_fitted_function (x : ℝ) : evaluation fitted x=1+2*x := by
  simp [evaluation,fitted,point]

theorem actual_fitted_rkhs_squared_norm : ‖fitted‖^2=5 := by
  norm_num [norm_squared_coordinates,fitted,point]

theorem actual_fitted_representer : fitted= -(feature 0)+(2 : ℝ) • feature 1 := by
  ext i
  fin_cases i <;> norm_num [fitted,feature,point]

theorem actual_fitted_kernel_representer :
    letI : RKHS ℝ E ℝ ℝ := affineRKHS
    fitted= -(RKHS.kerFun E (0 : ℝ) 1)+(2 : ℝ) • RKHS.kerFun E (1 : ℝ) 1 := by
  letI : RKHS ℝ E ℝ ℝ := affineRKHS
  rw [actual_kernel_section,actual_kernel_section]
  exact actual_fitted_representer

theorem actual_feature_norm (x : ℝ) : ‖feature x‖=Real.sqrt (scalarKernel x x) := by
  have hs : ‖feature x‖^2=1+x^2 := by
    rw [norm_squared_coordinates]
    simp [feature,point]
  have hr : (Real.sqrt (scalarKernel x x))^2=1+x^2 := by
    rw [Real.sq_sqrt (by dsimp [scalarKernel];nlinarith [sq_nonneg x])]
    simp [scalarKernel,pow_two]
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (hs.trans hr.symm)

theorem actual_reproducing_cauchy_schwarz (w : E) (x : ℝ) :
    |evaluation w x| ≤ ‖w‖*Real.sqrt (scalarKernel x x) := by
  rw [← actual_reproducing_identity,← actual_feature_norm]
  exact abs_real_inner_le_norm _ _

theorem actual_domain_conclusions :
    (¬∃ M : ℝ,∀ x : ℝ,|evaluation fitted x| ≤ M) ∧
    (∀ x ∈ Icc (-1 : ℝ) 1,|evaluation fitted x| ≤ Real.sqrt 10) ∧
    (¬∃ M : ℝ,∀ x : ℝ,scalarKernel x x ≤ M) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [actual_fitted_function] using SafeLearning.CompleteFoundationsFunctionExamples.affine_not_uniformly_bounded
  · intro x hx
    rw [actual_fitted_function]
    exact SafeLearning.CompleteFoundationsFunctionExamples.affine_compact_uniform_bound x hx
  · rintro ⟨M,hM⟩
    have h := hM (|M|+1)
    simp [scalarKernel] at h
    nlinarith [le_abs_self M,abs_nonneg M,sq_nonneg (|M|+1)]

end SafeLearning.CompleteFoundationsAffineRKHS
