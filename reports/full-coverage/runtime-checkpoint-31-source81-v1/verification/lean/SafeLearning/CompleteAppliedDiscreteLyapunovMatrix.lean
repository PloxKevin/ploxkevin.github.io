import SafeLearning.CompleteAppliedDiscreteQuadraticBasin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedDiscreteLyapunovMatrix
open CompleteAppliedDiscreteQuadraticBasin

def sourceA : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;-1,-1]
def symmetricCandidate (p1 p2 p3 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![p1,p2;p2,p3]
def sourceP : Matrix (Fin 2) (Fin 2) ℝ := symmetricCandidate (3/2) (1/2) 1
def eigenLow : ℝ := (5-Real.sqrt 5)/4
def eigenHigh : ℝ := (5+Real.sqrt 5)/4

theorem actual_candidate_Lyapunov_equation_matrix (p1 p2 p3 : ℝ) :
    sourceAᵀ*symmetricCandidate p1 p2 p3+symmetricCandidate p1 p2 p3*sourceA=
      !![-2*p2,p1-p2-p3;p1-p2-p3,2*p2-2*p3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceA,symmetricCandidate,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem actual_unique_symmetric_solution_of_the_source_Lyapunov_equation
    (p1 p2 p3 : ℝ) :
    sourceAᵀ*symmetricCandidate p1 p2 p3+symmetricCandidate p1 p2 p3*sourceA= -1 ↔
      p1=3/2 ∧ p2=1/2 ∧ p3=1 := by
  rw [actual_candidate_Lyapunov_equation_matrix]
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ=>M 0 0) h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ=>M 0 1) h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ=>M 1 1) h
    norm_num [Matrix.one_apply] at h00 h01 h11
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨rfl,rfl,rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

theorem actual_source_P_transpose_product_trace_and_determinant :
    sourceAᵀ*sourceP= !![-1/2,-1;1,-1/2] ∧
      sourceAᵀ*sourceP+sourceP*sourceA= -1 ∧
      sourceP.trace=5/2 ∧ sourceP.det=5/4 := by
  refine ⟨?_,?_,?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sourceA,sourceP,symmetricCandidate,Matrix.mul_apply,Fin.sum_univ_two]
  · exact (actual_unique_symmetric_solution_of_the_source_Lyapunov_equation
      (3/2) (1/2) 1).mpr ⟨rfl,rfl,rfl⟩
  · norm_num [sourceP,symmetricCandidate,Matrix.trace,Fin.sum_univ_two]
  · norm_num [sourceP,symmetricCandidate,Matrix.det_fin_two]

theorem actual_source_P_quadratic_completion (x : Fin 2 → ℝ) :
    x ⬝ᵥ (sourceP *ᵥ x)=(x 1+x 0/2)^2+(5/4)*(x 0)^2 := by
  simp [sourceP,symmetricCandidate,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_source_P_is_positive_definite : sourceP.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sourceP,symmetricCandidate,Matrix.conjTranspose_apply]
  · intro x hx
    have he : star x=x := by ext i; simp
    rw [he,actual_source_P_quadratic_completion]
    have hn : x 0≠0 ∨ x 1≠0 := by
      by_contra h
      simp only [not_or,not_not] at h
      apply hx
      ext i
      fin_cases i <;> simp [h.1,h.2]
    rcases hn with hn | hn
    · have hp := sq_pos_of_ne_zero hn
      nlinarith [sq_nonneg (x 1+x 0/2)]
    · by_cases h0 : x 0=0
      · simp only [h0,zero_div,add_zero,pow_two,zero_mul,add_zero]
        simpa using mul_self_pos.mpr hn
      · nlinarith [sq_pos_of_ne_zero h0,sq_nonneg (x 1+x 0/2)]

def complexP : Matrix (Fin 2) (Fin 2) ℂ := sourceP.map Complex.ofReal

theorem actual_complete_complex_spectrum_of_source_P (z : ℂ) :
    z∈spectrum ℂ complexP ↔ z=(eigenLow:ℂ) ∨ z=(eigenHigh:ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  have hp : complexP.charpoly.eval z=z^2-(5/2)*z+5/4 := by
    rw [Matrix.charpoly_fin_two]
    norm_num [complexP,sourceP,symmetricCandidate,Matrix.trace,Fin.sum_univ_two,
      Matrix.det_fin_two]
  have hf : z^2-(5/2)*z+5/4=(z-(eigenLow:ℂ))*(z-(eigenHigh:ℂ)) := by
    have hs := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
    apply Complex.ext <;>
      simp [eigenLow,eigenHigh,Complex.mul_re,Complex.mul_im,pow_two] <;> nlinarith
  change complexP.charpoly.eval z=0 ↔ _
  rw [hp,hf]
  simp only [mul_eq_zero,sub_eq_zero]

theorem actual_source_eigenvalues_have_the_displayed_three_decimal_rounding :
    0<eigenLow ∧ eigenLow<eigenHigh ∧
      |eigenLow-691/1000|<1/2000 ∧ |eigenHigh-1809/1000|<1/2000 ∧
      eigenLow≠691/1000 ∧ eigenHigh≠1809/1000 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  have hp := Real.sqrt_pos.mpr (show (0:ℝ)<5 by norm_num)
  unfold eigenLow eigenHigh
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · nlinarith
  · linarith
  · rw [abs_lt]
    constructor <;> nlinarith
  · rw [abs_lt]
    constructor <;> nlinarith
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem actual_nonnegative_square_sublevel_is_the_true_symmetric_interval
    (c : ℝ) (hc : 0≤c) :
    {x : ℝ | x^2≤c}=Icc (-Real.sqrt c) (Real.sqrt c) := by
  ext x
  have hs := Real.sq_sqrt hc
  have hp := Real.sqrt_nonneg c
  constructor
  · intro hx
    change x^2≤c at hx
    have hab : |x|≤Real.sqrt c := by nlinarith [abs_nonneg x,sq_abs x]
    exact abs_le.mp hab
  · intro hx
    change x^2≤c
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (by linarith [hx.1] : 0≤x+Real.sqrt c)
      (by linarith [hx.2] : x-Real.sqrt c≤0)
    nlinarith

theorem actual_sublevel_fits_the_storage_decrease_region_iff
    (c : ℝ) (hc : 0≤c) :
    Icc (-Real.sqrt c) (Real.sqrt c) ⊆ Ioo (-3/2) (1/2) ↔ c<1/4 := by
  have hs := Real.sq_sqrt hc
  have hp := Real.sqrt_nonneg c
  constructor
  · intro h
    have hh := h (show Real.sqrt c∈Icc (-Real.sqrt c) (Real.sqrt c) by constructor <;> linarith)
    nlinarith [hh.2]
  · intro hh x hx
    have hr : Real.sqrt c<1/2 := by nlinarith
    constructor <;> linarith [hx.1,hx.2]

theorem actual_union_of_certified_nonnegative_sublevels_is_exactly_the_symmetric_estimate :
    {x : ℝ | ∃c : ℝ, 0≤c ∧ c<1/4 ∧ x^2≤c}=Ioo (-1/2) (1/2) := by
  ext x
  constructor
  · rintro ⟨c,hc,hsmall,hx⟩
    constructor <;> nlinarith [sq_nonneg (x+1/2),sq_nonneg (x-1/2)]
  · intro hx
    refine ⟨x^2,sq_nonneg x,?_,le_rfl⟩
    have hm := mul_neg_of_pos_of_neg (by linarith [hx.1] : 0<x+1/2)
      (by linarith [hx.2] : x-1/2<0)
    nlinarith

theorem actual_symmetric_certified_estimate_is_strictly_smaller_than_the_true_basin :
    Ioo (-1/2:ℝ) (1/2) ⊂ Ioo (-1) (1/2) ∧
      (-3/4:ℝ)∈Ioo (-1) (1/2) ∧ (-3/4:ℝ)∉Ioo (-1/2) (1/2) := by
  refine ⟨?_,by norm_num,by norm_num⟩
  constructor
  · intro x hx
    exact ⟨by linarith [hx.1],hx.2⟩
  · intro h
    have hh := h (show (-3/4:ℝ)∈Ioo (-1) (1/2) by norm_num)
    norm_num at hh

end SafeLearning.CompleteAppliedDiscreteLyapunovMatrix
