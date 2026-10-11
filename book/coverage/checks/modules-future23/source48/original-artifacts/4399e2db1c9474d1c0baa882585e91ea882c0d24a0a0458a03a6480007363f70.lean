import SafeLearning.CompleteFoundationsQuadraticForms

open Matrix Polynomial Set Filter
open scoped Topology
namespace SafeLearning.CompleteModulesNNStabilityLMI23
noncomputable section

def sourceM : Matrix (Fin 2) (Fin 2) ℝ := !![-14/25,9/10;9/10,-7/4]
def sourceQC (x w : ℝ) : ℝ := 2*(w-x/2)*(x-w)
def sourceDelta (x w : ℝ) : ℝ := ((6/5)*x-w/2)^2-x^2
def smallEigenvalue : ℝ := (-231-Real.sqrt 46561)/200
def largeEigenvalue : ℝ := (-231+Real.sqrt 46561)/200

theorem actual_lyapunov_and_qc_expansions (x w : ℝ) :
    sourceDelta x w=(11/25)*x^2-(6/5)*x*w+(1/4)*w^2 ∧
      sourceQC x w=-x^2+3*x*w-2*w^2 ∧
      sourceDelta x w+sourceQC x w=-(14/25)*x^2+(9/5)*x*w-(7/4)*w^2 := by
  unfold sourceDelta sourceQC
  constructor
  · ring
  constructor <;> ring

theorem actual_printed_matrix_and_determinant (x w : ℝ) :
    sourceM 0 0=-(14/25) ∧ sourceM.det=17/100 ∧
      sourceDelta x w+sourceQC x w=(![x,w] : Fin 2 → ℝ) ⬝ᵥ (sourceM *ᵥ ![x,w]) := by
  refine ⟨by norm_num [sourceM],by norm_num [sourceM,Matrix.det_fin_two],?_⟩
  simp [sourceM,sourceDelta,sourceQC,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_negative_definiteness_from_the_true_two_by_two_criterion :
    (-sourceM).PosDef := by
  have he : -sourceM=SafeLearning.CompleteFoundationsQuadraticForms.planeMatrix
      (14/25) (-9/10) (7/4) := by
    ext i j;fin_cases i <;> fin_cases j <;>
      norm_num [sourceM,SafeLearning.CompleteFoundationsQuadraticForms.planeMatrix]
  rw [he,SafeLearning.CompleteFoundationsQuadraticForms.plane_pd_criterion]
  norm_num

theorem actual_exact_full_official_spectrum (v : ℝ) :
    v ∈ spectrum ℝ sourceM ↔ v=smallEigenvalue ∨ v=largeEigenvalue := by
  have hc : sourceM.charpoly.eval v=v^2+(231/100)*v+17/100 := by
    rw [Matrix.charpoly_fin_two]
    simp [sourceM,Matrix.trace,Matrix.det_fin_two,Fin.sum_univ_two]
    ring
  have hs : (Real.sqrt (46561:ℝ))^2=46561 := Real.sq_sqrt (by norm_num)
  have he : (v-smallEigenvalue)*(v-largeEigenvalue)=v^2+(231/100)*v+17/100 := by
    unfold smallEigenvalue largeEigenvalue
    nlinarith [hs]
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,hc,←he]
  simp [mul_eq_zero,sub_eq_zero]

theorem actual_source_eigenvalue_roundings_are_rigorous :
    |smallEigenvalue-(-223390/100000:ℝ)|<1/200000 ∧
      |largeEigenvalue-(-761001/10000000:ℝ)|<1/20000000 ∧
      (-223390/100000:ℝ)<smallEigenvalue ∧
      (-761001/10000000:ℝ)<largeEigenvalue := by
  have hs : (Real.sqrt (46561:ℝ))^2=46561 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (46561:ℝ)
  have hl : (21577998/100000:ℝ)<Real.sqrt 46561 := by nlinarith
  have hu : Real.sqrt (46561:ℝ)<21577999/100000 := by nlinarith
  unfold smallEigenvalue largeEigenvalue
  rw [abs_lt,abs_lt]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor <;> linarith

theorem actual_sector_qc_is_nonnegative (x d : ℝ) (hd : d ∈ Icc (1/2:ℝ) 1) :
    0 ≤ sourceQC x (d*x) := by
  have he : sourceQC x (d*x)=2*(d-1/2)*(1-d)*x^2 := by
    unfold sourceQC;ring
  rw [he]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hd.1]))
    (by linarith [hd.2])) (sq_nonneg x)

theorem actual_on_sector_the_energy_strictly_decreases (x w : ℝ)
    (hq : 0 ≤ sourceQC x w) (hx : x ≠ 0) : sourceDelta x w<0 := by
  have hn : (![x,w] : Fin 2 → ℝ)≠0 := by
    intro hz;have he:=congrFun hz 0;simp at he;exact hx he
  have hp := actual_negative_definiteness_from_the_true_two_by_two_criterion.dotProduct_mulVec_pos hn
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg] at hp
  have he := (actual_printed_matrix_and_determinant x w).2.2
  linarith

theorem actual_uniform_energy_margin (x w : ℝ) :
    (! [x,w] : Fin 2 → ℝ) ⬝ᵥ (sourceM *ᵥ ![x,w]) ≤
      -(7/100)*(x^2+w^2) := by
  have hp : (SafeLearning.CompleteFoundationsQuadraticForms.planeMatrix
      (49/100) (-9/10) (42/25)).PosDef := by
    rw [SafeLearning.CompleteFoundationsQuadraticForms.plane_pd_criterion];norm_num
  have hn := hp.posSemidef.dotProduct_mulVec_nonneg (![x,w] : Fin 2 → ℝ)
  simp [SafeLearning.CompleteFoundationsQuadraticForms.planeMatrix,
    sourceM,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at *
  nlinarith

theorem actual_on_sector_one_step_geometric_energy_bound (x w : ℝ)
    (hq : 0 ≤ sourceQC x w) :
    ((6/5)*x-w/2)^2 ≤ (93/100)*x^2 := by
  have hm := actual_uniform_energy_margin x w
  have he := (actual_printed_matrix_and_determinant x w).2.2
  unfold sourceDelta at he
  nlinarith [sq_nonneg w]

end
end SafeLearning.CompleteModulesNNStabilityLMI23
