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
    (![x,w] : Fin 2 → ℝ) ⬝ᵥ (sourceM *ᵥ ![x,w]) ≤
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

def localLoop (activation : ℝ → ℝ) (x : ℝ) : ℝ :=
  (6/5)*x-(activation x)/2
def actualOrbit (activation : ℝ → ℝ) (initial : ℝ) (n : ℕ) : ℝ :=
  (localLoop activation)^[n] initial

theorem actual_contained_local_sector_implies_all_time_invariance_and_energy_bound
    (activation : ℝ → ℝ) (radius initial : ℝ)
    (hstart : initial^2 ≤ radius^2)
    (hlocal : ∀ x : ℝ,x^2 ≤ radius^2 → 0 ≤ sourceQC x (activation x)) :
    ∀ n : ℕ,(actualOrbit activation initial n)^2 ≤ (93/100:ℝ)^n*initial^2 ∧
      (actualOrbit activation initial n)^2 ≤ radius^2 := by
  intro n
  induction n with
  | zero => simp [actualOrbit,hstart]
  | succ n ih =>
    have hs := actual_on_sector_one_step_geometric_energy_bound
      (actualOrbit activation initial n) (activation (actualOrbit activation initial n))
      (hlocal _ ih.2)
    have hn : actualOrbit activation initial (n+1)=
        localLoop activation (actualOrbit activation initial n) := by
      simp [actualOrbit,Function.iterate_succ_apply']
    rw [hn]
    unfold localLoop
    constructor
    · rw [pow_succ]
      nlinarith [ih.1]
    · nlinarith [ih.2,sq_nonneg (actualOrbit activation initial n)]

theorem actual_contained_local_sector_trajectory_converges
    (activation : ℝ → ℝ) (radius initial : ℝ)
    (hstart : initial^2 ≤ radius^2)
    (hlocal : ∀ x : ℝ,x^2 ≤ radius^2 → 0 ≤ sourceQC x (activation x)) :
    Tendsto (actualOrbit activation initial) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (93/100:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hu : Tendsto (fun n : ℕ => (93/100:ℝ)^n*initial^2) atTop (𝓝 0) := by
    simpa only [zero_mul] using hp.mul_const (initial^2)
  have he : Tendsto (fun n : ℕ => (actualOrbit activation initial n)^2)
      atTop (𝓝 0) := by
    exact squeeze_zero (fun n => sq_nonneg _) (fun n =>
      (actual_contained_local_sector_implies_all_time_invariance_and_energy_bound
        activation radius initial hstart hlocal n).1) hu
  have hn : Tendsto (fun n : ℕ => |actualOrbit activation initial n|)
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs,Real.sqrt_zero] using he.sqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hn)

end
end SafeLearning.CompleteModulesNNStabilityLMI23
