import SafeLearning.CompleteAppliedPendulumLinear

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedPendulumSampling
open SafeLearning.CompleteAppliedPendulumLinear

def eulerMatrix (h:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := 1+(1/10:ℝ) • matrix h
def eulerComplexMatrix (h:ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (eulerMatrix h).map Complex.ofReal
def hangingEulerPlus : ℂ := 1+hangingPlus/10
def hangingEulerMinus : ℂ := 1+hangingMinus/10
def uprightEulerPlus : ℝ := 1+uprightPlus/10
def uprightEulerMinus : ℝ := 1+uprightMinus/10
def step (x:ℝ×ℝ) : ℝ×ℝ := (x.1+x.2/10,-x.1+99*x.2/100)
def trajectory (x:ℝ×ℝ) : ℕ→ℝ×ℝ := fun n => step^[n] x
def energy (x:ℝ×ℝ) : ℝ := 10*x.1^2+x.2^2+x.1*x.2/10

theorem actual_euler_matrices_and_hanging_step (x:ℝ×ℝ) :
    eulerMatrix (-10)=!![1,1/10;-1,99/100] ∧
      eulerMatrix 10=!![1,1/10;1,99/100] ∧
      (eulerMatrix (-10)).mulVec ![x.1,x.2]=![ (step x).1,(step x).2] := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [eulerMatrix,matrix]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [eulerMatrix,matrix]
  · have he : eulerMatrix (-10)=!![1,1/10;-1,99/100] := by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [eulerMatrix,matrix]
    rw [he]
    ext i; fin_cases i <;>
      norm_num [Matrix.mulVec,Fin.sum_univ_two,step] <;> ring

theorem actual_euler_official_complex_characteristic_equation (h:ℝ) (z:ℂ) :
    z∈spectrum ℂ (eulerComplexMatrix h) ↔
      z^2-(199/100:ℂ)*z+99/100-(h:ℂ)/100=0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (eulerComplexMatrix h).charpoly.eval z=0 ↔ _
  have he : (eulerComplexMatrix h).charpoly.eval z=
      z^2-(199/100:ℂ)*z+99/100-(h:ℂ)/100 := by
    rw [Matrix.charpoly_fin_two]
    simp [eulerComplexMatrix,eulerMatrix,matrix,Matrix.trace,Fin.sum_univ_two,
      Matrix.det_fin_two]
    ring
  rw [he]

theorem actual_hanging_euler_official_spectrum (z:ℂ) :
    z∈spectrum ℂ (eulerComplexMatrix (-10)) ↔
      z=hangingEulerPlus ∨ z=hangingEulerMinus := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3999)
  have hf : z^2-(199/100:ℂ)*z+99/100-((-10:ℝ):ℂ)/100=
      (z-hangingEulerPlus)*(z-hangingEulerMinus) := by
    apply Complex.ext <;>
      simp [hangingEulerPlus,hangingEulerMinus,hangingPlus,hangingMinus,
        Complex.mul_re,Complex.mul_im,pow_two] <;> nlinarith
  rw [actual_euler_official_complex_characteristic_equation,hf,
    mul_eq_zero,sub_eq_zero,sub_eq_zero]

theorem actual_upright_euler_official_spectrum (z:ℂ) :
    z∈spectrum ℂ (eulerComplexMatrix 10) ↔
      z=(uprightEulerPlus:ℂ) ∨ z=(uprightEulerMinus:ℂ) := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤4001)
  have hf : z^2-(199/100:ℂ)*z+99/100-((10:ℝ):ℂ)/100=
      (z-(uprightEulerPlus:ℂ))*(z-(uprightEulerMinus:ℂ)) := by
    apply Complex.ext <;>
      simp [uprightEulerPlus,uprightEulerMinus,uprightPlus,uprightMinus,
        Complex.mul_re,Complex.mul_im,pow_two] <;> nlinarith
  rw [actual_euler_official_complex_characteristic_equation,hf,
    mul_eq_zero,sub_eq_zero,sub_eq_zero]

theorem actual_hanging_euler_moduli_exceed_one :
    hangingEulerPlus.re=199/200 ∧ hangingEulerMinus.re=199/200 ∧
      Complex.normSq hangingEulerPlus=109/100 ∧
      Complex.normSq hangingEulerMinus=109/100 ∧
      1<‖hangingEulerPlus‖ ∧ 1<‖hangingEulerMinus‖ := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3999)
  have hp : Complex.normSq hangingEulerPlus=109/100 := by
    norm_num [hangingEulerPlus,hangingPlus,Complex.normSq_apply] <;> nlinarith
  have hm : Complex.normSq hangingEulerMinus=109/100 := by
    norm_num [hangingEulerMinus,hangingMinus,Complex.normSq_apply] <;> nlinarith
  refine ⟨?_,?_,hp,hm,?_,?_⟩
  · norm_num [hangingEulerPlus,hangingPlus]
  · norm_num [hangingEulerMinus,hangingMinus]
  · have hn:=Complex.normSq_eq_norm_sq hangingEulerPlus
    have hpos:=norm_nonneg hangingEulerPlus
    rw [hp] at hn
    nlinarith
  · have hn:=Complex.normSq_eq_norm_sq hangingEulerMinus
    have hpos:=norm_nonneg hangingEulerMinus
    rw [hm] at hn
    nlinarith

theorem actual_upright_euler_is_a_saddle :
    1<uprightEulerPlus ∧ 0<uprightEulerMinus ∧ uprightEulerMinus<1 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤4001)
  have hp:=Real.sqrt_nonneg (4001:ℝ)
  dsimp [uprightEulerPlus,uprightEulerMinus,uprightPlus,uprightMinus]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem actual_exact_sample_eigenvalue_moduli_are_strictly_below_one :
    ‖Complex.exp (hangingPlus/10)‖=Real.exp (-1/200) ∧
      ‖Complex.exp (hangingMinus/10)‖=Real.exp (-1/200) ∧
      Real.exp (-1/200)<1 := by
  constructor
  · rw [Complex.norm_exp]
    congr 1
    norm_num [hangingPlus]
  constructor
  · rw [Complex.norm_exp]
    congr 1
    norm_num [hangingMinus]
  · exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem actual_hanging_energy_completion_and_positive_definiteness (x:ℝ×ℝ) :
    energy x=(x.2+x.1/20)^2+(3999/400:ℝ)*x.1^2 ∧
      (energy x=0 ↔ x=0) ∧ (0<energy x ↔ x≠0) := by
  have he : energy x=(x.2+x.1/20)^2+(3999/400:ℝ)*x.1^2 := by
    dsimp [energy]; ring
  have hn : 0≤energy x := by rw [he]; positivity
  have hz : energy x=0 ↔ x=0 := by
    constructor
    · intro h
      have hx : x.1=0 := by
        have := sq_nonneg (x.2+x.1/20)
        have := sq_nonneg x.1
        rw [he] at h
        nlinarith
      have hy : x.2=0 := by
        rw [he,hx] at h
        nlinarith [sq_nonneg x.2]
      exact Prod.ext hx hy
    · intro h; simp [h,energy]
  refine ⟨he,hz,?_⟩
  exact ⟨fun h hx => by simpa [hx,energy] using h,
    fun h => lt_of_le_of_ne hn (Ne.symm (mt hz.mp h))⟩

theorem actual_hanging_euler_energy_recursion (x:ℝ×ℝ) :
    energy (step x)=(109/100:ℝ)*energy x := by
  dsimp [energy,step]; ring

theorem actual_hanging_euler_trajectory_energy (x:ℝ×ℝ) (n:ℕ) :
    energy (trajectory x n)=(109/100:ℝ)^n*energy x := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    rw [trajectory,Function.iterate_succ_apply']
    rw [actual_hanging_euler_energy_recursion]
    change (109/100:ℝ)*energy (trajectory x n)=_
    rw [ih,pow_succ]; ring

theorem actual_every_nonzero_hanging_euler_trajectory_energy_grows_without_bound
    (x:ℝ×ℝ) (hx:x≠0) :
    Tendsto (fun n => energy (trajectory x n)) atTop atTop := by
  simp_rw [actual_hanging_euler_trajectory_energy]
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<109/100)).atTop_mul_const
    ((actual_hanging_energy_completion_and_positive_definiteness x).2.2.mpr hx)

theorem actual_every_nonzero_hanging_euler_trajectory_fails_to_converge_to_zero
    (x:ℝ×ℝ) (hx:x≠0) : ¬Tendsto (trajectory x) atTop (nhds 0) := by
  intro h
  have hc : Continuous energy := by unfold energy; fun_prop
  have ht := hc.continuousAt.tendsto.comp h
  have hzero : energy (0:ℝ×ℝ)=0 := by norm_num [energy]
  rw [hzero] at ht
  exact not_tendsto_nhds_of_tendsto_atTop
    (actual_every_nonzero_hanging_euler_trajectory_energy_grows_without_bound x hx) 0 ht

end SafeLearning.CompleteAppliedPendulumSampling
