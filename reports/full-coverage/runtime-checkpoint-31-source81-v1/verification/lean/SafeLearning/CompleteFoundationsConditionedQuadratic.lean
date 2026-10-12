import SafeLearning.CompleteFoundationsAlgorithms
import SafeLearning.CompleteFoundationsGridExamples
import SafeLearning.CompleteFoundationsMatrixNormModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator

namespace SafeLearning.CompleteFoundationsConditionedQuadratic

abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
def objective (a b : ℝ) (x : E) : ℝ := (a*(x 0)^2+b*(x 1)^2)/2
def curvatureMatrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![a,b]
def hessian (a b : ℝ) : E →L[ℝ] E := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (curvatureMatrix a b)
def coordinate (i : Fin 2) : E →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i

theorem actual_hessian_coordinates (a b : ℝ) (x : E) :
    hessian a b x=point (a*x 0) (b*x 1) := by
  ext i
  change (curvatureMatrix a b *ᵥ (x : Fin 2 → ℝ)) i=(![a*x 0,b*x 1] : Fin 2 → ℝ) i
  fin_cases i <;> simp [curvatureMatrix,Matrix.mulVec_diagonal]

theorem actual_frechet_derivative (a b : ℝ) (x : E) :
    HasFDerivAt (objective a b) ((a*x 0) • coordinate 0+(b*x 1) • coordinate 1) x := by
  have h0 := (coordinate 0).hasFDerivAt (x := x)
  have h1 := (coordinate 1).hasFDerivAt (x := x)
  convert (((h0.pow 2).const_mul a).add ((h1.pow 2).const_mul b)).const_mul (1/2) using 1
  · funext y; simp [objective,coordinate,PiLp.proj,PiLp.projₗ];ring
  · ext u
    simp [coordinate,PiLp.proj,PiLp.projₗ]
    ring

theorem actual_gradient (a b : ℝ) (x : E) : HasGradientAt (objective a b) (hessian a b x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert actual_frechet_derivative a b x using 1
  ext u
  rw [actual_hessian_coordinates]
  simp [point,coordinate,InnerProductSpace.toDual_apply_apply,PiLp.inner_apply,
    Fin.sum_univ_succ,PiLp.proj,PiLp.projₗ]
  ring

theorem gradient_identification (a b : ℝ) : gradient (objective a b)=hessian a b := by
  funext x
  exact (actual_gradient a b x).gradient

theorem actual_hessian_derivative (a b : ℝ) (x : E) :
    HasFDerivAt (gradient (objective a b)) (hessian a b) x := by
  rw [gradient_identification]
  exact (hessian a b).hasFDerivAt

def gradientStep (a b eta : ℝ) (x : E) : E := x-eta • gradient (objective a b) x

theorem actual_gradient_step (a b eta : ℝ) (x : E) :
    gradientStep a b eta x=point ((1-eta*a)*x 0) ((1-eta*b)*x 1) := by
  rw [gradientStep,gradient_identification,actual_hessian_coordinates]
  ext i
  fin_cases i <;> simp [point] <;> ring

theorem actual_source_trajectory (eta : ℝ) (n : ℕ) :
    (gradientStep 1 10 eta)^[n] (point 10 1)=
      point (((SafeLearning.CompleteFoundationsAlgorithms.diagonalStep eta)^[n] (10,1)).1)
        (((SafeLearning.CompleteFoundationsAlgorithms.diagonalStep eta)^[n] (10,1)).2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,actual_gradient_step,Function.iterate_succ_apply']
    simp [point,SafeLearning.CompleteFoundationsAlgorithms.diagonalStep,mul_comm]

theorem actual_source_objective (u : ℝ × ℝ) :
    objective 1 10 (point u.1 u.2)=SafeLearning.CompleteFoundationsAlgorithms.diagonalObjective u := by
  simp [objective,point,SafeLearning.CompleteFoundationsAlgorithms.diagonalObjective]

theorem actual_source_iteration_budgets (n : ℕ) :
    (objective 1 10 ((gradientStep 1 10 (1/10))^[n] (point 10 1))≤1/1000000 ↔ 85≤n) ∧
    (objective 1 10 ((gradientStep 1 10 (2/11))^[n] (point 10 1))≤1/1000000 ↔ 45≤n) := by
  simp only [actual_source_trajectory,actual_source_objective]
  exact ⟨SafeLearning.CompleteFoundationsAlgorithms.slow_coordinate_minimal_budget n,
    SafeLearning.CompleteFoundationsAlgorithms.balanced_step_minimal_budget n⟩

theorem actual_newton_correction (a b : ℝ) (ha : a≠0) (hb : b≠0) (x d : E) :
    hessian a b d= -gradient (objective a b) x ↔ d= -x := by
  rw [gradient_identification,actual_hessian_coordinates,actual_hessian_coordinates]
  constructor
  · intro h
    have h0 := congrArg (fun y : E => y 0) h
    have h1 := congrArg (fun y : E => y 1) h
    simp [point] at h0 h1
    have hd0 : d 0= -x 0 := by apply mul_left_cancel₀ ha;linarith
    have hd1 : d 1= -x 1 := by apply mul_left_cancel₀ hb;linarith
    ext i
    fin_cases i <;> simp [hd0,hd1]
  · rintro rfl
    ext i
    fin_cases i <;> simp [point]

theorem actual_newton_step_solves (a b : ℝ) (ha : a≠0) (hb : b≠0) (x d : E)
    (hd : hessian a b d= -gradient (objective a b) x) : x+d=0 := by
  rw [(actual_newton_correction a b ha hb x d).mp hd]
  exact add_neg_cancel x

theorem actual_source_newton_data :
    gradient (objective 1 10) (point 10 1)=point 10 10 ∧
    (hessian 1 10 (point (-10) (-1))= -gradient (objective 1 10) (point 10 1)) ∧
    point 10 1+point (-10) (-1)=0 := by
  rw [gradient_identification,actual_hessian_coordinates]
  constructor
  · norm_num [point]
  constructor
  · rw [actual_hessian_coordinates]
    ext i
    fin_cases i <;> norm_num [point]
  · ext i
    fin_cases i <;> norm_num [point]

def inverseCurvature (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![a⁻¹,b⁻¹]

theorem actual_inverse_curvature (a b : ℝ) (ha : a≠0) (hb : b≠0) :
    (curvatureMatrix a b)⁻¹=inverseCurvature a b := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curvatureMatrix,inverseCurvature,Matrix.mul_apply,Matrix.diagonal,Fin.sum_univ_succ,ha,hb]

theorem actual_source_condition_number :
    ‖curvatureMatrix 1 10‖=10 ∧ ‖(curvatureMatrix 1 10)⁻¹‖=1 ∧
    ‖curvatureMatrix 1 10‖*‖(curvatureMatrix 1 10)⁻¹‖=10 := by
  have hH : ‖curvatureMatrix 1 10‖=10 := by
    rw [curvatureMatrix,SafeLearning.CompleteFoundationsMatrixNormModels.diagonal_two_spectral_norm]
    norm_num
  have hI : ‖(curvatureMatrix 1 10)⁻¹‖=1 := by
    rw [actual_inverse_curvature 1 10 (by norm_num) (by norm_num),inverseCurvature,
      SafeLearning.CompleteFoundationsMatrixNormModels.diagonal_two_spectral_norm]
    norm_num
  exact ⟨hH,hI,by rw [hH,hI];norm_num⟩

theorem actual_inner_coordinates (x y : E) : inner ℝ x y=x 0*y 0+x 1*y 1 := by
  simp [PiLp.inner_apply,Fin.sum_univ_succ]
  ring

theorem actual_source_curvature_bounds (x : E) :
    ‖x‖^2 ≤ inner ℝ x (hessian 1 10 x) ∧ inner ℝ x (hessian 1 10 x)≤10*‖x‖^2 := by
  rw [actual_hessian_coordinates]
  have hn : ‖x‖^2=(x 0)^2+(x 1)^2 := by
    rw [← real_inner_self_eq_norm_sq,actual_inner_coordinates]
    ring
  rw [hn]
  simp [point,PiLp.inner_apply,Fin.sum_univ_succ]
  constructor <;> nlinarith [sq_nonneg (x 1),sq_nonneg (x 0)]

def contraction (mu L eta : ℝ) : ℝ := max |1-eta*mu| |1-eta*L|

theorem generic_best_constant_step (mu L : ℝ) (hmu : 0 < mu) (hL : mu≤L) (eta : ℝ) :
    (L-mu)/(L+mu)≤contraction mu L eta ∧
      (contraction mu L eta=(L-mu)/(L+mu) ↔ eta=2/(L+mu)) := by
  have hLp : 0 < L := hmu.trans_le hL
  have hsum : 0 < L+mu := add_pos hLp hmu
  have h1 : 1-eta*mu≤contraction mu L eta :=
    (le_abs_self _).trans (le_max_left _ _)
  have h2 : -(1-eta*L)≤contraction mu L eta :=
    (neg_le_abs _).trans (le_max_right _ _)
  constructor
  · apply (div_le_iff₀ hsum).mpr
    nlinarith
  · constructor
    · intro he
      rw [he] at h1 h2
      have hr : (L+mu)*((L-mu)/(L+mu))=L-mu := by field_simp
      have h1m := mul_le_mul_of_nonneg_left h1 hsum.le
      have h2m := mul_le_mul_of_nonneg_left h2 hsum.le
      rw [hr] at h1m h2m
      apply (eq_div_iff hsum.ne').mpr
      nlinarith
    · rintro rfl
      have he1 : 1-2/(L+mu)*mu=(L-mu)/(L+mu) := by field_simp;ring
      have he2 : 1-2/(L+mu)*L= -((L-mu)/(L+mu)) := by field_simp;ring
      have hp : 0≤(L-mu)/(L+mu) := div_nonneg (sub_nonneg.mpr hL) hsum.le
      simp [contraction,he1,he2,abs_of_nonneg hp]

theorem generic_interval_factor_bound (mu L eta a : ℝ) (ha : mu≤a) (hb : a≤L) :
    |1-eta*a|≤contraction mu L eta := by
  have hmu := abs_le.mp ((le_max_left |1-eta*mu| |1-eta*L|) : |1-eta*mu|≤contraction mu L eta)
  have hL := abs_le.mp ((le_max_right |1-eta*mu| |1-eta*L|) : |1-eta*L|≤contraction mu L eta)
  change -contraction mu L eta≤1-eta*mu ∧ 1-eta*mu≤contraction mu L eta at hmu
  change -contraction mu L eta≤1-eta*L ∧ 1-eta*L≤contraction mu L eta at hL
  apply abs_le.mpr
  by_cases heta : 0≤eta
  · constructor <;> nlinarith
  · have heta' : eta≤0 := le_of_not_ge heta
    constructor <;> nlinarith

theorem generic_actual_diagonal_update_norm {N : Type*} [Fintype N] [DecidableEq N]
    (a : N → ℝ) (mu L eta : ℝ) (hinterval : ∀ i,mu≤a i ∧ a i≤L)
    (imin imax : N) (hmin : a imin=mu) (hmax : a imax=L) :
    ‖(1 : Matrix N N ℝ)-eta • Matrix.diagonal a‖=contraction mu L eta := by
  have hm : (1 : Matrix N N ℝ)-eta • Matrix.diagonal a=Matrix.diagonal (fun i => 1-eta*a i) := by
    ext i j
    by_cases hij : i=j
    · subst j;simp
    · simp [Matrix.diagonal,Matrix.one_apply,hij]
  rw [hm,Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg _))).mpr
    intro i
    change |1-eta*a i|≤contraction mu L eta
    exact generic_interval_factor_bound mu L eta (a i) (hinterval i).1 (hinterval i).2
  · apply max_le
    · simpa [hmin,Real.norm_eq_abs] using norm_le_pi_norm (fun i => 1-eta*a i) imin
    · simpa [hmax,Real.norm_eq_abs] using norm_le_pi_norm (fun i => 1-eta*a i) imax

theorem generic_quadratic_optimal_step {N : Type*} [Fintype N] [DecidableEq N]
    (a : N → ℝ) (mu L : ℝ) (hmu : 0 < mu) (hL : mu≤L)
    (hinterval : ∀ i,mu≤a i ∧ a i≤L) (imin imax : N) (hmin : a imin=mu) (hmax : a imax=L)
    (eta : ℝ) :
    (L-mu)/(L+mu)≤‖(1 : Matrix N N ℝ)-eta • Matrix.diagonal a‖ ∧
    (‖(1 : Matrix N N ℝ)-eta • Matrix.diagonal a‖=(L-mu)/(L+mu) ↔ eta=2/(L+mu)) := by
  rw [generic_actual_diagonal_update_norm a mu L eta hinterval imin imax hmin hmax]
  exact generic_best_constant_step mu L hmu hL eta

theorem actual_symmetric_quadratic_optimal_step {N : Type*} [Fintype N] [DecidableEq N]
    (H : Matrix N N ℝ) (hH : H.IsHermitian) (mu L : ℝ) (hmu : 0 < mu) (hL : mu≤L)
    (hinterval : ∀ i,mu≤hH.eigenvalues i ∧ hH.eigenvalues i≤L)
    (imin imax : N) (hmin : hH.eigenvalues imin=mu) (hmax : hH.eigenvalues imax=L)
    (eta : ℝ) :
    (L-mu)/(L+mu)≤‖(1 : Matrix N N ℝ)-eta • H‖ ∧
    (‖(1 : Matrix N N ℝ)-eta • H‖=(L-mu)/(L+mu) ↔ eta=2/(L+mu)) := by
  have he : H=Unitary.conjStarAlgAut ℝ (Matrix N N ℝ) hH.eigenvectorUnitary
      (Matrix.diagonal hH.eigenvalues) := by
    simpa using hH.spectral_theorem
  have hm : (1 : Matrix N N ℝ)-eta • H=
      Unitary.conjStarAlgAut ℝ (Matrix N N ℝ) hH.eigenvectorUnitary
        (1-eta • Matrix.diagonal hH.eigenvalues) := by
    rw [map_sub,map_one,map_smul,← he]
  rw [hm,Unitary.conjStarAlgAut_apply]
  simp only [← Unitary.coe_star,CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  exact generic_quadratic_optimal_step hH.eigenvalues mu L hmu hL hinterval imin imax hmin hmax eta

theorem actual_diagonal_update_norm (mu L eta : ℝ) :
    ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)-eta • curvatureMatrix mu L‖=contraction mu L eta := by
  have hm : (1 : Matrix (Fin 2) (Fin 2) ℝ)-eta • curvatureMatrix mu L=
      Matrix.diagonal ![1-eta*mu,1-eta*L] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [curvatureMatrix,Matrix.diagonal,Matrix.one_apply]
  rw [hm,SafeLearning.CompleteFoundationsMatrixNormModels.diagonal_two_spectral_norm]
  rfl

theorem actual_source_step_factors :
    1-(1/10 : ℝ)=9/10 ∧ 1-10*(1/10 : ℝ)=0 ∧
    1-(21/100 : ℝ)=79/100 ∧ 1-10*(21/100 : ℝ)= -11/10 ∧
    (2/(10+1) : ℝ)=2/11 ∧ |1-(2/11 : ℝ)|=9/11 ∧ |1-10*(2/11 : ℝ)|=9/11 ∧
    (21/100 : ℝ)>2/10 := by norm_num

theorem actual_unstable_ten_percent (n : ℕ) :
    |((gradientStep 1 10 (21/100))^[n+1] (point 10 1)) 1|=
      (11/10 : ℝ)*|((gradientStep 1 10 (21/100))^[n] (point 10 1)) 1| := by
  rw [Function.iterate_succ_apply',actual_gradient_step]
  norm_num [point,abs_mul]

theorem source_log_identities :
    Real.log (50000000 : ℝ)=8*(Real.log (5/4)+3*Real.log 2)-Real.log 2 ∧
    Real.log (55000000 : ℝ)=Real.log (11/8)+2*Real.log 2+7*(Real.log (5/4)+3*Real.log 2) ∧
    Real.log (100/81 : ℝ)=2*Real.log (10/9) ∧ Real.log (121/81 : ℝ)=2*Real.log (11/9) := by
  have ht : Real.log (10 : ℝ)=Real.log (5/4)+3*Real.log 2 := by
    have hm := Real.log_mul (by norm_num : (5/4 : ℝ)≠0) (by norm_num : (8 : ℝ)≠0)
    have hp := Real.log_pow (2 : ℝ) 3
    norm_num at hm hp
    rw [hm,hp]
  have h50 : Real.log (50000000 : ℝ)=8*Real.log 10-Real.log 2 := by
    have hd := Real.log_div (by norm_num : (10 : ℝ)^8≠0) (by norm_num : (2 : ℝ)≠0)
    rw [Real.log_pow] at hd
    norm_num at hd
    exact hd
  have h55 : Real.log (55000000 : ℝ)=Real.log (11/8)+2*Real.log 2+7*Real.log 10 := by
    have hm := Real.log_mul (by norm_num : (11/8 : ℝ)≠0) (by norm_num : (4 : ℝ)*10^7≠0)
    have hp := Real.log_mul (by norm_num : (4 : ℝ)≠0) (by norm_num : (10 : ℝ)^7≠0)
    have h4 := Real.log_pow (2 : ℝ) 2
    norm_num at hm hp h4
    have h10 := Real.log_pow (10 : ℝ) 7
    norm_num at h10
    rw [hm,hp,h4,h10]
    ring
  refine ⟨ht ▸ h50,ht ▸ h55,?_,?_⟩
  · have hp := Real.log_pow (10/9 : ℝ) 2
    norm_num at hp
    exact hp
  · have hp := Real.log_pow (11/9 : ℝ) 2
    norm_num at hp
    exact hp

theorem source_logarithmic_thresholds (n : ℕ) (hn : 1≤n) :
    (objective 1 10 ((gradientStep 1 10 (1/10))^[n] (point 10 1))≤1/1000000 ↔
      Real.log (2/100000000 : ℝ)/Real.log (81/100)≤(n : ℝ)) ∧
    (objective 1 10 ((gradientStep 1 10 (2/11))^[n] (point 10 1))≤1/1000000 ↔
      Real.log (55000000 : ℝ)/Real.log (121/81)≤(n : ℝ)) := by
  simp only [actual_source_trajectory,actual_source_objective]
  rw [SafeLearning.CompleteFoundationsAlgorithms.slow_coordinate_objective n hn,
    SafeLearning.CompleteFoundationsAlgorithms.balanced_step_objective n]
  have hs := SafeLearning.CompleteFoundationsGridExamples.geometric_accuracy_log_iff
    (81/100) 50 (1/1000000) n (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb := SafeLearning.CompleteFoundationsGridExamples.geometric_accuracy_log_iff
    (81/121) 55 (1/1000000) n (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hs hb
  have he : Real.log (2/100000000 : ℝ)/Real.log (81/100)=
      Real.log (50000000 : ℝ)/Real.log (100/81) := by
    have hl := Real.log_inv (50000000 : ℝ)
    have hq := Real.log_inv (100/81 : ℝ)
    norm_num at hl hq
    norm_num
    rw [hl,hq]
    ring
  rw [he]
  simpa only [mul_comm] using And.intro hs hb

theorem actual_slow_log_threshold_decimal :
    |Real.log (2/100000000 : ℝ)/Real.log (81/100)-(841/10 : ℝ)|<1/20 := by
  have h5 := Real.sum_range_sub_log_div_le (by norm_num : |(1/9 : ℝ)|<1) 5
  have h10 := Real.sum_range_sub_log_div_le (by norm_num : |(1/19 : ℝ)|<1) 5
  norm_num [Finset.sum_range_succ] at h5 h10
  have h5l := (abs_le.mp h5).1
  have h5u := (abs_le.mp h5).2
  have h10l := (abs_le.mp h10).1
  have h10u := (abs_le.mp h10).2
  have hn : Real.log (2/100000000 : ℝ)= -Real.log (50000000 : ℝ) := by
    have h := Real.log_inv (50000000 : ℝ)
    norm_num at h
    simpa only [show (2/100000000 : ℝ)=1/50000000 by norm_num] using h
  have hd : Real.log (81/100 : ℝ)= -Real.log (100/81 : ℝ) := by
    have h := Real.log_inv (100/81 : ℝ)
    norm_num at h
    exact h
  rw [hn,hd,neg_div_neg_eq,source_log_identities.1,source_log_identities.2.2.1,abs_lt]
  have hpos : 0<2*Real.log (10/9 : ℝ) := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  constructor
  · rw [lt_sub_iff_add_lt,lt_div_iff₀ hpos]
    nlinarith [Real.log_two_gt_d9,Real.log_two_lt_d9]
  · rw [sub_lt_iff_lt_add,div_lt_iff₀ hpos]
    nlinarith [Real.log_two_gt_d9,Real.log_two_lt_d9]

theorem actual_balanced_log_threshold_decimal :
    |Real.log (55000000 : ℝ)/Real.log (121/81)-(444/10 : ℝ)|<1/20 := by
  have h5 := Real.sum_range_sub_log_div_le (by norm_num : |(1/9 : ℝ)|<1) 5
  have h11 := Real.sum_range_sub_log_div_le (by norm_num : |(1/10 : ℝ)|<1) 5
  have h118 := Real.sum_range_sub_log_div_le (by norm_num : |(3/19 : ℝ)|<1) 5
  norm_num [Finset.sum_range_succ] at h5 h11 h118
  have h5l := (abs_le.mp h5).1
  have h5u := (abs_le.mp h5).2
  have h11l := (abs_le.mp h11).1
  have h11u := (abs_le.mp h11).2
  have h118l := (abs_le.mp h118).1
  have h118u := (abs_le.mp h118).2
  rw [source_log_identities.2.1,source_log_identities.2.2.2,abs_lt]
  have hpos : 0<2*Real.log (11/9 : ℝ) := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  constructor
  · rw [lt_sub_iff_add_lt,lt_div_iff₀ hpos]
    nlinarith [Real.log_two_gt_d9,Real.log_two_lt_d9]
  · rw [sub_lt_iff_lt_add,div_lt_iff₀ hpos]
    nlinarith [Real.log_two_gt_d9,Real.log_two_lt_d9]

end SafeLearning.CompleteFoundationsConditionedQuadratic
