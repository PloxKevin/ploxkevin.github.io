import SafeLearning.Modules

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Matrix
namespace SafeLearning.CompleteModulesLeakyReLUQC28

def leaky (a x : ℝ) : ℝ := max x (a*x)
def scalarQC (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-2*a,1+a;1+a,-2]
def qcValue (a x y : ℝ) : ℝ :=
  (![x-y,leaky a x-leaky a y]:Fin 2 → ℝ) ⬝ᵥ
    (scalarQC a *ᵥ (![x-y,leaky a x-leaky a y]:Fin 2 → ℝ))
def sourceTrainingMatrix (a beta t rho w0 w1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-2*a*beta*w0^2*t-rho,(a+beta)*w0*t;
    (a+beta)*w0*t,-2*t+w1^2]
def fixedPositiveSlopeFeasibleWeights : Set (ℝ × ℝ) :=
  {w | (-(sourceTrainingMatrix (1/2) 1 1 1 w.1 w.2)).PosSemidef}
def zeroMultiplierFeasibleWeights (a : ℝ) : Set (ℝ × ℝ) :=
  {w | (-(sourceTrainingMatrix a 1 0 1 w.1 w.2)).PosSemidef}

private theorem leaky_relu_incremental_sector (alpha x y : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    0 ≤ ((max x (alpha*x)-max y (alpha*y))-alpha*(x-y))*
      ((x-y)-(max x (alpha*x)-max y (alpha*y))) := by
  have hx : max x (alpha*x) = if 0 ≤ x then x else alpha*x := by
    split_ifs with h
    · exact max_eq_left (by nlinarith)
    · exact max_eq_right (by nlinarith)
  have hy : max y (alpha*y) = if 0 ≤ y then y else alpha*y := by
    split_ifs with h
    · exact max_eq_left (by nlinarith)
    · exact max_eq_right (by nlinarith)
  rw [hx,hy]
  by_cases hp : 0 ≤ x <;> by_cases hq : 0 ≤ y
  all_goals simp only [hp,hq,if_true,if_false]
  · have hid : (x-y-alpha*(x-y))*((x-y)-(x-y))=0 := by ring
    rw [hid]
  · have h₁ : 0 ≤ x*(1-alpha) := mul_nonneg hp (by linarith)
    have h₂ : 0 ≤ (-y)*(1-alpha) := mul_nonneg (by linarith) (by linarith)
    have hid : ((x-alpha*y)-alpha*(x-y))*((x-y)-(x-alpha*y))=
      (x*(1-alpha))*((-y)*(1-alpha)) := by ring
    rw [hid]; exact mul_nonneg h₁ h₂
  · have hid : ((alpha*x-y)-alpha*(x-y))*((x-y)-(alpha*x-y))=
      (y*(1-alpha))*((-x)*(1-alpha)) := by ring
    rw [hid]
    exact mul_nonneg (mul_nonneg hq (by linarith))
      (mul_nonneg (by linarith) (by linarith))
  · have hid : ((alpha*x-alpha*y)-alpha*(x-y))*((x-y)-(alpha*x-alpha*y))=0 := by ring
    rw [hid]

theorem actual_leaky_activation_piecewise_formula (a x : ℝ) (ha : 0<a) (ha1 : a<1) :
    leaky a x=if 0≤x then x else a*x := by
  split_ifs with hx
  · exact max_eq_left (by nlinarith)
  · exact max_eq_right (by nlinarith)

theorem actual_leaky_activation_is_continuous (a : ℝ) : Continuous (leaky a) :=
  continuous_id.max (continuous_const.mul continuous_id)

theorem actual_leaky_activation_derivatives (a x : ℝ) (ha : 0<a) (ha1 : a<1) :
    (x<0 → HasDerivAt (leaky a) a x) ∧ (0<x → HasDerivAt (leaky a) 1 x) := by
  constructor
  · intro hx
    apply ((hasDerivAt_id x).const_mul a).congr_of_eventuallyEq
    exact (gt_mem_nhds hx).mono (fun y hy=>by
      rw [actual_leaky_activation_piecewise_formula a y ha ha1,if_neg (by linarith)])
  · intro hx
    apply (hasDerivAt_id x).congr_of_eventuallyEq
    exact (lt_mem_nhds hx).mono (fun y hy=>by
      rw [actual_leaky_activation_piecewise_formula a y ha ha1,if_pos (le_of_lt hy)])

theorem actual_leaky_chord_is_slope_restricted (a x y : ℝ) (ha : 0<a) (ha1 : a<1)
    (hxy : x≠y) : a≤(leaky a x-leaky a y)/(x-y) ∧
      (leaky a x-leaky a y)/(x-y)≤1 := by
  have hn : x-y≠0 := sub_ne_zero.mpr hxy
  have hp:=leaky_relu_incremental_sector a x y (le_of_lt ha) (le_of_lt ha1)
  change 0≤(leaky a x-leaky a y-a*(x-y))*((x-y)-(leaky a x-leaky a y)) at hp
  have he : (leaky a x-leaky a y-a*(x-y))*((x-y)-(leaky a x-leaky a y))=
      (x-y)^2*(((leaky a x-leaky a y)/(x-y)-a)*(1-(leaky a x-leaky a y)/(x-y))) := by
    field_simp [hn]
    ring
  rw [he] at hp
  have hs:=nonneg_of_mul_nonneg_left hp (sq_pos_of_ne_zero hn)
  constructor
  · by_contra h
    have hneg : (leaky a x-leaky a y)/(x-y)-a<0 := by linarith
    have hpos : 0<1-(leaky a x-leaky a y)/(x-y) := by linarith
    exact (not_lt_of_ge hs) (mul_neg_of_neg_of_pos hneg hpos)
  · by_contra h
    have hpos : 0<(leaky a x-leaky a y)/(x-y)-a := by linarith
    have hneg : 1-(leaky a x-leaky a y)/(x-y)<0 := by linarith
    exact (not_lt_of_ge hs) (mul_neg_of_pos_of_neg hpos hneg)

theorem actual_incremental_qc_matrix_expansion (a x y : ℝ) :
    qcValue a x y= -2*(leaky a x-leaky a y-a*(x-y))*
      (leaky a x-leaky a y-(x-y)) := by
  simp [qcValue,scalarQC,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_incremental_qc_is_nonnegative (a x y : ℝ) (ha : 0<a) (ha1 : a<1) :
    0≤qcValue a x y := by
  rw [actual_incremental_qc_matrix_expansion]
  have h:=leaky_relu_incremental_sector a x y (le_of_lt ha) (le_of_lt ha1)
  change 0≤(leaky a x-leaky a y-a*(x-y))*((x-y)-(leaky a x-leaky a y)) at h
  nlinarith

theorem actual_qc_equality_iff_zero_chord_or_endpoint_slope (a x y : ℝ) (hxy : x≠y) :
    qcValue a x y=0 ↔ (leaky a x-leaky a y)/(x-y)=a ∨
      (leaky a x-leaky a y)/(x-y)=1 := by
  have hn : x-y≠0 := sub_ne_zero.mpr hxy
  rw [actual_incremental_qc_matrix_expansion]
  constructor
  · intro h
    have hz : (leaky a x-leaky a y-a*(x-y))*(leaky a x-leaky a y-(x-y))=0 := by nlinarith
    rcases mul_eq_zero.mp hz with h|h
    · left;apply (div_eq_iff hn).mpr;linarith
    · right;apply (div_eq_iff hn).mpr;linarith
  · rintro (h|h)
    · have he:leaky a x-leaky a y=a*(x-y) := (div_eq_iff hn).mp h
      rw [he];ring
    · have he:leaky a x-leaky a y=x-y := by simpa using (div_eq_iff hn).mp h
      rw [he];ring

theorem actual_zero_input_chord_has_qc_equality (a x : ℝ) : qcValue a x x=0 := by
  rw [actual_incremental_qc_matrix_expansion];ring

theorem actual_same_sign_chords_have_qc_equality (a x y : ℝ) (ha : 0<a) (ha1 : a<1)
    (hside : (0≤x ∧ 0≤y) ∨ (x≤0 ∧ y≤0)) : qcValue a x y=0 := by
  rw [actual_incremental_qc_matrix_expansion]
  rcases hside with ⟨hx,hy⟩|⟨hx,hy⟩
  · rw [show leaky a x=x from max_eq_left (by nlinarith),
      show leaky a y=y from max_eq_left (by nlinarith)];ring
  · rw [show leaky a x=a*x from max_eq_right (by nlinarith),
      show leaky a y=a*y from max_eq_right (by nlinarith)];ring

theorem actual_printed_leaky_pair_values_and_qc :
    (2:ℝ)-(-1)=3 ∧ leaky (1/10) 2-leaky (1/10) (-1)=21/10 ∧
    (leaky (1/10) 2-leaky (1/10) (-1))/(2-(-1))=7/10 ∧
    qcValue (1/10) 2 (-1)=81/25 := by
  norm_num [leaky,qcValue,scalarQC,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem actual_zero_lower_slope_qc_is_still_valid (a x y : ℝ) (ha : 0<a) (ha1 : a<1) :
    0≤(leaky a x-leaky a y)*((x-y)-(leaky a x-leaky a y)) := by
  by_cases hxy : x=y
  · subst y;simp
  · have h:=actual_leaky_chord_is_slope_restricted a x y ha ha1 hxy
    have hn : x-y≠0 := sub_ne_zero.mpr hxy
    have he : (leaky a x-leaky a y)*((x-y)-(leaky a x-leaky a y))=
        (x-y)^2*((leaky a x-leaky a y)/(x-y)*(1-(leaky a x-leaky a y)/(x-y))) := by
      field_simp [hn];ring
    rw [he]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith [h.1]) (by linarith [h.2]))

theorem actual_zero_lower_slope_is_strictly_conservative (a : ℝ) (ha : 0<a) (ha1 : a<1) :
    qcValue a (-1) (-2)=0 ∧
      0<(leaky a (-1)-leaky a (-2))*((-1-(-2))-(leaky a (-1)-leaky a (-2))) := by
  constructor
  · exact actual_same_sign_chords_have_qc_equality a (-1) (-2) ha ha1 (by norm_num)
  · rw [show leaky a (-1)= -a from by dsimp [leaky];rw [max_eq_right (by nlinarith)];ring,
      show leaky a (-2)= -2*a from by dsimp [leaky];rw [max_eq_right (by nlinarith)];ring]
    nlinarith [mul_pos ha (sub_pos.mpr ha1)]

theorem actual_fixed_positive_lower_slope_training_endpoints_are_feasible :
    ((1,9/10):ℝ × ℝ)∈fixedPositiveSlopeFeasibleWeights ∧
    ((2,11/25):ℝ × ℝ)∈fixedPositiveSlopeFeasibleWeights := by
  constructor
  all_goals apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j;fin_cases i <;> fin_cases j <;>
      norm_num [sourceTrainingMatrix,Matrix.conjTranspose_apply]
  · intro v
    have he : v ⬝ᵥ ((-(sourceTrainingMatrix (1/2) 1 1 1 1 (9/10))) *ᵥ v)=
        2*(v 0-(3/4)*v 1)^2+(13/200)*(v 1)^2 := by
      simp [sourceTrainingMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ];ring
    simpa only [star_trivial] using (show 0≤v ⬝ᵥ ((-(sourceTrainingMatrix (1/2) 1 1 1 1 (9/10))) *ᵥ v) by
      rw [he];positivity)
  · ext i j;fin_cases i <;> fin_cases j <;>
      norm_num [sourceTrainingMatrix,Matrix.conjTranspose_apply]
  · intro v
    have he : v ⬝ᵥ ((-(sourceTrainingMatrix (1/2) 1 1 1 2 (11/25))) *ᵥ v)=
        5*(v 0-(3/5)*v 1)^2+(4/625)*(v 1)^2 := by
      simp [sourceTrainingMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ];ring
    simpa only [star_trivial] using (show 0≤v ⬝ᵥ ((-(sourceTrainingMatrix (1/2) 1 1 1 2 (11/25))) *ᵥ v) by
      rw [he];positivity)

theorem actual_fixed_positive_lower_slope_training_midpoint_is_infeasible :
    ((3/2,67/100):ℝ × ℝ)∉fixedPositiveSlopeFeasibleWeights := by
  intro h
  have hv:=h.dotProduct_mulVec_nonneg (![9/13,1]:Fin 2 → ℝ)
  norm_num [sourceTrainingMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hv

theorem actual_fixed_positive_lower_slope_training_set_need_not_be_convex :
    ¬Convex ℝ fixedPositiveSlopeFeasibleWeights := by
  intro h
  have hm:=h actual_fixed_positive_lower_slope_training_endpoints_are_feasible.1
    actual_fixed_positive_lower_slope_training_endpoints_are_feasible.2
    (a:=(1/2:ℝ)) (b:=(1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have he : (1/2:ℝ) • ((1,9/10):ℝ × ℝ)+(1/2:ℝ) • ((2,11/25):ℝ × ℝ)=
      ((3/2,67/100):ℝ × ℝ) := by norm_num
  rw [he] at hm
  exact actual_fixed_positive_lower_slope_training_midpoint_is_infeasible hm

end SafeLearning.CompleteModulesLeakyReLUQC28
