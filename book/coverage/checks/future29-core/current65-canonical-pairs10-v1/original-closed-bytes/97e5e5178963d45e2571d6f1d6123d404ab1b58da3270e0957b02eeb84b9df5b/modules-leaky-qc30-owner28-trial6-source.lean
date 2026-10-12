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
    (_ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
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
  all_goals simp only [hp,hq,ite_true,ite_false]
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

theorem actual_leaky_activation_piecewise_formula (a x : ℝ) (_ha : 0<a) (ha1 : a<1) :
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
    have hd : HasDerivAt (fun y : ℝ=>a*y) a x := by
      simpa only [id_eq,mul_one] using ((hasDerivAt_id x).const_mul a)
    apply hd.congr_of_eventuallyEq
    exact (gt_mem_nhds hx).mono (fun y hy=>by
      rw [actual_leaky_activation_piecewise_formula a y ha ha1,ite_eq_right (by linarith)])
  · intro hx
    have hd : HasDerivAt (fun y : ℝ=>y) 1 x := hasDerivAt_id x
    apply hd.congr_of_eventuallyEq
    exact (lt_mem_nhds hx).mono (fun y hy=>by
      rw [actual_leaky_activation_piecewise_formula a y ha ha1,ite_eq_left (le_of_lt hy)])

theorem actual_leaky_chord_is_slope_restricted (a x y : ℝ) (ha : 0<a) (ha1 : a<1)
    (hxy : x≠y) : a≤(leaky a x-leaky a y)/(x-y) ∧
      (leaky a x-leaky a y)/(x-y)≤1 := by
  have hn : x-y≠0 := sub_ne_zero.mpr hxy
  have hp:=leaky_relu_incremental_sector a x y (le_of_lt ha) (le_of_lt ha1)
  change 0≤(leaky a x-leaky a y-a*(x-y))*((x-y)-(leaky a x-leaky a y)) at hp
  have he : (leaky a x-leaky a y-a*(x-y))*((x-y)-(leaky a x-leaky a y))=
      (x-y)^2*(((leaky a x-leaky a y)/(x-y)-a)*(1-(leaky a x-leaky a y)/(x-y))) := by
    field_simp [hn]
  rw [he] at hp
  have hs:=nonneg_of_mul_nonneg_right hp (sq_pos_of_ne_zero hn)
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

theorem actual_same_sign_chords_have_qc_equality (a x y : ℝ) (_ha : 0<a) (ha1 : a<1)
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
      field_simp [hn]
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


def leakySlope (a t : ℝ) : ℝ := if 0≤t then 1 else a

theorem actual_leaky_has_every_right_derivative (a x : ℝ) (ha : 0<a) (ha1 : a<1) :
    HasDerivWithinAt (leaky a) (leakySlope a x) (Ioi x) x := by
  rcases lt_trichotomy x 0 with hn|he|hp
  · simpa only [leakySlope,ite_eq_right (not_le_of_gt hn)] using
      ((actual_leaky_activation_derivatives a x ha ha1).1 hn).hasDerivWithinAt
  · subst x
    simp only [leakySlope,le_refl,ite_true]
    apply (hasDerivWithinAt_id (s:=Ioi (0:ℝ)) (x:=0)).congr
    · intro t ht
      change leaky a t=t
      rw [actual_leaky_activation_piecewise_formula a t ha ha1,ite_eq_left ht.le]
    · simp [leaky]
  · simpa only [leakySlope,ite_eq_left hp.le] using
      ((actual_leaky_activation_derivatives a x ha ha1).2 hp).hasDerivWithinAt

theorem actual_leaky_slope_is_interval_integrable (a x y : ℝ) :
    IntervalIntegrable (leakySlope a) MeasureTheory.volume y x := by
  rw [intervalIntegrable_iff]
  have h1 := (intervalIntegrable_const (c:=(1:ℝ)) (μ:=MeasureTheory.volume)
    (a:=y) (b:=x)).def'
  have ha := (intervalIntegrable_const (c:=a) (μ:=MeasureTheory.volume)
    (a:=y) (b:=x)).def'
  have h1' : MeasureTheory.Integrable (fun _ : ℝ=>(1:ℝ))
      (MeasureTheory.volume.restrict (uIoc y x)) := h1
  have ha' : MeasureTheory.Integrable (fun _ : ℝ=>a)
      (MeasureTheory.volume.restrict (uIoc y x)) := ha
  have hp := MeasureTheory.Integrable.piecewise (s:=Ici (0:ℝ))
      (μ:=MeasureTheory.volume.restrict (uIoc y x)) measurableSet_Ici
      h1'.integrableOn ha'.integrableOn
  apply hp.congr
  exact Filter.Eventually.of_forall (fun t=>by
    simp only [Set.piecewise,Set.mem_Ici,leakySlope])

theorem actual_leaky_slope_integral_is_the_endpoint_increment (a x y : ℝ)
    (ha : 0<a) (ha1 : a<1) :
    (∫ t in y..x, leakySlope a t)=leaky a x-leaky a y := by
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right
    (actual_leaky_activation_is_continuous a).continuousOn
    (fun t _=>actual_leaky_has_every_right_derivative a t ha ha1)
    (actual_leaky_slope_is_interval_integrable a x y)

theorem actual_leaky_slope_equals_the_genuine_derivative_almost_everywhere (a : ℝ)
    (ha : 0<a) (ha1 : a<1) :
    ∀ᵐ t : ℝ ∂MeasureTheory.volume, leakySlope a t=deriv (leaky a) t := by
  have hz : ∀ᵐ t : ℝ ∂MeasureTheory.volume,t≠0 := by
    apply MeasureTheory.ae_iff.mpr
    simp
  filter_upwards [hz] with t ht
  rcases lt_or_gt_of_ne ht with hn|hp
  · rw [((actual_leaky_activation_derivatives a t ha ha1).1 hn).deriv]
    exact ite_eq_right (not_le_of_gt hn)
  · rw [((actual_leaky_activation_derivatives a t ha ha1).2 hp).deriv]
    exact ite_eq_left hp.le

theorem actual_leaky_chord_is_the_average_of_the_genuine_derivative
    (a x y : ℝ) (ha : 0<a) (ha1 : a<1) (hxy : x≠y) :
    (leaky a x-leaky a y)/(x-y)=(∫ t in y..x,deriv (leaky a) t)/(x-y) ∧
    a≤(∫ t in y..x,deriv (leaky a) t)/(x-y) ∧
      (∫ t in y..x,deriv (leaky a) t)/(x-y)≤1 := by
  have he : (∫ t in y..x,deriv (leaky a) t)=leaky a x-leaky a y := by
    rw [←actual_leaky_slope_integral_is_the_endpoint_increment a x y ha ha1]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [actual_leaky_slope_equals_the_genuine_derivative_almost_everywhere a ha ha1]
      with t ht
    intro _
    exact ht.symm
  rw [he]
  exact ⟨rfl,actual_leaky_chord_is_slope_restricted a x y ha ha1 hxy⟩

theorem actual_zero_multiplier_feasible_weights_are_exactly_zero_output (a : ℝ) :
    zeroMultiplierFeasibleWeights a={w : ℝ×ℝ | w.2=0} := by
  ext w
  constructor
  · intro h
    have hv:=h.dotProduct_mulVec_nonneg (![0,1]:Fin 2 → ℝ)
    norm_num [sourceTrainingMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hv
    change w.2=0
    nlinarith [sq_nonneg w.2]
  · intro h
    change w.2=0 at h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [sourceTrainingMatrix,Matrix.conjTranspose_apply,h]
    · intro v
      simpa [sourceTrainingMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h]
        using mul_self_nonneg (v 0)

theorem actual_zero_multiplier_is_a_convex_positive_activation_countermodel (a : ℝ) :
    Convex ℝ (zeroMultiplierFeasibleWeights a) := by
  rw [actual_zero_multiplier_feasible_weights_are_exactly_zero_output]
  intro x hx y hy b c hb hc hbc
  change x.2=0 at hx
  change y.2=0 at hy
  change (b • x+c • y).2=0
  simp [hx,hy]

def negativeGram {ι κ : Type*} [Fintype ι] (a beta : ℝ)
    (T : Matrix ι ι ℝ) (X : Matrix ι κ ℝ) : Matrix κ κ ℝ :=
  (-2*a*beta) • (Xᴴ*T*X)

theorem actual_negative_gram_concavity_deficit_identity {ι κ : Type*} [Fintype ι]
    (a beta theta : ℝ) (T : Matrix ι ι ℝ) (X Y : Matrix ι κ ℝ) :
    negativeGram a beta T (theta • X+(1-theta) • Y)-
      (theta • negativeGram a beta T X+(1-theta) • negativeGram a beta T Y)=
        (2*a*beta*theta*(1-theta)) • ((X-Y)ᴴ*T*(X-Y)) := by
  simp only [negativeGram,Matrix.conjTranspose_add,Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul,star_trivial,Matrix.add_mul,Matrix.mul_add,
    Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem actual_negative_gram_is_matrix_concave {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a beta theta : ℝ) (ha : 0≤a) (hb : 0≤beta) (ht : theta∈Icc 0 1)
    (T : Matrix ι ι ℝ) (hT : T.PosSemidef) (X Y : Matrix ι κ ℝ) :
    (negativeGram a beta T (theta • X+(1-theta) • Y)-
      (theta • negativeGram a beta T X+(1-theta) • negativeGram a beta T Y)).PosSemidef := by
  rw [actual_negative_gram_concavity_deficit_identity]
  apply (hT.conjTranspose_mul_mul_same (X-Y)).smul
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) hb) ht.1)
    (by linarith [ht.2])


theorem actual_opposite_strict_sign_chords_have_strict_qc (a x y : ℝ)
    (ha : 0<a) (ha1 : a<1)
    (hopposite : (0<x ∧ y<0) ∨ (x<0 ∧ 0<y)) : 0<qcValue a x y := by
  rw [actual_incremental_qc_matrix_expansion]
  rcases hopposite with ⟨hx,hy⟩|⟨hx,hy⟩
  · rw [actual_leaky_activation_piecewise_formula a x ha ha1,ite_eq_left hx.le,
      actual_leaky_activation_piecewise_formula a y ha ha1,ite_eq_right (not_le_of_gt hy)]
    have he : -2*(x-a*y-a*(x-y))*(x-a*y-(x-y))=
        2*((1-a)*x)*((1-a)*(-y)) := by ring
    rw [he]
    exact mul_pos (mul_pos (by norm_num) (mul_pos (sub_pos.mpr ha1) hx))
      (mul_pos (sub_pos.mpr ha1) (by linarith))
  · rw [actual_leaky_activation_piecewise_formula a x ha ha1,ite_eq_right (not_le_of_gt hx),
      actual_leaky_activation_piecewise_formula a y ha ha1,ite_eq_left hy.le]
    have he : -2*(a*x-y-a*(x-y))*(a*x-y-(x-y))=
        2*((1-a)*(-x))*((1-a)*y) := by ring
    rw [he]
    exact mul_pos (mul_pos (by norm_num) (mul_pos (sub_pos.mpr ha1) (by linarith)))
      (mul_pos (sub_pos.mpr ha1) hy)

theorem actual_qc_equality_iff_both_points_in_a_common_closed_halfline (a x y : ℝ)
    (ha : 0<a) (ha1 : a<1) :
    qcValue a x y=0 ↔ (0≤x ∧ 0≤y) ∨ (x≤0 ∧ y≤0) := by
  constructor
  · intro h
    by_cases hx : 0≤x
    · by_cases hy : 0≤y
      · exact Or.inl ⟨hx,hy⟩
      · by_cases hx0 : x=0
        · exact Or.inr ⟨by simp [hx0],le_of_not_ge hy⟩
        · have hp : 0<qcValue a x y := actual_opposite_strict_sign_chords_have_strict_qc
            a x y ha ha1 (Or.inl ⟨lt_of_le_of_ne hx (Ne.symm hx0),lt_of_not_ge hy⟩)
          rw [h] at hp
          exact (lt_irrefl (0:ℝ) hp).elim
    · by_cases hy : 0≤y
      · by_cases hy0 : y=0
        · exact Or.inr ⟨le_of_not_ge hx,by simp [hy0]⟩
        · have hp : 0<qcValue a x y := actual_opposite_strict_sign_chords_have_strict_qc
            a x y ha ha1 (Or.inr ⟨lt_of_not_ge hx,lt_of_le_of_ne hy (Ne.symm hy0)⟩)
          rw [h] at hp
          exact (lt_irrefl (0:ℝ) hp).elim
      · exact Or.inr ⟨le_of_not_ge hx,le_of_not_ge hy⟩
  · exact actual_same_sign_chords_have_qc_equality a x y ha ha1


/-- A fixed positive multiplier and zero prescribed bound also provide a convex exception. -/
def zeroBoundPositiveMultiplierFeasibleWeights : Set (ℝ × ℝ) :=
  {w | (-(sourceTrainingMatrix (1/2) 1 1 0 w.1 w.2)).PosSemidef}

theorem actual_positive_multiplier_zero_bound_feasible_weights_characterization :
    zeroBoundPositiveMultiplierFeasibleWeights =
      {w : ℝ × ℝ | w.1=0 ∧ w.2^2≤2} := by
  ext w
  constructor
  · intro h
    have hsecond:=h.dotProduct_mulVec_nonneg (![0,1]:Fin 2 → ℝ)
    have htest:=h.dotProduct_mulVec_nonneg (![3/2,w.1]:Fin 2 → ℝ)
    have he : (![3/2,w.1]:Fin 2 → ℝ) ⬝ᵥ
        ((-(sourceTrainingMatrix (1/2) 1 1 0 w.1 w.2)) *ᵥ
          (![3/2,w.1]:Fin 2 → ℝ)) =
        -(1/4)*w.1^2-(w.1*w.2)^2 := by
      simp [sourceTrainingMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      ring
    simp only [star_trivial] at htest
    rw [he] at htest
    norm_num [sourceTrainingMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hsecond
    change w.1=0 ∧ w.2^2≤2
    constructor
    · nlinarith [sq_nonneg w.1,sq_nonneg (w.1*w.2)]
    · linarith
  · rintro ⟨hw,hb⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [sourceTrainingMatrix,Matrix.conjTranspose_apply,hw]
    · intro v
      have he : v ⬝ᵥ ((-(sourceTrainingMatrix (1/2) 1 1 0 w.1 w.2)) *ᵥ v)=
          (2-w.2^2)*(v 1)^2 := by
        simp [sourceTrainingMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hw]
        ring
      simpa only [star_trivial] using
        (show 0≤v ⬝ᵥ ((-(sourceTrainingMatrix (1/2) 1 1 0 w.1 w.2)) *ᵥ v) by
          rw [he]
          exact mul_nonneg (by linarith) (sq_nonneg _))

theorem actual_positive_multiplier_zero_bound_certified_weights_are_convex :
    Convex ℝ zeroBoundPositiveMultiplierFeasibleWeights := by
  rw [actual_positive_multiplier_zero_bound_feasible_weights_characterization]
  intro x hx y hy b c hb hc hbc
  change x.1=0 ∧ x.2^2≤2 at hx
  change y.1=0 ∧ y.2^2≤2 at hy
  change (b • x+c • y).1=0 ∧ (b • x+c • y).2^2≤2
  constructor
  · simp [hx.1,hy.1]
  · change (b*x.2+c*y.2)^2≤2
    have he : (b*x.2+c*y.2)^2+b*c*(x.2-y.2)^2=
        (b+c)*(b*x.2^2+c*y.2^2) := by ring
    rw [hbc,one_mul] at he
    have hp : 0≤b*c*(x.2-y.2)^2 :=
      mul_nonneg (mul_nonneg hb hc) (sq_nonneg _)
    have hbx:=mul_le_mul_of_nonneg_left hx.2 hb
    have hcy:=mul_le_mul_of_nonneg_left hy.2 hc
    nlinarith

theorem actual_slope_interval_iff_chord_product (a s : ℝ) (ha1 : a<1) :
    (a ≤ s ∧ s ≤ 1) ↔ (s-a)*(s-1)≤0 := by
  constructor
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h.1) (sub_nonpos.mpr h.2)
  · intro h
    constructor
    · by_contra hn
      have hleft : s-a<0 := by linarith
      have hright : s-1<0 := by linarith
      exact (not_lt_of_ge h) (mul_pos_of_neg_of_neg hleft hright)
    · by_contra hn
      have hleft : 0<s-a := by linarith
      have hright : 0<s-1 := by linarith
      exact (not_lt_of_ge h) (mul_pos hleft hright)

theorem actual_zero_lower_slope_removes_negative_gram {ι κ : Type*} [Fintype ι]
    (beta : ℝ) (T : Matrix ι ι ℝ) (X : Matrix ι κ ℝ) :
    negativeGram 0 beta T X=0 := by
  simp [negativeGram]

end SafeLearning.CompleteModulesLeakyReLUQC28
