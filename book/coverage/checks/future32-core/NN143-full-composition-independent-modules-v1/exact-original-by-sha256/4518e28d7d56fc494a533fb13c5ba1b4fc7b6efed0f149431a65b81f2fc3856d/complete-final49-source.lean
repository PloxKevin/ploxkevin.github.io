import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Polynomial Set Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteModulesNNWalkthroughLocal31

/- Exact proposed associations for NN14.3. This source has not been compiled.
The private helper bodies below are copied from already selected supporting
sources; no old source, status, native time or owner metadata is rewritten. -/

private theorem tanh_derivative (x : ℝ) :
    HasDerivAt Real.tanh (1/(Real.cosh x)^2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have hid : Real.cosh x*Real.cosh x-Real.sinh x*Real.sinh x=1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  convert h using 1
  · ext y; exact Real.tanh_eq_sinh_div_cosh y
  · rw [hid]

private theorem tanh_derivative_bounds (x : ℝ) :
    0 ≤ 1/(Real.cosh x)^2 ∧ 1/(Real.cosh x)^2 ≤ 1 := by
  have hc := Real.one_le_cosh x
  have hsq : 1 ≤ (Real.cosh x)^2 := by nlinarith
  constructor
  · positivity
  · exact (div_le_one (by positivity)).mpr hsq

private theorem tanh_lipschitz : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x; exact (tanh_derivative x).differentiableAt
  · intro x
    have hb := tanh_derivative_bounds x
    rw [(tanh_derivative x).deriv]
    exact_mod_cast (show ‖(1:ℝ)/(Real.cosh x)^2‖ ≤ 1 by
      rw [Real.norm_eq_abs,abs_of_nonneg hb.1]; exact hb.2)

private theorem tanh_monotone : Monotone Real.tanh := by
  apply monotone_of_deriv_nonneg
  · intro x; exact (tanh_derivative x).differentiableAt
  · intro x
    rw [(tanh_derivative x).deriv]
    exact (tanh_derivative_bounds x).1

private theorem tanh_incremental_sector (x y : ℝ) :
    0 ≤ (Real.tanh x-Real.tanh y)*((x-y)-(Real.tanh x-Real.tanh y)) := by
  have hl := tanh_lipschitz.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hl
  rcases le_total y x with hxy | hxy
  · have hm := tanh_monotone hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hm),abs_of_nonneg (sub_nonneg.mpr hxy)] at hl
    exact mul_nonneg (sub_nonneg.mpr hm) (by linarith)
  · have hm := tanh_monotone hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hm),abs_of_nonpos (sub_nonpos.mpr hxy)] at hl
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hm) (by linarith)

private theorem tanh_global_sector (x : ℝ) :
    0 ≤ Real.tanh x*(x-Real.tanh x) := by
  simpa using tanh_incremental_sector x 0

private theorem tanh_concave_nonnegative : ConcaveOn ℝ (Ici 0) Real.tanh := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
  · exact tanh_lipschitz.continuous.continuousOn
  · intro x _; exact (tanh_derivative x).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hx0 : 0 ≤ x := interior_subset hx
    have hy0 : 0 ≤ y := interior_subset hy
    have hc : Real.cosh x ≤ Real.cosh y := by
      apply Real.cosh_le_cosh.mpr
      rwa [abs_of_nonneg hx0,abs_of_nonneg hy0]
    rw [(tanh_derivative x).deriv,(tanh_derivative y).deriv]
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith [Real.cosh_pos x,Real.cosh_pos y]

private theorem tanh_chord_lower (radius x : ℝ) (hr : 0 < radius) (hx : x ∈ Icc 0 radius) :
    (Real.tanh radius/radius)*x ≤ Real.tanh x := by
  have hb : 0 ≤ x/radius := div_nonneg hx.1 (le_of_lt hr)
  have ha : 0 ≤ 1-x/radius := by
    have h := (div_le_one hr).mpr hx.2
    linarith
  have hc := tanh_concave_nonnegative.2
    (show (0:ℝ) ∈ Ici 0 by simp) (show radius ∈ Ici 0 from le_of_lt hr)
    ha hb (show (1-x/radius)+(x/radius)=1 by ring)
  simp only [smul_eq_mul,Real.tanh_zero,mul_zero,zero_add] at hc
  rw [show x/radius*radius=x by field_simp] at hc
  convert hc using 1 <;> ring

private theorem tanh_local_origin_sector (radius x : ℝ) (hr : 0 < radius)
    (hx : |x| ≤ radius) :
    0 ≤ (Real.tanh x-(Real.tanh radius/radius)*x)*(x-Real.tanh x) := by
  have hglobal := tanh_global_sector x
  by_cases hp : 0 ≤ x
  · have hlo := tanh_chord_lower radius x hr ⟨hp,(abs_le.mp hx).2⟩
    have hpos := tanh_monotone hp
    simp only [Real.tanh_zero] at hpos
    have hupper := tanh_lipschitz.dist_le_mul x 0
    simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul,
      abs_of_nonneg hpos,abs_of_nonneg hp] at hupper
    exact mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hupper)
  · have hlo := tanh_chord_lower radius (-x) hr
      ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    rw [Real.tanh_neg] at hlo
    have hneg := tanh_monotone (le_of_not_ge hp)
    simp only [Real.tanh_zero] at hneg
    have hupper := tanh_lipschitz.dist_le_mul x 0
    simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul,
      abs_of_nonpos hneg,abs_of_nonpos (le_of_not_ge hp)] at hupper
    exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith) (by linarith)


private def realQuadratic {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

private def planeMatrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a,b;b,c]

private theorem plane_actual_form (a b c : ℝ) (x : Fin 2 → ℝ) :
    realQuadratic (planeMatrix a b c) x=a*(x 0)^2+2*b*x 0*x 1+c*(x 1)^2 := by
  simp [realQuadratic,planeMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

private theorem plane_completed_square (a b c : ℝ) (ha : a≠0) (x : Fin 2 → ℝ) :
    realQuadratic (planeMatrix a b c) x=
      a*(x 0+(b/a)*x 1)^2+(c-b^2/a)*(x 1)^2 := by
  rw [plane_actual_form]
  field_simp [ha]
  ring

private theorem plane_actual_determinant (a b c : ℝ) : (planeMatrix a b c).det=a*c-b^2 := by
  simp [planeMatrix,Matrix.det_fin_two]
  ring

private theorem plane_pd_criterion (a b c : ℝ) :
    (planeMatrix a b c).PosDef ↔ 0<a ∧ 0<a*c-b^2 := by
  constructor
  · intro h
    have he0 : (![1,0] : Fin 2 → ℝ)≠0 := by
      intro hh
      have hz := congrFun hh 0
      norm_num at hz
    have ha : 0<a := by
      have hp : 0<realQuadratic (planeMatrix a b c) (![1,0] : Fin 2 → ℝ) := by
        simpa only [realQuadratic,Pi.star_apply,star_trivial] using h.dotProduct_mulVec_pos he0
      simpa [plane_actual_form] using hp
    have hex : (![-b/a,1] : Fin 2 → ℝ)≠0 := by
      intro hh
      have hz := congrFun hh 1
      norm_num at hz
    have hp : 0<realQuadratic (planeMatrix a b c) (![-b/a,1] : Fin 2 → ℝ) := by
      simpa only [realQuadratic,Pi.star_apply,star_trivial] using h.dotProduct_mulVec_pos hex
    have hvalue : realQuadratic (planeMatrix a b c) (![-b/a,1] : Fin 2 → ℝ)=c-b^2/a := by
      rw [plane_actual_form]
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one,one_pow,mul_one]
      field_simp [ha.ne']
      ring
    rw [hvalue] at hp
    have hm := mul_pos ha hp
    have hid : a*(c-b^2/a)=a*c-b^2 := by field_simp [ha.ne']
    exact ⟨ha,hid ▸ hm⟩
  · rintro ⟨ha,hd⟩
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · change (planeMatrix a b c).conjTranspose=planeMatrix a b c
      ext i j
      fin_cases i <;> fin_cases j <;> simp [planeMatrix,Matrix.conjTranspose_apply]
    · intro x hx
      have hc : 0<c-b^2/a := by
        have heq : c-b^2/a=(a*c-b^2)/a := by field_simp [ha.ne']
        rw [heq]
        exact div_pos hd ha
      have hp : 0<realQuadratic (planeMatrix a b c) x := by
        by_cases hx1 : x 1=0
        · have hx0 : x 0≠0 := by
            intro hz
            apply hx
            ext i
            fin_cases i <;> simp [hz,hx1]
          rw [plane_actual_form,hx1]
          simp
          exact mul_pos ha (sq_pos_of_ne_zero hx0)
        · rw [plane_completed_square _ _ _ ha.ne']
          exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (sq_nonneg _))
            (mul_pos hc (sq_pos_of_ne_zero hx1))
      simpa only [realQuadratic,Pi.star_apply,star_trivial] using hp


def originLower : ℝ := Real.tanh 3/3

def walkthroughMatrix (a alpha p lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p*(a^2-1)-8*alpha*lam, -(3*a/5)*p+2*(1+alpha)*lam;
     -(3*a/5)*p+2*(1+alpha)*lam, (9/25)*p-2*lam]

def physicalStep (x : ℝ) : ℝ := (13/10)*x-(3/5)*Real.tanh (2*x)
def physicalOrbit (initial : ℝ) (n : ℕ) : ℝ := (physicalStep^[n]) initial

theorem actual_source_scalar_plant_and_controller_composition (a x : ℝ) :
    a*x+(-3/5)*Real.tanh (2*x)=a*x-(3/5)*Real.tanh (2*x) := by ring

theorem actual_source_LMI_is_the_energy_difference_plus_the_origin_sector_QC
    (a alpha p lam x w : ℝ) :
    (![x,w] : Fin 2 → ℝ) ⬝ᵥ (walkthroughMatrix a alpha p lam *ᵥ ![x,w]) =
      p*(a*x-(3/5)*w)^2-p*x^2+2*lam*(w-alpha*(2*x))*(2*x-w) := by
  simp [walkthroughMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem actual_global_walkthrough_determinant (p lam : ℝ) :
    (walkthroughMatrix (4/5) 0 p lam).det =
      -4*lam^2+(66/25)*p*lam-(9/25)*p^2 := by
  simp [walkthroughMatrix,Matrix.det_fin_two]
  ring

theorem actual_global_walkthrough_optimizer_matrix_and_determinant :
    ((1-(4/5:ℝ)^2-(4/5)*(-6/5))/4)=33/100 ∧
      walkthroughMatrix (4/5) 0 1 (33/100)=!![-9/25,9/50;9/50,-3/10] ∧
      (walkthroughMatrix (4/5) 0 1 (33/100)).det=189/2500 := by
  refine ⟨by norm_num,?_,?_⟩
  · ext i j;fin_cases i <;> fin_cases j <;> norm_num [walkthroughMatrix]
  · norm_num [walkthroughMatrix,Matrix.det_fin_two]

theorem actual_global_walkthrough_optimizer_matrix_is_negative_definite :
    (-walkthroughMatrix (4/5) 0 1 (33/100)).PosDef := by
  have he : -walkthroughMatrix (4/5) 0 1 (33/100)=
      planeMatrix (9/25) (-9/50) (3/10) := by
    ext i j;fin_cases i <;> fin_cases j <;> norm_num [walkthroughMatrix,planeMatrix]
  rw [he,plane_pd_criterion]
  norm_num

theorem actual_unstable_global_walkthrough_has_no_negative_definite_certificate
    (p lam : ℝ) (hp : 0<p) :
    ¬(-walkthroughMatrix (13/10) 0 p lam).PosDef := by
  intro h
  have hn : (![1,0] : Fin 2 → ℝ)≠0 := by
    intro hz;have he:=congrFun hz 0;norm_num at he
  have he := h.dotProduct_mulVec_pos hn
  simp [walkthroughMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at he
  nlinarith

theorem actual_local_walkthrough_determinant (alpha p lam : ℝ) :
    (walkthroughMatrix (13/10) alpha p lam).det =
      -(9/25)*p^2+(87/50+(6/25)*alpha)*p*lam-
        4*(1-alpha)^2*lam^2 := by
  simp [walkthroughMatrix,Matrix.det_fin_two]
  ring

private theorem copied_tanh_exponential_square_ratio (x : ℝ) :
    Real.tanh x=((Real.exp x)^2-1)/((Real.exp x)^2+1) := by
  rw [Real.tanh_eq,Real.exp_neg]
  have hn := Real.exp_ne_zero x
  have hp : (Real.exp x)^2+1 ≠ 0 := by positivity
  field_simp <;> ring

theorem actual_exp_one_bounds_give_the_required_tanh_three_sector_enclosure :
    (3/10:ℝ)<originLower ∧ originLower<(33169/100000:ℝ) ∧
      originLower<(1/3:ℝ) := by
  have h0 : 0≤Real.exp 1 := (Real.exp_pos 1).le
  have hlo : (2:ℝ)<Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hhi : Real.exp 1<(5437/2000:ℝ) := by linarith [Real.exp_one_lt_d9]
  have hpL : (2:ℝ)^6<(Real.exp 1)^6 :=
    pow_lt_pow_left₀ hlo (by norm_num) (by decide : (6:ℕ)≠0)
  have hpU : (Real.exp 1)^6<(5437/2000:ℝ)^6 :=
    pow_lt_pow_left₀ hhi h0 (by decide : (6:ℕ)≠0)
  have hnum : (5437/2000:ℝ)^6<404 := by norm_num
  have he3 : Real.exp (3:ℝ)=(Real.exp 1)^3 := by
    rw [show (3:ℝ)=1+1+1 by norm_num,Real.exp_add,Real.exp_add]
    ring
  have he6 : (Real.exp 3)^2=(Real.exp 1)^6 := by rw [he3];ring
  have hElo : (64:ℝ)<(Real.exp 3)^2 := by rw [he6];norm_num at hpL ⊢;exact hpL
  have hEhi : (Real.exp 3)^2<(404:ℝ) := by rw [he6];exact hpU.trans hnum
  have hden : 0<(Real.exp 3)^2+1 := by positivity
  have htl : (9/10:ℝ)<Real.tanh 3 := by
    rw [copied_tanh_exponential_square_ratio]
    apply (lt_div_iff₀ hden).mpr
    nlinarith
  have htu : Real.tanh 3<(99507/100000:ℝ) := by
    rw [copied_tanh_exponential_square_ratio]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  dsimp [originLower]
  refine ⟨by linarith,by linarith,by linarith [Real.tanh_lt_one 3]⟩

theorem actual_half_multiplier_has_the_exact_negative_pivot_and_positive_determinant
    (alpha : ℝ) (ha : alpha∈Icc (3/10:ℝ) (1/3)) :
    walkthroughMatrix (13/10) alpha 1 (1/2) 0 0≤-(51/100:ℝ) ∧
      (walkthroughMatrix (13/10) alpha 1 (1/2)).det≥7/125 := by
  have hgap : (-alpha^2+(53/25)*alpha-49/100)-(7/125)=
      (alpha-3/10)*(91/50-alpha) := by ring
  have hn : 0≤(alpha-3/10)*(91/50-alpha) :=
    mul_nonneg (by linarith [ha.1]) (by linarith [ha.2])
  constructor
  · norm_num [walkthroughMatrix];linarith [ha.1]
  · rw [actual_local_walkthrough_determinant]
    nlinarith

theorem actual_exact_half_multiplier_is_strictly_feasible :
    (-walkthroughMatrix (13/10) originLower 1 (1/2)).PosDef := by
  have hb:=actual_exp_one_bounds_give_the_required_tanh_three_sector_enclosure
  have ha : originLower∈Icc (3/10:ℝ) (1/3) := ⟨hb.1.le,hb.2.2.le⟩
  have hdet := (actual_half_multiplier_has_the_exact_negative_pivot_and_positive_determinant
    originLower ha).2
  have he : -walkthroughMatrix (13/10) originLower 1 (1/2)=
      planeMatrix (4*originLower-69/100) (-originLower-11/50) (16/25) := by
    ext i j;fin_cases i <;> fin_cases j <;> norm_num [walkthroughMatrix,planeMatrix] <;> ring
  rw [he,plane_pd_criterion]
  constructor
  · linarith [ha.1]
  · have hid : (4*originLower-69/100)*(16/25)-(-originLower-11/50)^2 =
        (walkthroughMatrix (13/10) originLower 1 (1/2)).det := by
      rw [actual_local_walkthrough_determinant];ring
    rw [hid]
    linarith

theorem actual_positive_rescaling_retains_the_source_LMI_identity
    (a alpha p lam scale : ℝ) :
    walkthroughMatrix a alpha (scale*p) (scale*lam)=
      scale • walkthroughMatrix a alpha p lam := by
  ext i j;fin_cases i <;> fin_cases j <;>
    simp [walkthroughMatrix] <;> ring

theorem actual_rescaled_box_three_multiplier_is_strictly_feasible :
    (-walkthroughMatrix (13/10) originLower (4/9) (2/9)).PosDef := by
  have hb:=actual_exp_one_bounds_give_the_required_tanh_three_sector_enclosure
  have ha : originLower∈Icc (3/10:ℝ) (1/3) := ⟨hb.1.le,hb.2.2.le⟩
  have hd := (actual_half_multiplier_has_the_exact_negative_pivot_and_positive_determinant
    originLower ha).2
  have hscale : (walkthroughMatrix (13/10) originLower (4/9) (2/9)).det=
      (16/81)*(walkthroughMatrix (13/10) originLower 1 (1/2)).det := by
    rw [actual_local_walkthrough_determinant,actual_local_walkthrough_determinant]
    ring
  have he : -walkthroughMatrix (13/10) originLower (4/9) (2/9)=
      planeMatrix ((4/9)*(4*originLower-69/100))
        ((4/9)*(-originLower-11/50)) ((4/9)*(16/25)) := by
    ext i j;fin_cases i <;> fin_cases j <;> norm_num [walkthroughMatrix,planeMatrix] <;> ring
  rw [he,plane_pd_criterion]
  constructor
  · nlinarith [ha.1]
  · have hid : ((4/9)*(4*originLower-69/100))*((4/9)*(16/25))-
        ((4/9)*(-originLower-11/50))^2 =
        (walkthroughMatrix (13/10) originLower (4/9) (2/9)).det := by
      rw [actual_local_walkthrough_determinant];ring
    rw [hid,hscale]
    nlinarith

def containmentMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![9,2;2,4/9]

theorem actual_box_three_containment_matrix_is_semidefinite_with_zero_determinant :
    containmentMatrix.PosSemidef ∧ containmentMatrix.det=0 := by
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j;fin_cases i <;> fin_cases j <;> norm_num [containmentMatrix,Matrix.conjTranspose_apply]
    · intro x
      simp [containmentMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,star_trivial]
      nlinarith [sq_nonneg (3*x 0+(2/3)*x 1)]
  · norm_num [containmentMatrix,Matrix.det_fin_two]

theorem actual_rescaled_sublevel_is_exactly_the_box_three_state_interval (x : ℝ) :
    ((4/9:ℝ)*x^2≤1 ↔ |x|≤3/2) ∧
      (|2*x|≤3 ↔ |x|≤3/2) := by
  constructor
  · constructor
    · intro h;rw [abs_le];constructor <;> nlinarith [sq_nonneg (x-3/2),sq_nonneg (x+3/2)]
    · intro h;have hh:=abs_le.mp h;nlinarith [hh.1,hh.2]
  · rw [abs_mul];norm_num;constructor <;> intro h <;> linarith

private def localDet (alpha lam : ℝ) : ℝ :=
  -(9/25)+(87/50+(6/25)*alpha)*lam-4*(1-alpha)^2*lam^2

theorem actual_printed_upper_interval_contains_an_infeasible_multiplier :
    (7499/10000:ℝ)∈Ioo (269/1000) (3/4) ∧
      (walkthroughMatrix (13/10) originLower 1 (7499/10000)).det<0 ∧
      ¬(-walkthroughMatrix (13/10) originLower 1 (7499/10000)).PosDef := by
  have hb:=actual_exp_one_bounds_give_the_required_tanh_three_sector_enclosure
  have hmono : localDet originLower (7499/10000)≤
      localDet (33169/100000) (7499/10000) := by
    have hid : localDet (33169/100000) (7499/10000)-localDet originLower (7499/10000)=
      ((33169/100000)-originLower)*
        (4*(7499/10000)^2*(2-(33169/100000)-originLower)+(6/25)*(7499/10000)) := by
      unfold localDet;ring
    have hp : 0≤((33169/100000)-originLower)*
        (4*(7499/10000)^2*(2-(33169/100000)-originLower)+(6/25)*(7499/10000)) := by
      have hfirst : 0≤(33169/100000:ℝ)-originLower := by linarith [hb.2.1]
      have hsecond : 0≤(2:ℝ)-(33169/100000)-originLower := by linarith [hb.2.2]
      positivity
    linarith
  have hval : localDet (33169/100000) (7499/10000)=
      (-36467924217561/250000000000000000:ℝ) := by norm_num [localDet]
  have hdet : (walkthroughMatrix (13/10) originLower 1 (7499/10000)).det<0 := by
    rw [actual_local_walkthrough_determinant]
    simp only [one_pow,mul_one,one_mul]
    change localDet originLower (7499/10000)<0
    rw [hval] at hmono
    linarith
  refine ⟨by norm_num,hdet,?_⟩
  intro h
  have he : -walkthroughMatrix (13/10) originLower 1 (7499/10000)=
      planeMatrix (8*originLower*(7499/10000)-69/100)
        (39/50-2*(1+originLower)*(7499/10000)) (2*(7499/10000)-9/25) := by
    ext i j;fin_cases i <;> fin_cases j <;> norm_num [walkthroughMatrix,planeMatrix] <;> ring
  rw [he,plane_pd_criterion] at h
  have hd:=h.2
  rw [actual_local_walkthrough_determinant] at hdet
  nlinarith

theorem actual_origin_sector_on_the_entire_box_three (v : ℝ) (hv : |v|≤3) :
    0≤2*(Real.tanh v-originLower*v)*(v-Real.tanh v) := by
  have h:=tanh_local_origin_sector 3 v (by norm_num) hv
  dsimp [originLower]
  nlinarith

private theorem actual_nonnegative_state_origin_bounds (x : ℝ)
    (hx0 : 0≤x) (hx : x≤3/2) :
    0≤physicalStep x ∧ physicalStep x≤(47/50)*x := by
  have hv : (2*x:ℝ)∈Icc 0 3 := ⟨by linarith,by linarith⟩
  have hlow:=tanh_chord_lower 3 (2*x) (by norm_num) hv
  have hpositive:=tanh_monotone (show (0:ℝ)≤2*x by linarith)
  simp only [Real.tanh_zero] at hpositive
  have hu:=tanh_lipschitz.dist_le_mul (2*x) 0
  simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul,
    abs_of_nonneg hpositive,abs_of_nonneg (show (0:ℝ)≤2*x by linarith)] at hu
  have ha: (3/10:ℝ)≤originLower :=
    actual_exp_one_bounds_give_the_required_tanh_three_sector_enclosure.1.le
  change originLower*(2*x)≤Real.tanh (2*x) at hlow
  have hp:=mul_nonneg (sub_nonneg.mpr ha) hx0
  unfold physicalStep
  constructor <;> nlinarith

theorem actual_local_loop_has_origin_norm_decay_without_a_pairwise_contraction_claim
    (x : ℝ) (hx : |x|≤3/2) : |physicalStep x|≤(47/50)*|x| := by
  by_cases hx0 : 0≤x
  · have h:=actual_nonnegative_state_origin_bounds x hx0 (abs_le.mp hx).2
    rw [abs_of_nonneg h.1,abs_of_nonneg hx0]
    exact h.2
  · have h:=actual_nonnegative_state_origin_bounds (-x) (by linarith) (by linarith [(abs_le.mp hx).1])
    have he : physicalStep (-x)= -physicalStep x := by
      unfold physicalStep
      simp only [mul_neg,Real.tanh_neg]
      ring
    rw [he] at h
    rw [abs_of_nonpos (by linarith [h.1]),abs_of_neg (lt_of_not_ge hx0)]
    exact h.2

theorem actual_local_physical_loop_has_all_time_invariance_and_origin_decay
    (initial : ℝ) (hstart : |initial|≤3/2) (n : ℕ) :
    |physicalOrbit initial n|≤(47/50:ℝ)^n*|initial| ∧
      |physicalOrbit initial n|≤3/2 := by
  induction n with
  | zero => simp [physicalOrbit,hstart]
  | succ n ih =>
    have hstep:=actual_local_loop_has_origin_norm_decay_without_a_pairwise_contraction_claim
      (physicalOrbit initial n) ih.2
    have hn : physicalOrbit initial (n+1)=physicalStep (physicalOrbit initial n) := by
      simp [physicalOrbit,Function.iterate_succ_apply']
    rw [hn]
    constructor
    · calc
        |physicalStep (physicalOrbit initial n)|≤(47/50)*|physicalOrbit initial n| := hstep
        _≤(47/50)*((47/50:ℝ)^n*|initial|) :=
          mul_le_mul_of_nonneg_left ih.1 (by norm_num)
        _=(47/50:ℝ)^(n+1)*|initial| := by rw [pow_succ];ring
    · nlinarith [ih.2,abs_nonneg (physicalOrbit initial n)]

theorem actual_every_initial_state_in_the_certified_interval_converges_to_zero
    (initial : ℝ) (hstart : |initial|≤3/2) :
    Tendsto (physicalOrbit initial) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (47/50:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hu : Tendsto (fun n : ℕ => (47/50:ℝ)^n*|initial|) atTop (𝓝 0) := by
    simpa only [zero_mul] using hp.mul_const |initial|
  have hnorm : Tendsto (fun n : ℕ => |physicalOrbit initial n|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) (fun n =>
      (actual_local_physical_loop_has_all_time_invariance_and_origin_decay initial hstart n).1) hu
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hnorm)

theorem actual_rescaled_storage_along_the_true_loop_has_geometric_decay
    (initial : ℝ) (hstart : |initial|≤3/2) (n : ℕ) :
    (4/9:ℝ)*(physicalOrbit initial n)^2≤
      (47/50:ℝ)^(2*n)*((4/9)*initial^2) := by
  have h:=(actual_local_physical_loop_has_all_time_invariance_and_origin_decay initial hstart n).1
  have hsq : (physicalOrbit initial n)^2≤((47/50:ℝ)^n)^2*initial^2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg (physicalOrbit initial n)) h 2
    simpa only [mul_pow,sq_abs] using hs
  have hp:=mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ)≤4/9)
  calc
    (4/9:ℝ)*(physicalOrbit initial n)^2≤
        (4/9)*(((47/50:ℝ)^n)^2*initial^2) := hp
    _=(47/50:ℝ)^(2*n)*((4/9)*initial^2) := by
      rw [←pow_mul]
      rw [show n*2=2*n by omega]
      ring

end SafeLearning.CompleteModulesNNWalkthroughLocal31

namespace SafeLearning.CompleteModulesNNWalkthroughLocal31

def globalSmallEigenvalue : ℝ := (-33-3*Real.sqrt 37)/100
def globalLargeEigenvalue : ℝ := (-33+3*Real.sqrt 37)/100
def globalLowerMultiplier : ℝ := (33-3*Real.sqrt 21)/100
def globalUpperMultiplier : ℝ := (33+3*Real.sqrt 21)/100

theorem actual_global_walkthrough_has_the_complete_exact_official_spectrum (mu : ℝ) :
    mu∈spectrum ℝ (walkthroughMatrix (4/5) 0 1 (33/100)) ↔
      mu=globalSmallEigenvalue ∨ mu=globalLargeEigenvalue := by
  have hc : (walkthroughMatrix (4/5) 0 1 (33/100)).charpoly.eval mu=
      mu^2+(33/50)*mu+189/2500 := by
    rw [Matrix.charpoly_fin_two]
    simp [walkthroughMatrix,Matrix.trace,Matrix.det_fin_two,Fin.sum_univ_two]
    ring
  have hs : (Real.sqrt (37:ℝ))^2=37 := Real.sq_sqrt (by norm_num)
  have he : (mu-globalSmallEigenvalue)*(mu-globalLargeEigenvalue)=
      mu^2+(33/50)*mu+189/2500 := by
    unfold globalSmallEigenvalue globalLargeEigenvalue
    nlinarith [hs]
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,hc,←he]
  simp [mul_eq_zero,sub_eq_zero]

theorem actual_global_walkthrough_determinant_factors_at_the_exact_multiplier_endpoints
    (p lam : ℝ) :
    (walkthroughMatrix (4/5) 0 p lam).det=
      4*(lam-p*globalLowerMultiplier)*(p*globalUpperMultiplier-lam) := by
  have hs : (Real.sqrt (21:ℝ))^2=21 := Real.sq_sqrt (by norm_num)
  have he : 4*(lam-p*globalLowerMultiplier)*(p*globalUpperMultiplier-lam)-
      (-4*lam^2+(66/25)*p*lam-(9/25)*p^2)=
      (9/2500)*p^2*((Real.sqrt 21)^2-21) := by
    unfold globalLowerMultiplier globalUpperMultiplier
    ring
  rw [hs] at he
  rw [actual_global_walkthrough_determinant]
  nlinarith

theorem actual_all_positive_storage_walkthrough_certificates_have_the_exact_multiplier_interval
    (p lam : ℝ) (hp : 0<p) :
    (-walkthroughMatrix (4/5) 0 p lam).PosDef ↔
      p*globalLowerMultiplier<lam ∧ lam<p*globalUpperMultiplier := by
  have hs : 0<Real.sqrt (21:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hgap : 0<p*(3*Real.sqrt 21/50) := mul_pos hp (by positivity)
  have horder : p*globalLowerMultiplier<p*globalUpperMultiplier := by
    unfold globalLowerMultiplier globalUpperMultiplier
    nlinarith
  have he : -walkthroughMatrix (4/5) 0 p lam=
      planeMatrix ((9/25)*p) ((12/25)*p-2*lam) (2*lam-(9/25)*p) := by
    ext i j;fin_cases i <;> fin_cases j <;> norm_num [walkthroughMatrix,planeMatrix] <;> ring
  have hdet : ((9/25)*p)*(2*lam-(9/25)*p)-((12/25)*p-2*lam)^2=
      4*(lam-p*globalLowerMultiplier)*(p*globalUpperMultiplier-lam) := by
    have h:=actual_global_walkthrough_determinant_factors_at_the_exact_multiplier_endpoints p lam
    rw [actual_global_walkthrough_determinant] at h
    nlinarith
  rw [he,plane_pd_criterion]
  constructor
  · rintro ⟨_,hd⟩
    rw [hdet] at hd
    have hprod : 0<(lam-p*globalLowerMultiplier)*(p*globalUpperMultiplier-lam) := by nlinarith
    constructor
    · by_contra h
      have hfirst : lam-p*globalLowerMultiplier≤0 := by linarith
      have hsecond : 0≤p*globalUpperMultiplier-lam := by linarith
      have hn:=mul_nonpos_of_nonpos_of_nonneg hfirst hsecond
      linarith
    · by_contra h
      have hfirst : 0≤lam-p*globalLowerMultiplier := by linarith
      have hsecond : p*globalUpperMultiplier-lam≤0 := by linarith
      have hn:=mul_nonpos_of_nonneg_of_nonpos hfirst hsecond
      linarith
  · rintro ⟨hl,hu⟩
    constructor
    · nlinarith
    · rw [hdet]
      have hn:=mul_pos (sub_pos.mpr hl) (sub_pos.mpr hu)
      nlinarith

theorem actual_all_unit_storage_admissible_multipliers_are_exactly_between_the_roots
    (lam : ℝ) :
    (-walkthroughMatrix (4/5) 0 1 lam).PosDef ↔
      lam∈Ioo globalLowerMultiplier globalUpperMultiplier := by
  simpa only [one_mul,Set.mem_Ioo] using
    actual_all_positive_storage_walkthrough_certificates_have_the_exact_multiplier_interval
      1 lam (by norm_num)

theorem actual_displayed_global_inner_interval_is_sound_but_does_not_list_all_multipliers :
    (∀ lam∈Ioo (193/1000:ℝ) (467/1000),
      (-walkthroughMatrix (4/5) 0 1 lam).PosDef) ∧
      (-walkthroughMatrix (4/5) 0 1 (963/5000)).PosDef ∧
      (963/5000:ℝ)∉Ioo (193/1000) (467/1000) := by
  have hs : (Real.sqrt (21:ℝ))^2=21 := Real.sq_sqrt (by norm_num)
  have hn:=Real.sqrt_nonneg (21:ℝ)
  have hlo : (137/30:ℝ)<Real.sqrt 21 := by nlinarith
  have hupper : globalLowerMultiplier<(193/1000:ℝ) ∧
      (467/1000:ℝ)<globalUpperMultiplier := by
    unfold globalLowerMultiplier globalUpperMultiplier
    constructor <;> linarith
  refine ⟨?_,?_,by norm_num⟩
  · intro lam hl
    apply (actual_all_unit_storage_admissible_multipliers_are_exactly_between_the_roots lam).mpr
    exact ⟨hupper.1.trans hl.1,hl.2.trans hupper.2⟩
  · have he : -walkthroughMatrix (4/5) 0 1 (963/5000)=
        planeMatrix (9/25) (237/2500) (63/2500) := by
      ext i j;fin_cases i <;> fin_cases j <;> norm_num [walkthroughMatrix,planeMatrix]
    rw [he,plane_pd_criterion]
    norm_num

theorem actual_two_printed_rounded_eigenvalues_are_not_exact_spectral_values :
    (-37/250:ℝ)∉spectrum ℝ (walkthroughMatrix (4/5) 0 1 (33/100)) ∧
      (-64/125:ℝ)∉spectrum ℝ (walkthroughMatrix (4/5) 0 1 (33/100)) := by
  have hc (mu : ℝ) : (walkthroughMatrix (4/5) 0 1 (33/100)).charpoly.eval mu=
      mu^2+(33/50)*mu+189/2500 := by
    rw [Matrix.charpoly_fin_two]
    simp [walkthroughMatrix,Matrix.trace,Matrix.det_fin_two,Fin.sum_univ_two]
    ring
  constructor <;> intro h
  · rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,hc] at h
    norm_num at h
  · rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,hc] at h
    norm_num at h

end SafeLearning.CompleteModulesNNWalkthroughLocal31

/- The following separate scalar basin-family append is wholly uncompiled.
The preceding passed26 source bytes are retained as an exact immutable prefix.
No source qualifier, whole exercise approval, or live owner change is claimed. -/
namespace SafeLearning.CompleteModulesNNWalkthroughLocal31

def basinSecant (y : ℝ) : ℝ := Real.tanh y/y

def basinStep (y : ℝ) : ℝ := (13/10)*y-(6/5)*Real.tanh y

def basinOrbit (initial : ℝ) (n : ℕ) : ℝ := (basinStep^[n]) initial

private theorem basin_tanh_is_strictly_concave_nonnegative :
    StrictConcaveOn ℝ (Ici 0) Real.tanh := by
  have hderiv : StrictAntiOn (deriv Real.tanh) (interior (Ici (0:ℝ))) := by
    intro x hx y hy hxy
    have hx0 : 0≤x := interior_subset hx
    have hy0 : 0≤y := interior_subset hy
    have hc := Real.cosh_strictMonoOn hx0 hy0 hxy
    rw [(tanh_derivative y).deriv,(tanh_derivative x).deriv]
    apply (div_lt_div_iff₀ (sq_pos_of_pos (Real.cosh_pos y))
      (sq_pos_of_pos (Real.cosh_pos x))).mpr
    nlinarith [Real.cosh_pos x,Real.cosh_pos y]
  exact hderiv.strictConcaveOn_of_deriv (convex_Ici 0)
    tanh_lipschitz.continuous.continuousOn

theorem actual_positive_tanh_origin_secants_strictly_decrease :
    StrictAntiOn basinSecant (Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0<x := hx
  have hy0 : 0<y := hy
  have h:=basin_tanh_is_strictly_concave_nonnegative.secant_strict_mono
    (show (0:ℝ)∈Ici 0 by simp) (show x∈Ici 0 from hx0.le)
    (show y∈Ici 0 from hy0.le) hx0.ne' hy0.ne' hxy
  simpa only [basinSecant,Real.tanh_zero,sub_zero] using h

private theorem basin_tanh_double_exponential_ratio (y : ℝ) :
    Real.tanh y=(Real.exp (2*y)-1)/(Real.exp (2*y)+1) := by
  have he : (Real.exp y)^2=Real.exp (2*y) := by
    simpa using (Real.exp_nat_mul y 2).symm
  rw [copied_tanh_exponential_square_ratio]
  simp only [he]

theorem actual_critical_secant_has_rigorous_opposite_signs_at_the_two_rational_endpoints :
    (1/4:ℝ)<basinSecant (39973/10000) ∧
      basinSecant (19987/5000)<(1/4:ℝ) := by
  have he8 : Real.exp (8:ℝ)=(Real.exp 1)^8 := by
    simpa using Real.exp_nat_mul (1:ℝ) 8
  have he1L : (1359/500:ℝ)<Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he1U : Real.exp 1<(2719/1000:ℝ) := by linarith [Real.exp_one_lt_d9]
  have h8L : (1359/500:ℝ)^8<Real.exp 8 := by
    rw [he8]
    exact pow_lt_pow_left₀ he1L (by norm_num) (by decide : (8:ℕ)≠0)
  have h8U : Real.exp 8<(2719/1000:ℝ)^8 := by
    rw [he8]
    exact pow_lt_pow_left₀ he1U (Real.exp_pos 1).le (by decide : (8:ℕ)≠0)
  have hn : (4973/5000:ℝ)≤Real.exp (-27/5000) := by
    linarith [Real.add_one_le_exp (-27/5000:ℝ)]
  have hEL : (1359/500:ℝ)^8*(4973/5000)<Real.exp (2*(39973/10000:ℝ)) := by
    calc
      (1359/500:ℝ)^8*(4973/5000)<Real.exp 8*(4973/5000) :=
        mul_lt_mul_of_pos_right h8L (by norm_num)
      _≤Real.exp 8*Real.exp (-27/5000) :=
        mul_le_mul_of_nonneg_left hn (Real.exp_pos 8).le
      _=Real.exp (2*(39973/10000:ℝ)) := by
        rw [←Real.exp_add]
        congr 1
        norm_num
  have hEU : Real.exp (2*(19987/5000:ℝ))<(2719/1000:ℝ)^8 :=
    (Real.exp_lt_exp.mpr (by norm_num : 2*(19987/5000:ℝ)<8)).trans h8U
  have hcrossL : 0<(4-(39973/10000:ℝ))*Real.exp (2*(39973/10000:ℝ))-
      (4+(39973/10000:ℝ)) := by
    have hnum : 0<(4-(39973/10000:ℝ))*((1359/500:ℝ)^8*(4973/5000))-
      (4+(39973/10000:ℝ)) := by norm_num
    have hm:=mul_lt_mul_of_pos_left hEL (by norm_num : 0<(4:ℝ)-39973/10000)
    nlinarith
  have hcrossU : (4-(19987/5000:ℝ))*Real.exp (2*(19987/5000:ℝ))-
      (4+(19987/5000:ℝ))<0 := by
    have hnum : (4-(19987/5000:ℝ))*(2719/1000:ℝ)^8-
      (4+(19987/5000:ℝ))<0 := by norm_num
    have hm:=mul_lt_mul_of_pos_left hEU (by norm_num : 0<(4:ℝ)-19987/5000)
    nlinarith
  have hL : (39973/10000:ℝ)/4<Real.tanh (39973/10000) := by
    rw [basin_tanh_double_exponential_ratio]
    apply (lt_div_iff₀ (show 0<Real.exp (2*(39973/10000:ℝ))+1 by positivity)).mpr
    nlinarith
  have hU : Real.tanh (19987/5000)<(19987/5000:ℝ)/4 := by
    rw [basin_tanh_double_exponential_ratio]
    apply (div_lt_iff₀ (show 0<Real.exp (2*(19987/5000:ℝ))+1 by positivity)).mpr
    nlinarith
  constructor
  · unfold basinSecant
    apply (lt_div_iff₀ (by norm_num : 0<(39973/10000:ℝ))).mpr
    linarith
  · unfold basinSecant
    apply (div_lt_iff₀ (by norm_num : 0<(19987/5000:ℝ))).mpr
    linarith

theorem actual_unique_positive_critical_radius_exists_and_has_the_exact_rational_bracket :
    ∃ r : ℝ, 0<r ∧ basinSecant r=(1/4:ℝ) ∧
      r∈Ioo (39973/10000) (19987/5000) ∧
      ∀ u : ℝ, 0<u → basinSecant u=(1/4:ℝ) → u=r := by
  have hs:=actual_critical_secant_has_rigorous_opposite_signs_at_the_two_rational_endpoints
  have hL : (39973/10000:ℝ)/4<Real.tanh (39973/10000) := by
    have h:=(lt_div_iff₀ (by norm_num : 0<(39973/10000:ℝ))).mp hs.1
    linarith
  have hU : Real.tanh (19987/5000)<(19987/5000:ℝ)/4 := by
    have h:=(div_lt_iff₀ (by norm_num : 0<(19987/5000:ℝ))).mp hs.2
    linarith
  have hc : Continuous (fun y : ℝ => Real.tanh y-y/4) :=
    tanh_lipschitz.continuous.sub (continuous_id.div_const 4)
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc' (by norm_num : (39973/10000:ℝ)≤19987/5000)
    hc.continuousOn (show (0:ℝ)∈Icc (Real.tanh (19987/5000)-(19987/5000)/4)
      (Real.tanh (39973/10000)-(39973/10000)/4) from ⟨by linarith,by linarith⟩)
  have hr0 : 0<r := by linarith [hr.1]
  have hroot : basinSecant r=(1/4:ℝ) := by
    unfold basinSecant
    apply (div_eq_iff hr0.ne').mpr
    linarith
  have hbracket : r∈Ioo (39973/10000:ℝ) (19987/5000) := by
    constructor
    · by_contra h
      have her : r=(39973/10000:ℝ) := by linarith [hr.1]
      rw [her] at he
      linarith
    · by_contra h
      have her : r=(19987/5000:ℝ) := by linarith [hr.2]
      rw [her] at he
      linarith
  refine ⟨r,hr0,hroot,hbracket,?_⟩
  intro u hu huroot
  apply actual_positive_tanh_origin_secants_strictly_decrease.injOn hu hr0
  rw [huroot,hroot]

def basinRadius : ℝ :=
  Classical.choose actual_unique_positive_critical_radius_exists_and_has_the_exact_rational_bracket

private theorem basinRadius_spec :
    0<basinRadius ∧ basinSecant basinRadius=(1/4:ℝ) ∧
      basinRadius∈Ioo (39973/10000) (19987/5000) ∧
      ∀ u : ℝ, 0<u → basinSecant u=(1/4:ℝ) → u=basinRadius :=
  Classical.choose_spec actual_unique_positive_critical_radius_exists_and_has_the_exact_rational_bracket

end SafeLearning.CompleteModulesNNWalkthroughLocal31

/- This cumulative second basin append is also wholly uncompiled. It adds
actual state dynamics, not pairwise contraction or an assumed basin premise. -/
namespace SafeLearning.CompleteModulesNNWalkthroughLocal31

def basinGain (radius : ℝ) : ℝ := (13/10)-(6/5)*basinSecant radius

private theorem basinStep_odd (y : ℝ) : basinStep (-y)= -basinStep y := by
  unfold basinStep
  simp only [mul_neg,Real.tanh_neg]
  ring

private theorem basinOrbit_succ (initial : ℝ) (n : ℕ) :
    basinOrbit initial (n+1)=basinStep (basinOrbit initial n) := by
  simp [basinOrbit,Function.iterate_succ_apply']

private theorem physicalOrbit_succ (initial : ℝ) (n : ℕ) :
    physicalOrbit initial (n+1)=physicalStep (physicalOrbit initial n) := by
  simp [physicalOrbit,Function.iterate_succ_apply']

private theorem basinOrbit_odd (initial : ℝ) (n : ℕ) :
    basinOrbit (-initial) n= -basinOrbit initial n := by
  induction n with
  | zero => simp [basinOrbit]
  | succ n ih => simp only [basinOrbit_succ,ih,basinStep_odd]

private theorem basin_nonnegative_state_bounds (radius y : ℝ) (hr : 0<radius)
    (hy0 : 0≤y) (hy : y≤radius) :
    0≤basinStep y ∧ basinStep y≤basinGain radius*y := by
  have hlow:=tanh_chord_lower radius y hr ⟨hy0,hy⟩
  have hpositive:=tanh_monotone hy0
  simp only [Real.tanh_zero] at hpositive
  have hupper:=tanh_lipschitz.dist_le_mul y 0
  simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul,
    abs_of_nonneg hpositive,abs_of_nonneg hy0] at hupper
  unfold basinStep basinGain basinSecant
  constructor <;> nlinarith

theorem actual_every_strictly_interior_box_has_a_true_origin_radial_gain_less_than_one
    (radius : ℝ) (hr : 0<radius) (hinside : radius<basinRadius) :
    (1/10:ℝ)≤basinGain radius ∧ basinGain radius<1 ∧
      ∀ y : ℝ, |y|≤radius → |basinStep y|≤basinGain radius*|y| := by
  have hstrict:=actual_positive_tanh_origin_secants_strictly_decrease hr
    basinRadius_spec.1 hinside
  rw [basinRadius_spec.2.1] at hstrict
  have hpositive:=tanh_monotone hr.le
  simp only [Real.tanh_zero] at hpositive
  have hupper:=tanh_lipschitz.dist_le_mul radius 0
  simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul,
    abs_of_nonneg hpositive,abs_of_pos hr] at hupper
  have hsecant : basinSecant radius≤1 := (div_le_one hr).mpr hupper
  have hq0 : (1/10:ℝ)≤basinGain radius := by unfold basinGain;linarith
  have hq1 : basinGain radius<1 := by unfold basinGain;linarith
  refine ⟨hq0,hq1,?_⟩
  intro y hy
  by_cases hy0 : 0≤y
  · have h:=basin_nonnegative_state_bounds radius y hr hy0 (abs_le.mp hy).2
    rw [abs_of_nonneg h.1,abs_of_nonneg hy0]
    exact h.2
  · have h:=basin_nonnegative_state_bounds radius (-y) hr (by linarith)
      (by linarith [(abs_le.mp hy).1])
    rw [basinStep_odd] at h
    rw [abs_of_nonpos (by linarith [h.1]),abs_of_neg (lt_of_not_ge hy0)]
    exact h.2

theorem actual_every_interior_initial_y_has_all_time_origin_geometric_convergence
    (initial : ℝ) (hinside : |initial|<basinRadius) :
    ∃ q : ℝ, q∈Ioo 0 1 ∧
      (∀ n : ℕ, |basinOrbit initial n|≤q^n*|initial| ∧
        |basinOrbit initial n|<basinRadius) ∧
      Tendsto (basinOrbit initial) atTop (𝓝 0) := by
  let radius : ℝ := (|initial|+basinRadius)/2
  have hr : 0<radius := by dsimp [radius];linarith [abs_nonneg initial,basinRadius_spec.1]
  have hri : radius<basinRadius := by dsimp [radius];linarith
  have hstart : |initial|≤radius := by dsimp [radius];linarith
  have hrad:=actual_every_strictly_interior_box_has_a_true_origin_radial_gain_less_than_one
    radius hr hri
  let q : ℝ := basinGain radius
  have hq0 : 0<q := by dsimp [q];linarith [hrad.1]
  have hq1 : q<1 := hrad.2.1
  have horbit (n : ℕ) : |basinOrbit initial n|≤q^n*|initial| ∧
      |basinOrbit initial n|≤radius := by
    induction n with
    | zero => exact ⟨by simp [basinOrbit],by simpa [basinOrbit] using hstart⟩
    | succ n ih =>
      have hstep:=hrad.2.2 (basinOrbit initial n) ih.2
      rw [basinOrbit_succ]
      constructor
      · calc
          |basinStep (basinOrbit initial n)|≤q*|basinOrbit initial n| := hstep
          _≤q*(q^n*|initial|) := mul_le_mul_of_nonneg_left ih.1 hq0.le
          _=q^(n+1)*|initial| := by rw [pow_succ];ring
      · have hbound:=mul_le_mul_of_nonneg_left ih.2 hq0.le
        have hscaled : q*radius≤radius := by nlinarith [hr]
        exact hstep.trans (hbound.trans hscaled)
  have hp : Tendsto (fun n : ℕ => q^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
  have hmul : Tendsto (fun n : ℕ => q^n*|initial|) atTop (𝓝 0) := by
    simpa only [zero_mul] using hp.mul_const |initial|
  have habs : Tendsto (fun n : ℕ => |basinOrbit initial n|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) (fun n => (horbit n).1) hmul
  refine ⟨q,⟨hq0,hq1⟩,fun n => ⟨(horbit n).1,(horbit n).2.trans_lt hri⟩,?_⟩
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

private theorem basin_positive_exterior_step (seed y : ℝ) (hseed : basinRadius<seed)
    (hy : seed≤y) :
    1<basinGain seed ∧ basinGain seed*y≤basinStep y ∧ seed≤basinStep y := by
  have hs0 : 0<seed := basinRadius_spec.1.trans hseed
  have hy0 : 0<y := hs0.trans_le hy
  have hstrict:=actual_positive_tanh_origin_secants_strictly_decrease
    basinRadius_spec.1 hs0 hseed
  rw [basinRadius_spec.2.1] at hstrict
  have hq : 1<basinGain seed := by unfold basinGain;linarith
  have hsecant:=actual_positive_tanh_origin_secants_strictly_decrease.antitoneOn hs0 hy0 hy
  have ht : Real.tanh y≤basinSecant seed*y :=
    (div_le_iff₀ hy0).mp hsecant
  have hstep : basinGain seed*y≤basinStep y := by
    unfold basinGain basinStep
    nlinarith
  have hgrowth : y≤basinGain seed*y := by nlinarith
  exact ⟨hq,hstep,hy.trans (hgrowth.trans hstep)⟩

theorem actual_positive_exterior_y_has_geometric_escape_to_positive_infinity
    (initial : ℝ) (houtside : basinRadius< initial) :
    1<basinGain initial ∧
      (∀ n : ℕ, (basinGain initial)^n*initial≤basinOrbit initial n ∧
        initial≤basinOrbit initial n) ∧
      Tendsto (basinOrbit initial) atTop atTop := by
  have h0:=basin_positive_exterior_step initial initial houtside le_rfl
  have hinit0 : 0< initial := basinRadius_spec.1.trans houtside
  have hq0 : 0≤basinGain initial := by linarith [h0.1]
  have horbit (n : ℕ) : (basinGain initial)^n*initial≤basinOrbit initial n ∧
      initial≤basinOrbit initial n := by
    induction n with
    | zero => simp [basinOrbit]
    | succ n ih =>
      have hstep:=basin_positive_exterior_step initial (basinOrbit initial n) houtside ih.2
      rw [basinOrbit_succ]
      constructor
      · calc
          (basinGain initial)^(n+1)*initial=
              basinGain initial*((basinGain initial)^n*initial) := by rw [pow_succ];ring
          _≤basinGain initial*basinOrbit initial n := mul_le_mul_of_nonneg_left ih.1 hq0
          _≤basinStep (basinOrbit initial n) := hstep.2.1
      · exact hstep.2.2
  have hp : Tendsto (fun n : ℕ => (basinGain initial)^n*initial) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt h0.1).atTop_mul_const hinit0
  exact ⟨h0.1,horbit,tendsto_atTop_mono (fun n => (horbit n).1) hp⟩

theorem actual_negative_exterior_y_has_geometric_escape_to_negative_infinity
    (initial : ℝ) (houtside : initial< -basinRadius) :
    1<basinGain (-initial) ∧
      (∀ n : ℕ, basinOrbit initial n≤ -((basinGain (-initial))^n*(-initial))) ∧
      Tendsto (basinOrbit initial) atTop atBot := by
  have hpositive:=actual_positive_exterior_y_has_geometric_escape_to_positive_infinity
    (-initial) (by linarith)
  refine ⟨hpositive.1,?_,?_⟩
  · intro n
    have h:=(hpositive.2.1 n).1
    rw [basinOrbit_odd] at h
    linarith
  · have h:=tendsto_neg_atTop_atBot.comp hpositive.2.2
    simpa only [Function.comp_def,basinOrbit_odd,neg_neg] using h

private theorem basinRadius_is_an_actual_fixed_point : basinStep basinRadius=basinRadius := by
  have hroot:=basinRadius_spec.2.1
  unfold basinSecant at hroot
  have ht:=(div_eq_iff basinRadius_spec.1.ne').mp hroot
  unfold basinStep
  nlinarith

private theorem basin_positive_fixed_point_unique (y : ℝ) (hy : 0<y)
    (hfixed : basinStep y=y) : y=basinRadius := by
  have ht : Real.tanh y=(1/4:ℝ)*y := by unfold basinStep at hfixed;nlinarith
  have hroot : basinSecant y=(1/4:ℝ) := (div_eq_iff hy.ne').mpr ht
  exact basinRadius_spec.2.2.2 y hy hroot

theorem actual_scalar_y_fixed_points_are_exactly_zero_and_the_two_critical_boundaries (y : ℝ) :
    basinStep y=y ↔ y=0 ∨ y=basinRadius ∨ y= -basinRadius := by
  constructor
  · intro hfixed
    by_cases hz : y=0
    · exact Or.inl hz
    · rcases lt_or_gt_of_ne hz with hy | hy
      · have hneg : 0< -y := by linarith
        have hfixedneg : basinStep (-y)= -y := by rw [basinStep_odd,hfixed]
        have hr:=basin_positive_fixed_point_unique (-y) hneg hfixedneg
        exact Or.inr (Or.inr (by linarith))
      · exact Or.inr (Or.inl (basin_positive_fixed_point_unique y hy hfixed))
  · rintro (rfl|rfl|rfl)
    · norm_num [basinStep]
    · exact basinRadius_is_an_actual_fixed_point
    · rw [basinStep_odd,basinRadius_is_an_actual_fixed_point]

theorem actual_physical_iterates_are_exactly_the_half_rescaled_y_iterates
    (initial : ℝ) (n : ℕ) :
    basinOrbit (2*initial) n=2*physicalOrbit initial n := by
  induction n with
  | zero => simp [basinOrbit,physicalOrbit]
  | succ n ih =>
    simp only [basinOrbit_succ,physicalOrbit_succ,ih]
    unfold basinStep physicalStep
    ring

private theorem basinOrbit_of_fixed_point (initial : ℝ) (hfixed : basinStep initial=initial)
    (n : ℕ) : basinOrbit initial n=initial := by
  induction n with
  | zero => simp [basinOrbit]
  | succ n ih => simp only [basinOrbit_succ,ih,hfixed]

private theorem basin_origin_convergence_iff_strictly_inside (initial : ℝ) :
    Tendsto (basinOrbit initial) atTop (𝓝 0) ↔ |initial|<basinRadius := by
  constructor
  · intro hconverges
    by_contra hinside
    have hge : basinRadius≤|initial| := le_of_not_gt hinside
    by_cases hboundary : |initial|=basinRadius
    · have hfixed : basinStep initial=initial := by
        apply (actual_scalar_y_fixed_points_are_exactly_zero_and_the_two_critical_boundaries initial).mpr
        by_cases hp : 0≤ initial
        · rw [abs_of_nonneg hp] at hboundary
          exact Or.inr (Or.inl hboundary)
        · rw [abs_of_neg (lt_of_not_ge hp)] at hboundary
          exact Or.inr (Or.inr (by linarith))
      have hconst : basinOrbit initial=(fun _ : ℕ => initial) := by
        funext n
        exact basinOrbit_of_fixed_point initial hfixed n
      rw [hconst] at hconverges
      have hz : initial=0 := tendsto_const_nhds_iff.mp hconverges
      rw [hz,abs_zero] at hboundary
      linarith [basinRadius_spec.1]
    · have hstrict : basinRadius < |initial| := by
        by_contra h
        have : |initial|=basinRadius := by linarith
        exact hboundary this
      by_cases hp : 0≤ initial
      · rw [abs_of_nonneg hp] at hstrict
        exact not_tendsto_nhds_of_tendsto_atTop
          (actual_positive_exterior_y_has_geometric_escape_to_positive_infinity initial hstrict).2.2
          0 hconverges
      · rw [abs_of_neg (lt_of_not_ge hp)] at hstrict
        exact not_tendsto_nhds_of_tendsto_atBot
          (actual_negative_exterior_y_has_geometric_escape_to_negative_infinity initial
            (by linarith)).2.2 0 hconverges
  · intro hinside
    obtain ⟨q,hq,hbound,hconverges⟩:=
      actual_every_interior_initial_y_has_all_time_origin_geometric_convergence initial hinside
    exact hconverges

private theorem physical_origin_convergence_iff_y_origin_convergence (initial : ℝ) :
    Tendsto (physicalOrbit initial) atTop (𝓝 0) ↔
      Tendsto (basinOrbit (2*initial)) atTop (𝓝 0) := by
  constructor
  · intro h
    have hc:=h.const_mul (2:ℝ)
    simpa only [←actual_physical_iterates_are_exactly_the_half_rescaled_y_iterates,mul_zero] using hc
  · intro h
    convert h.mul_const (1/2:ℝ) using 1
    · funext n
      rw [actual_physical_iterates_are_exactly_the_half_rescaled_y_iterates]
      ring
    · norm_num

theorem actual_physical_walkthrough_has_the_exact_open_basin_and_the_two_source_initial_states :
    (∀ initial : ℝ, Tendsto (physicalOrbit initial) atTop (𝓝 0) ↔ |2*initial|<basinRadius) ∧
      (∀ x : ℝ, physicalStep x=x ↔ x=0 ∨ x=basinRadius/2 ∨ x= -(basinRadius/2)) ∧
      Tendsto (physicalOrbit (3997/2000)) atTop (𝓝 0) ∧
      Tendsto (physicalOrbit (1999/1000)) atTop atTop ∧
      basinRadius/2∈Ioo (39973/20000:ℝ) (19987/10000) := by
  have hbasin (initial : ℝ) : Tendsto (physicalOrbit initial) atTop (𝓝 0) ↔
      |2*initial|<basinRadius :=
    (physical_origin_convergence_iff_y_origin_convergence initial).trans
      (basin_origin_convergence_iff_strictly_inside (2*initial))
  refine ⟨hbasin,?_,?_,?_,?_⟩
  · intro x
    have he : basinStep (2*x)=2*physicalStep x := by unfold basinStep physicalStep;ring
    have hfixed : physicalStep x=x ↔ basinStep (2*x)=2*x := by rw [he];constructor <;> intro h <;> linarith
    rw [hfixed,actual_scalar_y_fixed_points_are_exactly_zero_and_the_two_critical_boundaries]
    constructor
    · rintro (h|h|h)
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
    · rintro (h|h|h)
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  · apply (hbasin (3997/2000)).mpr
    norm_num
    linarith [basinRadius_spec.2.2.1.1]
  · have hy : basinRadius<2*(1999/1000:ℝ) := by linarith [basinRadius_spec.2.2.1.2]
    have h:=
      (actual_positive_exterior_y_has_geometric_escape_to_positive_infinity (2*(1999/1000)) hy).2.2
    convert h.atTop_mul_const (by norm_num : (0:ℝ)<1/2) using 1
    funext n
    rw [actual_physical_iterates_are_exactly_the_half_rescaled_y_iterates]
    ring
  · exact ⟨by linarith [basinRadius_spec.2.2.1.1],by linarith [basinRadius_spec.2.2.1.2]⟩

end SafeLearning.CompleteModulesNNWalkthroughLocal31

/- Separate literal scalar sector-LMI certificate-union support.
This new append is wholly uncompiled; the preceding passed36 source is exact.
Printed optimizer numbers and explorer claims remain outside this scope. -/
namespace SafeLearning.CompleteModulesNNWalkthroughLocal31

def uniformSectorMultiplier (alpha p : ℝ) : ℝ := p*(3/10)/(1-alpha)
def scalarBoxStorage (radius : ℝ) : ℝ := 4/radius^2
def scalarBoxContainment (radius p : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![radius^2,2;2,p]
def scalarStrictlyCertifiedState (x : ℝ) : Prop :=
  ∃ radius p lam : ℝ, 0<radius ∧ 0<p ∧ 0≤lam ∧
    (-walkthroughMatrix (13/10) (basinSecant radius) p lam).PosDef ∧
      (scalarBoxContainment radius p).PosSemidef ∧ p*x^2≤1

private theorem basin_positive_secant_is_at_most_one (radius : ℝ) (hr : 0<radius) :
    basinSecant radius≤1 := by
  have hpositive:=tanh_monotone hr.le
  simp only [Real.tanh_zero] at hpositive
  have hupper:=tanh_lipschitz.dist_le_mul radius 0
  simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul,
    abs_of_nonneg hpositive,abs_of_pos hr] at hupper
  exact (div_le_one hr).mpr hupper

private theorem basin_positive_secant_is_strictly_less_than_one (radius : ℝ) (hr : 0<radius) :
    basinSecant radius<1 := by
  have hh : 0<radius/2 := half_pos hr
  have hs:=actual_positive_tanh_origin_secants_strictly_decrease hh hr (by linarith)
  exact hs.trans_le (basin_positive_secant_is_at_most_one (radius/2) hh)

theorem actual_literal_sector_slope_exceeds_one_quarter_iff_radius_is_strictly_below_root
    (radius : ℝ) (hr : 0<radius) :
    (1/4:ℝ)<basinSecant radius ↔ radius<basinRadius := by
  constructor
  · intro hs
    by_contra hn
    have hle : basinRadius≤radius := le_of_not_gt hn
    have h:=actual_positive_tanh_origin_secants_strictly_decrease.antitoneOn
      basinRadius_spec.1 hr hle
    rw [basinRadius_spec.2.1] at h
    linarith
  · intro hsmall
    have h:=actual_positive_tanh_origin_secants_strictly_decrease hr basinRadius_spec.1 hsmall
    rwa [basinRadius_spec.2.1] at h

theorem actual_uniform_multiplier_has_the_exact_literal_determinant_and_negative_pivot
    (alpha p : ℝ) (ha : alpha≠1) :
    (walkthroughMatrix (13/10) alpha p (uniformSectorMultiplier alpha p)).det=
      p^2*(99/500)*(4*alpha-1)/(1-alpha) ∧
      (-walkthroughMatrix (13/10) alpha p (uniformSectorMultiplier alpha p)) 0 0=
        p*(309*alpha-69)/(100*(1-alpha)) := by
  have hn : 1-alpha≠0 := by intro h;apply ha;linarith
  constructor
  · rw [actual_local_walkthrough_determinant]
    unfold uniformSectorMultiplier
    field_simp [hn]
    ring
  · norm_num [walkthroughMatrix,uniformSectorMultiplier]
    field_simp [hn]
    ring

theorem actual_uniform_multiplier_is_strictly_feasible_for_every_storage_scale
    (alpha p : ℝ) (ha : alpha∈Ioo (1/4:ℝ) 1) (hp : 0<p) :
    0<uniformSectorMultiplier alpha p ∧
      (-walkthroughMatrix (13/10) alpha p (uniformSectorMultiplier alpha p)).PosDef := by
  have hden : 0<1-alpha := by linarith [ha.2]
  have hneq : alpha≠1 := ne_of_lt ha.2
  have hident:=actual_uniform_multiplier_has_the_exact_literal_determinant_and_negative_pivot alpha p hneq
  have hlam : 0<uniformSectorMultiplier alpha p := by unfold uniformSectorMultiplier;positivity
  have hfirst : 0<(-walkthroughMatrix (13/10) alpha p (uniformSectorMultiplier alpha p)) 0 0 := by
    rw [hident.2]
    have hn : 0<309*alpha-69 := by linarith [ha.1]
    positivity
  have hdet : 0<(walkthroughMatrix (13/10) alpha p (uniformSectorMultiplier alpha p)).det := by
    rw [hident.1]
    have hn : 0<4*alpha-1 := by linarith [ha.1]
    positivity
  have he : -walkthroughMatrix (13/10) alpha p (uniformSectorMultiplier alpha p)=
      planeMatrix (8*alpha*uniformSectorMultiplier alpha p-(69/100)*p)
        ((39/50)*p-2*(1+alpha)*uniformSectorMultiplier alpha p)
        (2*uniformSectorMultiplier alpha p-(9/25)*p) := by
    ext i j;fin_cases i <;> fin_cases j <;> norm_num [walkthroughMatrix,planeMatrix] <;> ring
  have hdetid :
      (8*alpha*uniformSectorMultiplier alpha p-(69/100)*p)*
          (2*uniformSectorMultiplier alpha p-(9/25)*p)-
        ((39/50)*p-2*(1+alpha)*uniformSectorMultiplier alpha p)^2=
      (walkthroughMatrix (13/10) alpha p (uniformSectorMultiplier alpha p)).det := by
    rw [actual_local_walkthrough_determinant]
    ring
  refine ⟨hlam,?_⟩
  rw [he,plane_pd_criterion]
  constructor
  · rw [he] at hfirst
    simpa [planeMatrix] using hfirst
  · rw [hdetid]
    exact hdet

theorem actual_any_literal_strict_quadratic_sector_LMI_requires_slope_above_one_quarter
    (alpha p lam : ℝ) (hp : 0<p)
    (hM : (-walkthroughMatrix (13/10) alpha p lam).PosDef) : (1/4:ℝ)<alpha := by
  have hn : (![1,2*alpha] : Fin 2 → ℝ)≠0 := by
    intro h
    have he:=congrFun h 0
    norm_num at he
  have hq:=hM.dotProduct_mulVec_pos hn
  have he : star (![1,2*alpha] : Fin 2 → ℝ) ⬝ᵥ
      ((-walkthroughMatrix (13/10) alpha p lam) *ᵥ ![1,2*alpha])=
      p*(1-((13/10)-(6/5)*alpha)^2) := by
    simp [walkthroughMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,star_trivial]
    ring
  rw [he] at hq
  have hprod : p*((13/10)-(6/5)*alpha)^2<p*1 := by nlinarith
  have hs : ((13/10)-(6/5)*alpha)^2<1 := lt_of_mul_lt_mul_left hprod hp.le
  nlinarith [sq_nonneg (((13/10)-(6/5)*alpha)-1)]

private theorem scalar_containment_projection (radius p : ℝ) (hr : 0<radius)
    (hc : (scalarBoxContainment radius p).PosSemidef) : 4≤p*radius^2 := by
  have hq : 0≤realQuadratic (scalarBoxContainment radius p)
      (![2/radius,-radius] : Fin 2 → ℝ) := by
    simpa only [realQuadratic,Pi.star_apply,star_trivial] using
      hc.dotProduct_mulVec_nonneg (![2/radius,-radius] : Fin 2 → ℝ)
  have he : realQuadratic (scalarBoxContainment radius p)
      (![2/radius,-radius] : Fin 2 → ℝ)=p*radius^2-4 := by
    change realQuadratic (planeMatrix (radius^2) 2 p) _=p*radius^2-4
    rw [plane_actual_form]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    field_simp [hr.ne']
    ring
  rw [he] at hq
  linarith

theorem actual_literal_containment_LMI_projects_every_quadratic_sublevel_into_the_sector_box
    (radius p x : ℝ) (hr : 0<radius) (hp : 0<p)
    (hc : (scalarBoxContainment radius p).PosSemidef) (hx : p*x^2≤1) :
    |2*x|≤radius := by
  have hproject:=scalar_containment_projection radius p hr hc
  have hupper:=mul_le_mul_of_nonneg_right hx (sq_nonneg radius)
  have hlower:=mul_le_mul_of_nonneg_right hproject (sq_nonneg x)
  have hs : (2*x)^2≤radius^2 := by nlinarith
  exact (sq_le_sq₀ (abs_nonneg (2*x)) hr.le).mp (by simpa only [sq_abs] using hs)

private theorem scalar_exact_storage_containment_identity (radius : ℝ) (hr : 0<radius)
    (x : Fin 2 → ℝ) :
    realQuadratic (scalarBoxContainment radius (scalarBoxStorage radius)) x=
      (radius*x 0+(2/radius)*x 1)^2 := by
  change realQuadratic (planeMatrix (radius^2) 2 (4/radius^2)) x=_
  rw [plane_actual_form]
  field_simp [hr.ne']
  ring

private theorem scalar_exact_storage_containment_semidefinite (radius : ℝ) (hr : 0<radius) :
    (scalarBoxContainment radius (scalarBoxStorage radius)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j;fin_cases i <;> fin_cases j <;> simp [scalarBoxContainment,Matrix.conjTranspose_apply]
  · intro x
    have h : 0≤realQuadratic (scalarBoxContainment radius (scalarBoxStorage radius)) x := by
      rw [scalar_exact_storage_containment_identity radius hr x]
      exact sq_nonneg _
    simpa only [realQuadratic,Pi.star_apply,star_trivial] using h

private theorem scalar_exact_storage_sublevel_iff_sector_box (radius x : ℝ) (hr : 0<radius) :
    scalarBoxStorage radius*x^2≤1 ↔ |2*x|≤radius := by
  unfold scalarBoxStorage
  have he : (4/radius^2)*x^2=(2*x)^2/radius^2 := by ring
  rw [he,div_le_iff₀ (sq_pos_of_pos hr)]
  simp only [one_mul]
  simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg (2*x)) hr.le

theorem actual_every_strictly_subcritical_radius_has_an_explicit_literal_LMI_and_containment_certificate
    (radius : ℝ) (hr : 0<radius) (hsmall : radius<basinRadius) :
    0<scalarBoxStorage radius ∧
      0<uniformSectorMultiplier (basinSecant radius) (scalarBoxStorage radius) ∧
      (-walkthroughMatrix (13/10) (basinSecant radius) (scalarBoxStorage radius)
        (uniformSectorMultiplier (basinSecant radius) (scalarBoxStorage radius))).PosDef ∧
      (scalarBoxContainment radius (scalarBoxStorage radius)).PosSemidef ∧
      (scalarBoxContainment radius (scalarBoxStorage radius)).det=0 ∧
      (∀ x : ℝ, scalarBoxStorage radius*x^2≤1 ↔ |2*x|≤radius) ∧
      (∀ v : ℝ, |v|≤radius →
        0≤2*(Real.tanh v-basinSecant radius*v)*(v-Real.tanh v)) := by
  have hp : 0<scalarBoxStorage radius := by unfold scalarBoxStorage;positivity
  have ha : basinSecant radius∈Ioo (1/4:ℝ) 1 :=
    ⟨(actual_literal_sector_slope_exceeds_one_quarter_iff_radius_is_strictly_below_root radius hr).mpr hsmall,
      basin_positive_secant_is_strictly_less_than_one radius hr⟩
  have hM:=actual_uniform_multiplier_is_strictly_feasible_for_every_storage_scale
    (basinSecant radius) (scalarBoxStorage radius) ha hp
  have hc:=scalar_exact_storage_containment_semidefinite radius hr
  have hdet : (scalarBoxContainment radius (scalarBoxStorage radius)).det=0 := by
    norm_num [scalarBoxContainment,Matrix.det_fin_two]
    unfold scalarBoxStorage
    field_simp [hr.ne']
    ring
  refine ⟨hp,hM.1,hM.2,hc,hdet,fun x => scalar_exact_storage_sublevel_iff_sector_box radius x hr,?_⟩
  intro v hv
  have h:=tanh_local_origin_sector radius v hr hv
  change 0≤(Real.tanh v-basinSecant radius*v)*(v-Real.tanh v) at h
  nlinarith

theorem actual_literal_strict_certificate_radii_are_exactly_the_positive_radii_below_root
    (radius : ℝ) (hr : 0<radius) :
    (∃ p lam : ℝ, 0<p ∧ 0≤lam ∧
      (-walkthroughMatrix (13/10) (basinSecant radius) p lam).PosDef ∧
      (scalarBoxContainment radius p).PosSemidef) ↔ radius<basinRadius := by
  constructor
  · rintro ⟨p,lam,hp,hlam,hM,hc⟩
    apply (actual_literal_sector_slope_exceeds_one_quarter_iff_radius_is_strictly_below_root radius hr).mp
    exact actual_any_literal_strict_quadratic_sector_LMI_requires_slope_above_one_quarter
      (basinSecant radius) p lam hp hM
  · intro hsmall
    have h:=actual_every_strictly_subcritical_radius_has_an_explicit_literal_LMI_and_containment_certificate
      radius hr hsmall
    exact ⟨scalarBoxStorage radius,
      uniformSectorMultiplier (basinSecant radius) (scalarBoxStorage radius),
      h.1,h.2.1.le,h.2.2.1,h.2.2.2.1⟩

theorem actual_union_of_literal_strict_certified_ellipsoids_equals_the_open_basin_and_excludes_root_box :
    (∀ x : ℝ, scalarStrictlyCertifiedState x ↔ |2*x|<basinRadius) ∧
      (∀ x : ℝ, scalarStrictlyCertifiedState x ↔ Tendsto (physicalOrbit x) atTop (𝓝 0)) ∧
      ¬(∃ p lam : ℝ, 0<p ∧ 0≤lam ∧
        (-walkthroughMatrix (13/10) (basinSecant basinRadius) p lam).PosDef) := by
  have hregion (x : ℝ) : scalarStrictlyCertifiedState x ↔ |2*x|<basinRadius := by
    constructor
    · rintro ⟨radius,p,lam,hr,hp,hlam,hM,hc,hx⟩
      have hsmall:=(actual_literal_strict_certificate_radii_are_exactly_the_positive_radii_below_root
        radius hr).mp ⟨p,lam,hp,hlam,hM,hc⟩
      have hbox:=actual_literal_containment_LMI_projects_every_quadratic_sublevel_into_the_sector_box
        radius p x hr hp hc hx
      exact hbox.trans_lt hsmall
    · intro hx
      let radius : ℝ := (|2*x|+basinRadius)/2
      have hr : 0<radius := by dsimp [radius];linarith [abs_nonneg (2*x),basinRadius_spec.1]
      have hsmall : radius<basinRadius := by dsimp [radius];linarith
      have hbox : |2*x|≤radius := by dsimp [radius];linarith
      have h:=actual_every_strictly_subcritical_radius_has_an_explicit_literal_LMI_and_containment_certificate
        radius hr hsmall
      refine ⟨radius,scalarBoxStorage radius,
        uniformSectorMultiplier (basinSecant radius) (scalarBoxStorage radius),
        hr,h.1,h.2.1.le,h.2.2.1,h.2.2.2.1,?_⟩
      exact (h.2.2.2.2.2.1 x).mpr hbox
  refine ⟨hregion,?_,?_⟩
  · intro x
    exact (hregion x).trans
      (actual_physical_walkthrough_has_the_exact_open_basin_and_the_two_source_initial_states.1 x).symm
  · rintro ⟨p,lam,hp,hlam,hM⟩
    have h:=actual_any_literal_strict_quadratic_sector_LMI_requires_slope_above_one_quarter
      (basinSecant basinRadius) p lam hp hM
    rw [basinRadius_spec.2.1] at h
    exact (lt_irrefl (1/4:ℝ)) h

end SafeLearning.CompleteModulesNNWalkthroughLocal31

/- Separate actual global-model trajectory and determinant-optimizer append.
New bodies are wholly uncompiled; the passed44 prefix is immutable. -/
namespace SafeLearning.CompleteModulesNNWalkthroughLocal31

def globalPhysicalStep (x : ℝ) : ℝ := (4/5)*x-(3/5)*Real.tanh (2*x)
def globalPhysicalOrbit (initial : ℝ) (n : ℕ) : ℝ := (globalPhysicalStep^[n]) initial

theorem actual_global_determinant_has_the_unique_exact_maximizing_multiplier
    (p lam : ℝ) :
    (walkthroughMatrix (4/5) 0 p lam).det≤
      (walkthroughMatrix (4/5) 0 p ((33/100)*p)).det ∧
      ((walkthroughMatrix (4/5) 0 p lam).det=
        (walkthroughMatrix (4/5) 0 p ((33/100)*p)).det ↔ lam=(33/100)*p) := by
  have hid : (walkthroughMatrix (4/5) 0 p ((33/100)*p)).det-
      (walkthroughMatrix (4/5) 0 p lam).det=4*(lam-(33/100)*p)^2 := by
    rw [actual_global_walkthrough_determinant,actual_global_walkthrough_determinant]
    ring
  constructor
  · nlinarith [sq_nonneg (lam-(33/100)*p)]
  · constructor
    · intro heq
      have hs : (lam-(33/100)*p)^2=0 := by linarith
      have hz:=sq_eq_zero_iff.mp hs
      linarith
    · intro heq
      rw [heq]

private theorem globalPhysicalStep_odd (x : ℝ) :
    globalPhysicalStep (-x)= -globalPhysicalStep x := by
  unfold globalPhysicalStep
  simp only [mul_neg,Real.tanh_neg]
  ring

private theorem actual_global_nonnegative_state_origin_bound (x : ℝ) (hx : 0≤x) :
    |globalPhysicalStep x|≤(4/5)*x := by
  have hpositive:=tanh_monotone (show (0:ℝ)≤2*x by linarith)
  simp only [Real.tanh_zero] at hpositive
  have hupper:=tanh_lipschitz.dist_le_mul (2*x) 0
  simp only [Real.dist_eq,Real.tanh_zero,sub_zero,NNReal.coe_one,one_mul,
    abs_of_nonneg hpositive,abs_of_nonneg (show (0:ℝ)≤2*x by linarith)] at hupper
  apply abs_le.mpr
  unfold globalPhysicalStep
  constructor <;> nlinarith

theorem actual_global_physical_loop_has_the_true_four_fifths_origin_norm_bound (x : ℝ) :
    |globalPhysicalStep x|≤(4/5)*|x| := by
  by_cases hx : 0≤x
  · simpa only [abs_of_nonneg hx] using actual_global_nonnegative_state_origin_bound x hx
  · have h:=actual_global_nonnegative_state_origin_bound (-x) (by linarith)
    simpa only [globalPhysicalStep_odd,abs_neg,abs_of_neg (lt_of_not_ge hx)] using h

private theorem globalPhysicalOrbit_succ (initial : ℝ) (n : ℕ) :
    globalPhysicalOrbit initial (n+1)=globalPhysicalStep (globalPhysicalOrbit initial n) := by
  simp [globalPhysicalOrbit,Function.iterate_succ_apply']

theorem actual_every_global_physical_trajectory_has_an_all_time_geometric_bound
    (initial : ℝ) (n : ℕ) :
    |globalPhysicalOrbit initial n|≤(4/5:ℝ)^n*|initial| := by
  induction n with
  | zero => simp [globalPhysicalOrbit]
  | succ n ih =>
    rw [globalPhysicalOrbit_succ]
    calc
      |globalPhysicalStep (globalPhysicalOrbit initial n)|≤(4/5)*|globalPhysicalOrbit initial n| :=
        actual_global_physical_loop_has_the_true_four_fifths_origin_norm_bound _
      _≤(4/5)*((4/5:ℝ)^n*|initial|) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _=(4/5:ℝ)^(n+1)*|initial| := by rw [pow_succ];ring

theorem actual_every_global_physical_initial_state_converges_to_zero (initial : ℝ) :
    Tendsto (globalPhysicalOrbit initial) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (4/5:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hu : Tendsto (fun n : ℕ => (4/5:ℝ)^n*|initial|) atTop (𝓝 0) := by
    simpa only [zero_mul] using hp.mul_const |initial|
  have habs : Tendsto (fun n : ℕ => |globalPhysicalOrbit initial n|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) (actual_every_global_physical_trajectory_has_an_all_time_geometric_bound initial) hu
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

theorem actual_global_quadratic_storage_has_the_true_geometric_energy_bound
    (p initial : ℝ) (hp : 0≤p) (n : ℕ) :
    p*(globalPhysicalOrbit initial n)^2≤(4/5:ℝ)^(2*n)*(p*initial^2) := by
  have h:=actual_every_global_physical_trajectory_has_an_all_time_geometric_bound initial n
  have hs : (globalPhysicalOrbit initial n)^2≤((4/5:ℝ)^n)^2*initial^2 := by
    have hb:=pow_le_pow_left₀ (abs_nonneg (globalPhysicalOrbit initial n)) h 2
    simpa only [mul_pow,sq_abs] using hb
  have hscaled:=mul_le_mul_of_nonneg_left hs hp
  calc
    p*(globalPhysicalOrbit initial n)^2≤p*(((4/5:ℝ)^n)^2*initial^2) := hscaled
    _=(4/5:ℝ)^(2*n)*(p*initial^2) := by
      rw [←pow_mul]
      rw [show n*2=2*n by omega]
      ring

end SafeLearning.CompleteModulesNNWalkthroughLocal31
