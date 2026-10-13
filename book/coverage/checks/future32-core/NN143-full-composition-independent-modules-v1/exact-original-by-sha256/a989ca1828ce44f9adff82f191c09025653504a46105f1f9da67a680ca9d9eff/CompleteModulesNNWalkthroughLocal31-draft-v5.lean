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
