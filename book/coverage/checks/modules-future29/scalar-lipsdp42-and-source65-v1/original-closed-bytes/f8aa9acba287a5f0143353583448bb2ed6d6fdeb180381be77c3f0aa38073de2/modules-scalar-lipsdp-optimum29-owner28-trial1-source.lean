import SafeLearning.Modules

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Matrix
namespace SafeLearning.CompleteModulesScalarLipSDPOptimum29

def sourceMatrix (a beta t rho w0 w1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-2*a*beta*w0^2*t-rho,(a+beta)*w0*t;(a+beta)*w0*t,-2*t+w1^2]
def objective (a beta w1 t : ℝ) : ℝ :=
  (a+beta)^2*t^2/(2*t-w1^2)-2*a*beta*t
def firstDerivative (a beta w1 t : ℝ) : ℝ :=
  2*(a+beta)^2*t*(t-w1^2)/(2*t-w1^2)^2-2*a*beta
def secondDerivative (a beta w1 t : ℝ) : ℝ :=
  2*(a+beta)^2*w1^4/(2*t-w1^2)^3
def optimalMultiplier (a beta w1 : ℝ) : ℝ := beta*w1^2/(beta-a)
def scalarNetwork (phi : ℝ → ℝ) (w0 w1 b c x : ℝ) : ℝ := w1*phi (w0*x+b)+c
def slopeRestricted (phi : ℝ → ℝ) (a beta : ℝ) : Prop :=
  ∀ x y : ℝ,x≠y → a≤(phi x-phi y)/(x-y) ∧ (phi x-phi y)/(x-y)≤beta
def realLipschitzBound (f : ℝ → ℝ) (L : ℝ) : Prop :=
  0≤L ∧ ∀ x y : ℝ,|f x-f y|≤L*|x-y|
def derivativeSupremum (phi : ℝ → ℝ) : ℝ := sSup (Set.range (deriv phi))

theorem actual_source_matrix_quadratic_expansion (a beta t rho w0 w1 : ℝ)
    (v : Fin 2 → ℝ) :
    v ⬝ᵥ (sourceMatrix a beta t rho w0 w1 *ᵥ v)=
      (-2*a*beta*w0^2*t-rho)*(v 0)^2+
        2*((a+beta)*w0*t)*(v 0)*(v 1)+(-2*t+w1^2)*(v 1)^2 := by
  simp [sourceMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_schur_square_identity (a beta t rho w0 w1 : ℝ)
    (ht : 2*t-w1^2≠0) (v : Fin 2 → ℝ) :
    v ⬝ᵥ ((-(sourceMatrix a beta t rho w0 w1)) *ᵥ v)=
      (2*t-w1^2)*(v 1-((a+beta)*w0*t)/(2*t-w1^2)*v 0)^2+
        (rho-w0^2*objective a beta w1 t)*(v 0)^2 := by
  simp [sourceMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,objective]
  field_simp [ht]
  ring

theorem actual_matrix_feasible_iff_fixed_multiplier_lower_bound
    (a beta t rho w0 w1 : ℝ) (ht : w1^2/2<t) :
    (-(sourceMatrix a beta t rho w0 w1)).PosSemidef ↔
      w0^2*objective a beta w1 t≤rho := by
  have hd : 0<2*t-w1^2 := by linarith
  constructor
  · intro h
    have hv := h.dotProduct_mulVec_nonneg
      (![1,((a+beta)*w0*t)/(2*t-w1^2)]:Fin 2 → ℝ)
    simp only [star_trivial] at hv
    rw [actual_schur_square_identity a beta t rho w0 w1 (ne_of_gt hd)] at hv
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,sub_self,zero_pow,mul_zero,
      one_pow,mul_one,zero_add] using hv
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [sourceMatrix,Matrix.conjTranspose_apply]
    · intro v
      simp only [star_trivial]
      rw [actual_schur_square_identity a beta t rho w0 w1 (ne_of_gt hd)]
      exact add_nonneg (mul_nonneg hd.le (sq_nonneg _))
        (mul_nonneg (sub_nonneg.mpr h) (sq_nonneg _))

theorem actual_smallest_feasible_rho_at_fixed_multiplier
    (a beta t w0 w1 : ℝ) (ht : w1^2/2<t) :
    IsLeast {rho : ℝ | (-(sourceMatrix a beta t rho w0 w1)).PosSemidef}
      (w0^2*objective a beta w1 t) := by
  constructor
  · exact (actual_matrix_feasible_iff_fixed_multiplier_lower_bound a beta t _ w0 w1 ht).mpr le_rfl
  · intro rho h
    exact (actual_matrix_feasible_iff_fixed_multiplier_lower_bound a beta t rho w0 w1 ht).mp h

theorem actual_every_feasible_multiplier_is_in_the_strict_schur_domain
    (a beta t rho w0 w1 : ℝ) (ha : 0≤a) (hab : a<beta)
    (hw0 : w0≠0) (hw1 : w1≠0)
    (h : (-(sourceMatrix a beta t rho w0 w1)).PosSemidef) : w1^2/2<t := by
  have hdiag := h.dotProduct_mulVec_nonneg (![0,1]:Fin 2 → ℝ)
  norm_num [sourceMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hdiag
  have hq : 0<w1^2 := sq_pos_of_ne_zero hw1
  have htpos : 0<t := by nlinarith
  have habpos : 0<a+beta := by linarith
  have hoff : (a+beta)*w0*t≠0 := mul_ne_zero (mul_ne_zero (ne_of_gt habpos) hw0) htpos.ne'
  have hdet := h.det_nonneg
  simp [sourceMatrix,Matrix.det_fin_two] at hdet
  by_contra hn
  have he : 2*t-w1^2=0 := by linarith
  have he' : 2*t=w1^2 := by linarith
  rw [he'] at hdet
  nlinarith [sq_pos_of_ne_zero hoff]

theorem actual_objective_gap_is_a_nonnegative_square
    (a beta w1 t : ℝ) (ht : 2*t-w1^2≠0) :
    objective a beta w1 t-beta^2*w1^2=
      ((beta-a)*t-beta*w1^2)^2/(2*t-w1^2) := by
  unfold objective
  field_simp [ht]
  ring

theorem actual_optimal_multiplier_is_in_the_strict_domain
    (a beta w1 : ℝ) (ha : 0≤a) (hab : a<beta) (hw1 : w1≠0) :
    w1^2/2<optimalMultiplier a beta w1 := by
  have hd : 0<beta-a := sub_pos.mpr hab
  have hq : 0<w1^2 := sq_pos_of_ne_zero hw1
  unfold optimalMultiplier
  apply (lt_div_iff₀ hd).mpr
  nlinarith [mul_pos (by linarith : 0<a+beta) hq]

theorem actual_global_objective_bound_and_exact_equality
    (a beta w1 t : ℝ) (ha : 0≤a) (hab : a<beta) (ht : w1^2/2<t) :
    beta^2*w1^2≤objective a beta w1 t ∧
      (objective a beta w1 t=beta^2*w1^2 ↔ t=optimalMultiplier a beta w1) := by
  have hd : 0<2*t-w1^2 := by linarith
  have hdelta : beta-a≠0 := (sub_pos.mpr hab).ne'
  have he := actual_objective_gap_is_a_nonnegative_square a beta w1 t hd.ne'
  constructor
  · have hp : 0≤((beta-a)*t-beta*w1^2)^2/(2*t-w1^2) := div_nonneg (sq_nonneg _) hd.le
    linarith
  · constructor
    · intro h
      have hz : ((beta-a)*t-beta*w1^2)^2=0 := by
        have he0 : ((beta-a)*t-beta*w1^2)^2/(2*t-w1^2)=0 := by linarith
        exact (div_eq_zero_iff).mp he0 |>.resolve_right hd.ne'
      have hx : (beta-a)*t-beta*w1^2=0 := sq_eq_zero_iff.mp hz
      unfold optimalMultiplier
      apply (eq_div_iff hdelta).mpr
      linarith
    · intro h
      rw [h] at he
      have hz : (beta-a)*optimalMultiplier a beta w1-beta*w1^2=0 := by
        unfold optimalMultiplier
        field_simp [hdelta]
        ring
      rw [hz,zero_pow,zero_div] at he
      linarith

theorem actual_optimal_rho_is_attained_and_is_globally_least
    (a beta w0 w1 : ℝ) (ha : 0≤a) (hab : a<beta) (hw0 : w0≠0) (hw1 : w1≠0) :
    (-(sourceMatrix a beta (optimalMultiplier a beta w1)
      (beta^2*w0^2*w1^2) w0 w1)).PosSemidef ∧
    (∀ t rho : ℝ,( -(sourceMatrix a beta t rho w0 w1)).PosSemidef →
      beta^2*w0^2*w1^2≤rho) := by
  have ht := actual_optimal_multiplier_is_in_the_strict_domain a beta w1 ha hab hw1
  have hmin := actual_global_objective_bound_and_exact_equality a beta w1
    (optimalMultiplier a beta w1) ha hab ht
  have he : objective a beta w1 (optimalMultiplier a beta w1)=beta^2*w1^2 := hmin.2.mpr rfl
  constructor
  · apply (actual_matrix_feasible_iff_fixed_multiplier_lower_bound a beta _ _ w0 w1 ht).mpr
    rw [he]
    ring_nf
    exact le_rfl
  · intro t rho h
    have hdomain := actual_every_feasible_multiplier_is_in_the_strict_schur_domain
      a beta t rho w0 w1 ha hab hw0 hw1 h
    have hlow := (actual_matrix_feasible_iff_fixed_multiplier_lower_bound
      a beta t rho w0 w1 hdomain).mp h
    have hg := (actual_global_objective_bound_and_exact_equality a beta w1 t ha hab hdomain).1
    have hm := mul_le_mul_of_nonneg_left hg (sq_nonneg w0)
    nlinarith

theorem actual_objective_has_the_printed_first_derivative
    (a beta w1 t : ℝ) (ht : 2*t-w1^2≠0) :
    HasDerivAt (objective a beta w1) (firstDerivative a beta w1 t) t := by
  have h := ((((hasDerivAt_id t).pow 2).const_mul ((a+beta)^2)).div
    (((hasDerivAt_id t).const_mul 2).sub_const (w1^2)) ht).sub
      ((hasDerivAt_id t).const_mul (2*a*beta))
  convert h using 1 <;> dsimp [objective,firstDerivative]
  · field_simp [ht]
    ring
  · ext x
    ring

theorem actual_first_derivative_has_the_printed_second_derivative
    (a beta w1 t : ℝ) (ht : 2*t-w1^2≠0) :
    HasDerivAt (firstDerivative a beta w1) (secondDerivative a beta w1 t) t := by
  have h := (((((hasDerivAt_id t).mul ((hasDerivAt_id t).sub_const (w1^2))).const_mul
    (2*(a+beta)^2)).div ((((hasDerivAt_id t).const_mul 2).sub_const (w1^2)).pow 2)
      (pow_ne_zero 2 ht)).sub_const (2*a*beta))
  convert h using 1 <;> dsimp [firstDerivative,secondDerivative]
  · field_simp [ht]
    ring
  · ext x
    ring

theorem actual_stationary_point_equation_and_unique_root
    (a beta w1 t : ℝ) (ha : 0≤a) (hab : a<beta) (hw1 : w1≠0)
    (ht : w1^2/2<t) :
    firstDerivative a beta w1 t=0 ↔ t=optimalMultiplier a beta w1 := by
  have hd : 0<2*t-w1^2 := by linarith
  have hq : 0<w1^2 := sq_pos_of_ne_zero hw1
  have htpos : 0<t := by nlinarith
  have hdelta : 0<beta-a := sub_pos.mpr hab
  have hf : firstDerivative a beta w1 t=
      2*((beta-a)*t-beta*w1^2)*((beta-a)*t+a*w1^2)/(2*t-w1^2)^2 := by
    unfold firstDerivative
    field_simp [hd.ne']
    ring
  have hp : 0<(beta-a)*t+a*w1^2 := add_pos_of_pos_of_nonneg
    (mul_pos hdelta htpos) (mul_nonneg ha hq.le)
  rw [hf]
  constructor
  · intro h
    have hz : 2*((beta-a)*t-beta*w1^2)*((beta-a)*t+a*w1^2)=0 :=
      (div_eq_zero_iff).mp h |>.resolve_right (pow_ne_zero 2 hd.ne')
    have hz1 : (beta-a)*t-beta*w1^2=0 := by
      rcases mul_eq_zero.mp hz with h|h
      · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
      · exact (hp.ne' h).elim
    unfold optimalMultiplier
    apply (eq_div_iff hdelta.ne').mpr
    linarith
  · intro h
    rw [h]
    have hz : (beta-a)*optimalMultiplier a beta w1-beta*w1^2=0 := by
      unfold optimalMultiplier
      field_simp [hdelta.ne']
      ring
    simp [hz]

theorem actual_second_derivative_is_strictly_positive
    (a beta w1 t : ℝ) (ha : 0≤a) (hab : a<beta) (hw1 : w1≠0)
    (ht : w1^2/2<t) : 0<secondDerivative a beta w1 t := by
  have hd : 0<2*t-w1^2 := by linarith
  have hs : 0<a+beta := by linarith
  unfold secondDerivative
  exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hs))
    (pow_pos (abs_pos.mpr hw1) 4 |>.trans_eq (by simp))) (pow_pos hd 3)

/-- These are source hypotheses on the actual activation, not derivative assumptions. -/
theorem actual_slope_restriction_implies_monotonicity_and_global_bound
    (phi : ℝ → ℝ) (a beta : ℝ) (ha : 0≤a) (hab : a<beta)
    (hp : slopeRestricted phi a beta) : Monotone phi ∧ realLipschitzBound phi beta := by
  have hb : 0≤beta := by linarith
  have hordered : ∀ x y : ℝ,x<y → 0≤phi y-phi x ∧ phi y-phi x≤beta*(y-x) := by
    intro x y hxy
    have h := hp y x hxy.ne'
    have hlo := (le_div_iff₀ (sub_pos.mpr hxy)).mp h.1
    have hhi := (div_le_iff₀ (sub_pos.mpr hxy)).mp h.2
    exact ⟨by nlinarith [mul_nonneg ha (sub_nonneg.mpr hxy.le)],hhi⟩
  constructor
  · intro x y hxy
    rcases hxy.eq_or_lt with he|ht
    · simp [he]
    · linarith [(hordered x y ht).1]
  · constructor
    · exact hb
    · intro x y
      rcases lt_trichotomy x y with h|h|h
      · have he := hordered x y h
        rw [abs_of_nonpos (by linarith : phi x-phi y≤0),abs_of_nonpos (by linarith : x-y≤0)]
        nlinarith
      · simp [h]
      · have he := hordered y x h
        rw [abs_of_nonneg he.1,abs_of_nonneg (sub_nonneg.mpr h.le)]
        exact he.2

theorem actual_real_bound_iff_mathlib_lipschitz (f : ℝ → ℝ) (L : ℝ) (hL : 0≤L) :
    realLipschitzBound f L ↔ LipschitzWith ⟨L,hL⟩ f := by
  constructor
  · intro h
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [Real.dist_eq,NNReal.coe_mk] using h.2 x y
  · intro h
    exact ⟨hL,by simpa only [Real.dist_eq,NNReal.coe_mk] using h.dist_le_mul⟩

theorem actual_derivative_supremum_is_the_least_activation_lipschitz_constant
    (phi : ℝ → ℝ) (a beta : ℝ) (ha : 0≤a) (hab : a<beta)
    (hp : slopeRestricted phi a beta) :
    IsLeast {L : ℝ | realLipschitzBound phi L} (derivativeSupremum phi) := by
  have hmon := (actual_slope_restriction_implies_monotonicity_and_global_bound phi a beta ha hab hp).1
  have hbeta := (actual_slope_restriction_implies_monotonicity_and_global_bound phi a beta ha hab hp).2
  have hlip := (actual_real_bound_iff_mathlib_lipschitz phi beta hbeta.1).mp hbeta
  have hder : ∀ x : ℝ,0≤deriv phi x ∧ deriv phi x≤beta := by
    intro x
    constructor
    · exact hmon.deriv_nonneg
    · have hn := norm_deriv_le_of_lipschitz (x₀:=x) hlip
      rw [Real.norm_eq_abs,abs_of_nonneg hmon.deriv_nonneg] at hn
      exact hn
  have hbdd : BddAbove (Set.range (deriv phi)) := ⟨beta,by rintro _ ⟨x,rfl⟩;exact (hder x).2⟩
  have hsup : ∀ x : ℝ,deriv phi x≤derivativeSupremum phi :=
    fun x=>le_csSup hbdd (Set.mem_range_self x)
  have hsnonneg : 0≤derivativeSupremum phi := le_trans (hder 0).1 (hsup 0)
  have hsbound : realLipschitzBound phi (derivativeSupremum phi) := by
    constructor
    · exact hsnonneg
    · intro x y
      have ordered : ∀ u v : ℝ,u≤v → phi v-phi u≤derivativeSupremum phi*(v-u) := by
        intro u v huv
        have hac := hlip.lipschitzOnWith.absolutelyContinuousOnInterval (a:=u) (b:=v)
        have hi := intervalIntegral.integral_mono_on huv hac.intervalIntegrable_deriv
          (intervalIntegrable_const (c:=derivativeSupremum phi)) (fun t _=>hsup t)
        rw [hac.integral_deriv_eq_sub,intervalIntegral.integral_const] at hi
        simpa only [smul_eq_mul,mul_comm] using hi
      rcases le_total x y with h|h
      · rw [abs_of_nonpos (by linarith [hmon h] : phi x-phi y≤0),
          abs_of_nonpos (sub_nonpos.mpr h)]
        linarith [ordered x y h]
      · rw [abs_of_nonneg (sub_nonneg.mpr (hmon h)),abs_of_nonneg (sub_nonneg.mpr h)]
        exact ordered y x h
  constructor
  · exact hsbound
  · intro L hL
    unfold derivativeSupremum
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x,rfl⟩
    have hl := (actual_real_bound_iff_mathlib_lipschitz phi L hL.1).mp hL
    have hn := norm_deriv_le_of_lipschitz (x₀:=x) hl
    rw [Real.norm_eq_abs,abs_of_nonneg hmon.deriv_nonneg] at hn
    exact hn

end SafeLearning.CompleteModulesScalarLipSDPOptimum29
