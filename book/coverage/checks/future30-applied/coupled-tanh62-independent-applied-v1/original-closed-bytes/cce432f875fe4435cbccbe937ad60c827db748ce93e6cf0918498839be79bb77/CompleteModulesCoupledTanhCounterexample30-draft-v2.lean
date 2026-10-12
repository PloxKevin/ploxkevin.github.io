import SafeLearning.CompleteModulesInvalidQC
import SafeLearning.CompleteModulesTanhNumerics
import SafeLearning.CompleteModulesTanhAsymptotic
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Set Filter Matrix
open scoped BigOperators Topology
namespace SafeLearning.CompleteModulesCoupledTanhCounterexample30

open CompleteModulesTheory CompleteModulesTanhChords CompleteModulesTanhNumerics
open CompleteModulesInvalidQC CompleteModulesLipSDPNetwork

def firstWeight : Matrix (Fin 2) (Fin 1) ℝ := !![-1;-1]
def lastWeight : Matrix (Fin 1) (Fin 2) ℝ := !![-1,1]
def firstBias : Fin 2 → ℝ := ![-1,1]
def lastBias : Fin 1 → ℝ := ![-1/2]
def network (x : ℝ) : ℝ := Real.tanh (x+1)-Real.tanh (x-1)-1/2
def networkDerivative (x : ℝ) : ℝ :=
  (1-(Real.tanh (x+1))^2)-(1-(Real.tanh (x-1))^2)
def networkSecondDerivative (x : ℝ) : ℝ :=
  -2*(1-(Real.tanh (x+1))^2)*Real.tanh (x+1)+
    2*(1-(Real.tanh (x-1))^2)*Real.tanh (x-1)

def fullCertificate (rho : ℝ) (T : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks (-rho • 1) (firstWeightᵀ*T) (T*firstWeight)
    ((-2:ℝ) • T+lastWeightᵀ*lastWeight)
def coupledMatrix (rho : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-rho,0,0;0,-1,1;0,1,-1]
def diagonalMatrix (rho t0 t1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-rho,-t0,-t1;-t0,1-2*t0,-1;-t1,-1,1-2*t1]
def eigenBasis : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0;0,1,1;0,-1,1]
def inverseEigenBasis : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,0,0;0,1/2,-1/2;0,1/2,1/2]
def realLipschitzBound (f : ℝ → ℝ) (L : ℝ) : Prop :=
  0≤L ∧ ∀ x y : ℝ, |f x-f y|≤L*|x-y|

theorem actual_network_is_the_stated_affine_tanh_composition (x : ℝ) :
    (oneHiddenNetwork firstWeight lastWeight firstBias lastBias Real.tanh
      (![x] : Fin 1 → ℝ)) 0=network x := by
  simp [oneHiddenNetwork,hiddenValues,firstWeight,lastWeight,firstBias,lastBias,
    network,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  have h0 : -x-1=-(x+1) := by ring
  have h1 : -x+1=-(x-1) := by ring
  rw [h0,h1,Real.tanh_neg,Real.tanh_neg]
  ring

theorem actual_relu_points_increments_and_negative_qc :
    (![0,1] : Fin 2 → ℝ)-![-3/2,0]=![3/2,1] ∧
    reluVector (![0,1] : Fin 2 → ℝ)-reluVector ![-3/2,0]=![0,1] ∧
    coupledIncrementQC (![0,1] : Fin 2 → ℝ) ![-3/2,0]= -3 ∧
    ¬ 0≤coupledIncrementQC (![0,1] : Fin 2 → ℝ) ![-3/2,0] := by
  refine ⟨?_,?_,actual_paper_coupled_relu_failure,?_⟩
  · ext i; fin_cases i <;> norm_num
  · ext i; fin_cases i <;> norm_num [reluVector]
  · rw [actual_paper_coupled_relu_failure]; norm_num

theorem actual_weight_products_are_the_coupled_multiplier :
    coupledMultiplier*firstWeight=0 ∧ lastWeightᵀ*lastWeight=coupledMultiplier := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [coupledMultiplier,firstWeight,lastWeight,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_coupled_source_certificate_is_the_printed_matrix (rho : ℝ) :
    fullCertificate rho coupledMultiplier=
      fun i j => coupledMatrix rho
        (finSumFinEquiv i : Fin 3) (finSumFinEquiv j : Fin 3) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => fin_cases i; fin_cases j; norm_num [fullCertificate,coupledMatrix,finSumFinEquiv]
    | inr j => fin_cases i; fin_cases j <;>
        norm_num [fullCertificate,coupledMatrix,firstWeight,lastWeight,coupledMultiplier,
          Matrix.mul_apply,Fin.sum_univ_succ,finSumFinEquiv]
  | inr i =>
    cases j with
    | inl j => fin_cases i <;> fin_cases j <;>
        norm_num [fullCertificate,coupledMatrix,firstWeight,lastWeight,coupledMultiplier,
          Matrix.mul_apply,Fin.sum_univ_succ,finSumFinEquiv]
    | inr j => fin_cases i <;> fin_cases j <;>
        norm_num [fullCertificate,coupledMatrix,firstWeight,lastWeight,coupledMultiplier,
          Matrix.mul_apply,Fin.sum_univ_succ,finSumFinEquiv]

theorem actual_coupled_matrix_quadratic (rho : ℝ) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (coupledMatrix rho *ᵥ v)= -rho*(v 0)^2-(v 1-v 2)^2 := by
  simp [coupledMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_coupled_matrix_is_negative_semidefinite_iff (rho : ℝ) :
    (-(coupledMatrix rho)).PosSemidef ↔ 0≤rho := by
  constructor
  · intro h
    have hv := h.dotProduct_mulVec_nonneg (![1,0,0] : Fin 3 → ℝ)
    norm_num [coupledMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hv
    exact hv
  · intro hr
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [coupledMatrix,Matrix.conjTranspose_apply]
    · intro v
      simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg]
      rw [actual_coupled_matrix_quadratic]
      have h := add_nonneg (mul_nonneg hr (sq_nonneg (v 0))) (sq_nonneg (v 1-v 2))
      linarith

theorem actual_eigenbasis_inverse : eigenBasis*inverseEigenBasis=1 ∧
    inverseEigenBasis*eigenBasis=1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [eigenBasis,inverseEigenBasis,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_coupled_matrix_diagonalisation (rho : ℝ) :
    inverseEigenBasis*coupledMatrix rho*eigenBasis=
      Matrix.diagonal (![-rho,-2,0] : Fin 3 → ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [inverseEigenBasis,eigenBasis,coupledMatrix,Matrix.mul_apply,Fin.sum_univ_succ]
    <;> ring

theorem actual_coupled_characteristic_polynomial_with_multiplicities (rho : ℝ) :
    (coupledMatrix rho).charpoly=
      (Polynomial.X+Polynomial.C rho)*(Polynomial.X+2)*Polynomial.X := by
  have h : (inverseEigenBasis*coupledMatrix rho*eigenBasis).charpoly=
      (coupledMatrix rho).charpoly := by
    rw [Matrix.charpoly_mul_comm,←Matrix.mul_assoc,actual_eigenbasis_inverse.1,Matrix.one_mul]
  rw [actual_coupled_matrix_diagonalisation,Matrix.charpoly_diagonal] at h
  simpa [Fin.prod_univ_succ,sub_neg_eq_add] using h.symm

theorem actual_coupled_eigenvalues (rho lambda : ℝ) :
    (coupledMatrix rho).charpoly.IsRoot lambda ↔
      lambda= -rho ∨ lambda= -2 ∨ lambda=0 := by
  rw [actual_coupled_characteristic_polynomial_with_multiplicities,Polynomial.IsRoot]
  simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_C,Polynomial.eval_ofNat,mul_eq_zero]
  constructor
  · rintro ((h|h)|h)
    · left; linarith
    · right; left; linarith
    · right; right; exact h
  · rintro (h|h|h)
    · left; left; linarith
    · left; right; linarith
    · right; exact h

theorem actual_diagonal_source_certificate_is_the_printed_matrix (rho t0 t1 : ℝ) :
    fullCertificate rho (Matrix.diagonal (![t0,t1] : Fin 2 → ℝ))=
      fun i j => diagonalMatrix rho t0 t1
        (finSumFinEquiv i : Fin 3) (finSumFinEquiv j : Fin 3) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => fin_cases i; fin_cases j; norm_num [fullCertificate,diagonalMatrix,finSumFinEquiv]
    | inr j => fin_cases i; fin_cases j <;>
        norm_num [fullCertificate,diagonalMatrix,firstWeight,lastWeight,
          Matrix.mul_apply,Fin.sum_univ_succ,finSumFinEquiv]
  | inr i =>
    cases j with
    | inl j => fin_cases i <;> fin_cases j <;>
        norm_num [fullCertificate,diagonalMatrix,firstWeight,lastWeight,
          Matrix.mul_apply,Fin.sum_univ_succ,finSumFinEquiv]
    | inr j => fin_cases i <;> fin_cases j <;>
        norm_num [fullCertificate,diagonalMatrix,firstWeight,lastWeight,
          Matrix.mul_apply,Fin.sum_univ_succ,finSumFinEquiv]

theorem actual_every_diagonal_certificate_requires_rho_at_least_one
    (rho t0 t1 : ℝ) (h : (-(diagonalMatrix rho t0 t1)).PosSemidef) : 1≤rho := by
  have hv := h.dotProduct_mulVec_nonneg (![1,-1,0] : Fin 3 → ℝ)
  norm_num [diagonalMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hv
  linarith

theorem actual_identity_diagonal_multiplier_gives_negative_all_ones :
    diagonalMatrix 1 1 1= -(1 : Fin 3 → Fin 3 → ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [diagonalMatrix]

theorem actual_identity_diagonal_multiplier_is_feasible :
    (-(diagonalMatrix 1 1 1)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [diagonalMatrix,Matrix.conjTranspose_apply]
  · intro v
    simp only [star_trivial]
    have he : v ⬝ᵥ ((-(diagonalMatrix 1 1 1)) *ᵥ v)=(v 0+v 1+v 2)^2 := by
      simp [diagonalMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      ring
    rw [he]; exact sq_nonneg _

theorem actual_diagonal_lipsdp_optimum_is_attained_and_least :
    IsLeast {rho : ℝ | ∃ t0 t1 : ℝ, 0≤t0 ∧ 0≤t1 ∧
      (-(diagonalMatrix rho t0 t1)).PosSemidef} 1 := by
  refine ⟨⟨1,1,by norm_num,by norm_num,actual_identity_diagonal_multiplier_is_feasible⟩,?_⟩
  rintro rho ⟨t0,t1,_,_,h⟩
  exact actual_every_diagonal_certificate_requires_rho_at_least_one rho t0 t1 h

theorem actual_all_independent_slope_patterns_have_attained_gain_one :
    IsGreatest {L : ℝ | ∃ d0 d1 : ℝ, d0∈Icc 0 1 ∧ d1∈Icc 0 1 ∧
      L=|d0-d1|} 1 := by
  constructor
  · exact ⟨1,0,by norm_num,by norm_num,by norm_num⟩
  · rintro _ ⟨d0,d1,hd0,hd1,rfl⟩
    apply abs_le.mpr
    constructor <;> linarith [hd0.1,hd0.2,hd1.1,hd1.2]

theorem actual_network_has_the_printed_first_derivative (x : ℝ) :
    HasDerivAt network (networkDerivative x) x := by
  have hp := ((actual_tanh_has_the_literal_strictly_positive_bounded_derivative (x+1)).1).comp x
    ((hasDerivAt_id x).add_const 1)
  have hm := ((actual_tanh_has_the_literal_strictly_positive_bounded_derivative (x-1)).1).comp x
    ((hasDerivAt_id x).sub_const 1)
  convert (hp.sub hm).sub_const (1/2) using 1 <;> simp [network,networkDerivative]

theorem actual_network_derivative_is_difference_of_sech_squares (x : ℝ) :
    networkDerivative x=1/(Real.cosh (x+1))^2-1/(Real.cosh (x-1))^2 := by
  simp [networkDerivative,actual_tanh_derivative_is_one_minus_square]

theorem actual_network_derivative_has_the_printed_second_derivative (x : ℝ) :
    HasDerivAt networkDerivative (networkSecondDerivative x) x := by
  have hp := ((actual_tanh_has_the_literal_strictly_positive_bounded_derivative (x+1)).1).comp x
    ((hasDerivAt_id x).add_const 1)
  have hm := ((actual_tanh_has_the_literal_strictly_positive_bounded_derivative (x-1)).1).comp x
    ((hasDerivAt_id x).sub_const 1)
  convert ((hasDerivAt_const x (1:ℝ)).sub (hp.pow 2)).sub
    ((hasDerivAt_const x (1:ℝ)).sub (hm.pow 2)) using 1
  · funext y; rfl
  · simp only [one_mul,zero_sub,networkSecondDerivative]
    ring

theorem actual_network_is_even_and_its_derivative_is_odd (x : ℝ) :
    network (-x)=network x ∧ networkDerivative (-x)= -networkDerivative x := by
  have hp : -x+1=-(x-1) := by ring
  have hm : -x-1=-(x+1) := by ring
  constructor <;> simp only [network,networkDerivative,hp,hm,Real.tanh_neg,neg_sq] <;> ring

theorem actual_derivative_magnitude_is_even (x : ℝ) :
    |networkDerivative x|=|networkDerivative |x|| := by
  by_cases hx : 0≤x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx),(actual_network_is_even_and_its_derivative_is_odd x).2,abs_neg]

theorem actual_network_is_not_constant : network 1<network 0 := by
  have hr := actual_tanh_one_rigorous_rational_enclosure
  have hu := Real.tanh_lt_one 2
  norm_num [network,Real.tanh_neg] at *
  linarith

theorem actual_zero_lipschitz_bound_is_false : ¬realLipschitzBound network 0 := by
  rintro ⟨_,h⟩
  have hc := h 1 0
  norm_num at hc
  have he := abs_eq_zero.mp (le_antisymm hc (abs_nonneg _))
  linarith [actual_network_is_not_constant]

theorem actual_arbitrarily_small_coupled_claim_does_imply_constancy
    (h : ∀ rho : ℝ, 0<rho → realLipschitzBound network (Real.sqrt rho)) :
    ∀ x y : ℝ, network x=network y := by
  intro x y
  have hh : ∀ eps : ℝ,0<eps → |network x-network y|≤eps*|x-y| := by
    intro eps he
    have h0 := (h (eps^2) (sq_pos_of_pos he)).2 x y
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos he] using h0
  by_cases hxy : x=y
  · simp [hxy]
  · have hp : 0<|x-y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    by_contra hn
    have hv : 0<|network x-network y| := abs_pos.mpr (sub_ne_zero.mpr hn)
    have hsmall := hh (|network x-network y|/(2*|x-y|)) (by positivity)
    have he : (|network x-network y|/(2*|x-y|))*|x-y|=|network x-network y|/2 := by
      field_simp [hp.ne']
      ring
    rw [he] at hsmall
    linarith

theorem actual_coupled_certificate_family_cannot_bound_the_network :
    (∀ rho : ℝ,0<rho → (-(coupledMatrix rho)).PosSemidef) ∧
      ¬∀ rho : ℝ,0<rho → realLipschitzBound network (Real.sqrt rho) := by
  constructor
  · intro rho hr; exact (actual_coupled_matrix_is_negative_semidefinite_iff rho).mpr hr.le
  · intro h
    have he := actual_arbitrarily_small_coupled_claim_does_imply_constancy h 1 0
    linarith [actual_network_is_not_constant]

def criticalPolynomial (k u : ℝ) : ℝ := 1-3*(1-k)*u-k*u^2
def derivativeProfile (r s : ℝ) : ℝ :=
  4*r*(1-r^2)*s*(1-s^2)/(1-r^2*s^2)^2

theorem actual_critical_polynomial_is_strictly_decreasing
    (k : ℝ) (hk0 : 0<k) (hk1 : k<1) : StrictAntiOn (criticalPolynomial k) (Ici 0) := by
  intro u hu v hv huv
  have he : criticalPolynomial k u-criticalPolynomial k v=
      (v-u)*(3*(1-k)+k*(u+v)) := by unfold criticalPolynomial; ring
  have hp : 0<(v-u)*(3*(1-k)+k*(u+v)) := by
    apply mul_pos (sub_pos.mpr huv)
    have hn := mul_nonneg hk0.le (add_nonneg hu hv)
    linarith
  linarith

theorem actual_critical_root_exists_uniquely
    (k : ℝ) (hk0 : 0<k) (hk1 : k<1) :
    ∃ u : ℝ,u∈Ioo 0 1 ∧ criticalPolynomial k u=0 ∧
      ∀ v : ℝ,0≤v → criticalPolynomial k v=0 → v=u := by
  have hc : ContinuousOn (criticalPolynomial k) (Icc 0 1) := by
    unfold criticalPolynomial
    fun_prop
  have h0 : criticalPolynomial k 0=1 := by simp [criticalPolynomial]
  have h1 : criticalPolynomial k 1<0 := by unfold criticalPolynomial; nlinarith
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ)≤1) hc
    (show (0:ℝ)∈Icc (criticalPolynomial k 1) (criticalPolynomial k 0) by rw [h0]; exact ⟨h1.le,by norm_num⟩)
  have hpos : 0<u := by
    by_contra hn
    have he0 : u=0 := le_antisymm (le_of_not_gt hn) hu.1
    subst u
    rw [h0] at he
    norm_num at he
  have hlt : u<1 := by
    by_contra hn
    have he1 : u=1 := le_antisymm hu.2 (le_of_not_gt hn)
    subst u
    linarith
  refine ⟨u,⟨hpos,hlt⟩,he,?_⟩
  intro v hv hev
  rcases lt_trichotomy v u with h|h|h
  · have hc := actual_critical_polynomial_is_strictly_decreasing k hk0 hk1 hv hpos.le h
    rw [he,hev] at hc
    linarith
  · exact h
  · have hc := actual_critical_polynomial_is_strictly_decreasing k hk0 hk1 hpos.le hv h
    rw [he,hev] at hc
    linarith

def criticalRoot (k : ℝ) : ℝ :=
  if h : 0<k ∧ k<1 then (actual_critical_root_exists_uniquely k h.1 h.2).choose else 0

theorem actual_chosen_critical_root_spec (k : ℝ) (hk0 : 0<k) (hk1 : k<1) :
    criticalRoot k∈Ioo 0 1 ∧ criticalPolynomial k (criticalRoot k)=0 := by
  simp only [criticalRoot,dif_pos ⟨hk0,hk1⟩]
  exact ⟨(actual_critical_root_exists_uniquely k hk0 hk1).choose_spec.1,
    (actual_critical_root_exists_uniquely k hk0 hk1).choose_spec.2.1⟩

theorem actual_profile_denominator_is_positive (r s : ℝ)
    (hr : 0<r ∧ r<1) (hs : s∈Icc 0 1) : 0<1-r^2*s^2 := by
  have hr2 : r^2<1 := by nlinarith
  have hs2 : s^2≤1 := by nlinarith [hs.1,hs.2]
  have hprod := mul_le_mul_of_nonneg_left hs2 (sq_nonneg r)
  nlinarith

theorem actual_profile_derivative (r s : ℝ) (hd : 1-r^2*s^2≠0) :
    HasDerivAt (derivativeProfile r)
      (4*r*(1-r^2)*criticalPolynomial (r^2) (s^2)/(1-r^2*s^2)^3) s := by
  have hn := (((hasDerivAt_id s).mul ((hasDerivAt_const s (1:ℝ)).sub ((hasDerivAt_id s).pow 2))).const_mul (4*r*(1-r^2)))
  have hden := ((hasDerivAt_const s (1:ℝ)).sub (((hasDerivAt_id s).pow 2).const_mul (r^2))).pow 2
  convert hn.div hden (pow_ne_zero 2 hd) using 1
  · funext y; simp [derivativeProfile,mul_assoc]
  · simp only [id_eq,one_mul,zero_sub,criticalPolynomial]
    field_simp [hd]
    ring

theorem actual_profile_global_maximum_on_the_complete_slope_interval
    (r : ℝ) (hr : 0<r ∧ r<1) :
    ∀ s : ℝ,s∈Icc 0 1 →
      derivativeProfile r s≤derivativeProfile r (Real.sqrt (criticalRoot (r^2))) := by
  have hk0 : 0<r^2 := sq_pos_of_pos hr.1
  have hk1 : r^2<1 := by nlinarith [hr.1,hr.2]
  have hu := actual_chosen_critical_root_spec (r^2) hk0 hk1
  let a := Real.sqrt (criticalRoot (r^2))
  have ha0 : 0<a := Real.sqrt_pos.2 hu.1.1
  have ha1 : a<1 := (Real.sqrt_lt (by norm_num : (0:ℝ)≤1)).2 (by simpa using hu.1.2)
  have ha2 : a^2=criticalRoot (r^2) := Real.sq_sqrt hu.1.1.le
  have hcontinuous : ContinuousOn (derivativeProfile r) (Icc 0 1) := by
    intro s hs
    exact (actual_profile_derivative r s (ne_of_gt (actual_profile_denominator_is_positive r s hr hs))).continuousAt.continuousWithinAt
  have hleft : MonotoneOn (derivativeProfile r) (Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact hcontinuous.mono (fun s hs=>⟨hs.1,le_trans hs.2 ha1.le⟩)
    · intro s hs
      have hs' : s∈Icc 0 1 := by
        rw [interior_Icc] at hs
        exact ⟨hs.1.le,le_trans hs.2.le ha1.le⟩
      exact (actual_profile_derivative r s (ne_of_gt (actual_profile_denominator_is_positive r s hr hs'))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hd := actual_profile_denominator_is_positive r s hr ⟨hs.1.le,le_trans hs.2.le ha1.le⟩
      rw [(actual_profile_derivative r s (ne_of_gt hd)).deriv]
      have hs2 : s^2≤criticalRoot (r^2) := by nlinarith [hs.1,hs.2,ha2]
      have hp : 0≤criticalPolynomial (r^2) (s^2) := by
        by_cases he : s^2=criticalRoot (r^2)
        · rw [he,hu.2]
        · have h := actual_critical_polynomial_is_strictly_decreasing (r^2) hk0 hk1
            (sq_nonneg s) hu.1.1.le (lt_of_le_of_ne hs2 he)
          rw [hu.2] at h
          exact h.le
      positivity
  have hright : AntitoneOn (derivativeProfile r) (Icc a 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact hcontinuous.mono (fun s hs=>⟨le_trans ha0.le hs.1,hs.2⟩)
    · intro s hs
      have hs' : s∈Icc 0 1 := by
        rw [interior_Icc] at hs
        exact ⟨le_trans ha0.le hs.1.le,hs.2.le⟩
      exact (actual_profile_derivative r s (ne_of_gt (actual_profile_denominator_is_positive r s hr hs'))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hd := actual_profile_denominator_is_positive r s hr ⟨le_trans ha0.le hs.1.le,hs.2.le⟩
      rw [(actual_profile_derivative r s (ne_of_gt hd)).deriv]
      have hs2 : criticalRoot (r^2)≤s^2 := by nlinarith [hs.1,hs.2,ha2]
      have hp : criticalPolynomial (r^2) (s^2)≤0 := by
        by_cases he : criticalRoot (r^2)=s^2
        · rw [←he,hu.2]
        · have h := actual_critical_polynomial_is_strictly_decreasing (r^2) hk0 hk1
            hu.1.1.le (sq_nonneg s) (lt_of_le_of_ne hs2 he)
          rw [hu.2] at h
          exact h.le
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hp
      · positivity
  intro s hs
  change derivativeProfile r s≤derivativeProfile r a
  rcases le_total s a with h|h
  · exact hleft ⟨hs.1,h⟩ ⟨ha0.le,le_rfl⟩ h
  · exact hright ⟨le_rfl,ha1.le⟩ ⟨h,hs.2⟩ h


theorem actual_tanh_addition_denominator_is_positive (x y : ℝ) :
    0<1+Real.tanh x*Real.tanh y := by
  have hx := Real.abs_tanh_lt_one x
  have hy := Real.abs_tanh_lt_one y
  have hm : |Real.tanh x|*|Real.tanh y|<1 := by
    nlinarith [abs_nonneg (Real.tanh x),abs_nonneg (Real.tanh y)]
  rw [←abs_mul] at hm
  linarith [(abs_lt.mp hm).1]

theorem actual_tanh_addition_ratio (x y : ℝ) :
    Real.tanh (x+y)=(Real.tanh x+Real.tanh y)/(1+Real.tanh x*Real.tanh y) := by
  have hcross : (1+Real.tanh x*Real.tanh y)*Real.tanh (x+y)=
      Real.tanh x+Real.tanh y := by
    rw [actual_tanh_is_the_exponential_square_ratio,
      actual_tanh_is_the_exponential_square_ratio,
      actual_tanh_is_the_exponential_square_ratio,Real.exp_add]
    have hx : (Real.exp x)^2+1≠0 := by positivity
    have hy : (Real.exp y)^2+1≠0 := by positivity
    have hxy : (Real.exp x*Real.exp y)^2+1≠0 := by positivity
    field_simp
    ring
  apply (eq_div_iff (ne_of_gt (actual_tanh_addition_denominator_is_positive x y))).mpr
  simpa [mul_comm] using hcross

theorem actual_network_derivative_is_the_full_profile (x : ℝ) :
    networkDerivative x= -derivativeProfile (Real.tanh 1) (Real.tanh x) := by
  have hp := actual_tanh_addition_ratio x 1
  have hm := actual_tanh_addition_ratio x (-1)
  have hdp := actual_tanh_addition_denominator_is_positive x 1
  have hdm := actual_tanh_addition_denominator_is_positive x (-1)
  simp only [Real.tanh_neg] at hm hdm
  have hd : 1-(Real.tanh 1)^2*(Real.tanh x)^2≠0 := by
    have he : 1-(Real.tanh 1)^2*(Real.tanh x)^2=
        (1+Real.tanh x*Real.tanh 1)*(1-Real.tanh x*Real.tanh 1) := by ring
    rw [he]
    exact mul_ne_zero (ne_of_gt hdp) (ne_of_gt (by simpa using hdm))
  unfold networkDerivative derivativeProfile
  rw [hp,show x-1=x+(-1) by ring,hm]
  field_simp [hd,ne_of_gt hdp,ne_of_gt (by simpa using hdm)]
  ring

theorem actual_tanh_one_is_strictly_between_zero_and_one :
    0<Real.tanh 1 ∧ Real.tanh 1<1 := by
  have h := actual_tanh_one_rigorous_rational_enclosure
  constructor <;> linarith

theorem actual_profile_is_nonnegative_on_the_slope_interval (r s : ℝ)
    (hr : 0<r ∧ r<1) (hs : s∈Icc 0 1) : 0≤derivativeProfile r s := by
  have hr2 : r^2<1 := by nlinarith [hr.1,hr.2]
  have hs2 : s^2≤1 := by nlinarith [hs.1,hs.2]
  unfold derivativeProfile
  positivity

theorem actual_network_derivative_magnitude_is_the_profile (x : ℝ) :
    |networkDerivative x|=derivativeProfile (Real.tanh 1) (Real.tanh |x|) := by
  rw [actual_derivative_magnitude_is_even,actual_network_derivative_is_the_full_profile,abs_neg]
  have hs : Real.tanh |x|∈Icc 0 1 := by
    constructor
    · simpa using tanh_monotone (abs_nonneg x)
    · exact (Real.tanh_lt_one _).le
  exact abs_of_nonneg (actual_profile_is_nonnegative_on_the_slope_interval _ _
    actual_tanh_one_is_strictly_between_zero_and_one hs)

def attainedSlope : ℝ := Real.sqrt (criticalRoot ((Real.tanh 1)^2))
def attainedInput : ℝ := Real.artanh attainedSlope
def exactLipschitz : ℝ := derivativeProfile (Real.tanh 1) attainedSlope

theorem actual_attaining_slope_input_and_positive_gain :
    attainedSlope∈Ioo 0 1 ∧ 0<attainedInput ∧
      Real.tanh attainedInput=attainedSlope ∧ 0<exactLipschitz := by
  have hr := actual_tanh_one_is_strictly_between_zero_and_one
  have hk0 : 0<(Real.tanh 1)^2 := sq_pos_of_pos hr.1
  have hk1 : (Real.tanh 1)^2<1 := by nlinarith [hr.1,hr.2]
  have hu := actual_chosen_critical_root_spec ((Real.tanh 1)^2) hk0 hk1
  have hs : attainedSlope∈Ioo 0 1 := by
    constructor
    · exact Real.sqrt_pos.2 hu.1.1
    · exact (Real.sqrt_lt (by norm_num : (0:ℝ)≤1)).2 (by simpa using hu.1.2)
  refine ⟨hs,Real.artanh_pos hs,Real.tanh_artanh ⟨by linarith [hs.1],hs.2⟩,?_⟩
  have hr2 : 0<1-(Real.tanh 1)^2 := by nlinarith [hr.1,hr.2]
  have hs2 : 0<1-attainedSlope^2 := by nlinarith [hs.1,hs.2]
  have hd := actual_profile_denominator_is_positive _ _ hr ⟨hs.1.le,hs.2.le⟩
  unfold exactLipschitz derivativeProfile
  positivity

theorem actual_global_derivative_maximum_is_attained_at_both_inputs :
    |networkDerivative attainedInput|=exactLipschitz ∧
      |networkDerivative (-attainedInput)|=exactLipschitz ∧
      ∀ x : ℝ,|networkDerivative x|≤exactLipschitz := by
  have hs := actual_attaining_slope_input_and_positive_gain
  have he : |networkDerivative attainedInput|=exactLipschitz := by
    rw [actual_network_derivative_magnitude_is_the_profile,abs_of_pos hs.2.1,hs.2.2.1]
    rfl
  refine ⟨he,?_,?_⟩
  · rw [(actual_network_is_even_and_its_derivative_is_odd attainedInput).2,abs_neg,he]
  · intro x
    rw [actual_network_derivative_magnitude_is_the_profile]
    apply actual_profile_global_maximum_on_the_complete_slope_interval _
      actual_tanh_one_is_strictly_between_zero_and_one
    constructor
    · simpa using tanh_monotone (abs_nonneg x)
    · exact (Real.tanh_lt_one _).le

theorem actual_real_network_lipschitz_bound_iff_derivative_bound (L : ℝ) :
    realLipschitzBound network L ↔ 0≤L ∧ ∀ x : ℝ,|networkDerivative x|≤L := by
  constructor
  · rintro ⟨hL,h⟩
    refine ⟨hL,fun x=>?_⟩
    have hd := norm_deriv_le_of_lip' hL
      (Filter.Eventually.of_forall (fun y=>show ‖network y-network x‖≤L*‖y-x‖ by
        simpa only [Real.norm_eq_abs] using h y x))
    simpa only [(actual_network_has_the_printed_first_derivative x).deriv,Real.norm_eq_abs] using hd
  · rintro ⟨hL,h⟩
    refine ⟨hL,fun x y=>?_⟩
    have he := norm_image_sub_le_of_norm_deriv_le
      (s:=Set.univ) (f:=network) (C:=L)
      (fun z _=>(actual_network_has_the_printed_first_derivative z).differentiableAt)
      (fun z _=>by simpa only [(actual_network_has_the_printed_first_derivative z).deriv,Real.norm_eq_abs] using h z)
      convex_univ (show y∈(Set.univ : Set ℝ) from trivial)
      (show x∈(Set.univ : Set ℝ) from trivial)
    simpa only [Real.norm_eq_abs] using he

theorem actual_exact_network_lipschitz_constant_is_least_and_attained :
    IsLeast {L : ℝ | realLipschitzBound network L} exactLipschitz := by
  refine ⟨(actual_real_network_lipschitz_bound_iff_derivative_bound _).mpr
    ⟨actual_attaining_slope_input_and_positive_gain.2.2.2.le,
      actual_global_derivative_maximum_is_attained_at_both_inputs.2.2⟩,?_⟩
  intro L hL
  have h := ((actual_real_network_lipschitz_bound_iff_derivative_bound L).mp hL).2 attainedInput
  rwa [actual_global_derivative_maximum_is_attained_at_both_inputs.1] at h

theorem actual_attaining_input_is_a_zero_of_the_printed_second_derivative :
    networkSecondDerivative attainedInput=0 := by
  have hs := actual_attaining_slope_input_and_positive_gain
  have hr := actual_tanh_one_is_strictly_between_zero_and_one
  have hu := actual_chosen_critical_root_spec ((Real.tanh 1)^2)
    (sq_pos_of_pos hr.1) (by nlinarith [hr.1,hr.2])
  have hs2 : attainedSlope^2=criticalRoot ((Real.tanh 1)^2) := Real.sq_sqrt hu.1.1.le
  have hd := actual_profile_denominator_is_positive _ _ hr ⟨hs.1.1.le,hs.1.2.le⟩
  have hp := (actual_profile_derivative (Real.tanh 1) attainedSlope (ne_of_gt hd)).neg
  rw [hs2,hu.2] at hp
  simp only [mul_zero,zero_div,neg_zero] at hp
  have ht := (actual_tanh_has_the_literal_strictly_positive_bounded_derivative attainedInput).1
  have hc := hp.comp attainedInput ht
  rw [hs.2.2.1] at hc
  have hz : HasDerivAt networkDerivative 0 attainedInput := by
    convert hc using 1
    · funext x; exact actual_network_derivative_is_the_full_profile x
    · ring
  exact (actual_network_derivative_has_the_printed_second_derivative attainedInput).unique hz

theorem actual_derivative_magnitude_tends_to_zero_at_infinite_absolute_input :
    Tendsto (fun x : ℝ=>|networkDerivative x|)
      (comap (abs : ℝ→ℝ) atTop) (nhds 0) := by
  have hplus : Tendsto (fun x : ℝ=>x+1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b-1)] with x hx
    linarith
  have hminus : Tendsto (fun x : ℝ=>x-1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b+1)] with x hx
    linarith
  have hp := CompleteModulesTanhAsymptotic.actual_tanh_derivative_tends_to_zero_at_positive_infinity.comp hplus
  have hm := CompleteModulesTanhAsymptotic.actual_tanh_derivative_tends_to_zero_at_positive_infinity.comp hminus
  have he : Tendsto networkDerivative atTop (nhds 0) := by
    convert hp.sub hm using 1
    · funext x
      simp only [Function.comp_apply,(tanh_derivative (x+1)).deriv,
        (tanh_derivative (x-1)).deriv,actual_network_derivative_is_difference_of_sech_squares]
    · norm_num
  have hh := he.abs.comp (tendsto_comap : Tendsto (abs : ℝ→ℝ) (comap abs atTop) atTop)
  convert hh using 1
  · funext x; exact actual_derivative_magnitude_is_even x
  · simp

theorem actual_tanh_one_square_rigorous_enclosure :
    (0.5800256582:ℝ)<(Real.tanh 1)^2 ∧ (Real.tanh 1)^2<0.5800256587 := by
  have hr := actual_tanh_one_rigorous_rational_enclosure
  constructor <;> nlinarith [hr.1,hr.2]

theorem actual_unique_critical_root_rigorous_enclosure :
    (0.617919996:ℝ)<criticalRoot ((Real.tanh 1)^2) ∧
      criticalRoot ((Real.tanh 1)^2)<0.617919998 := by
  have hr := actual_tanh_one_is_strictly_between_zero_and_one
  have hk := actual_tanh_one_square_rigorous_enclosure
  have hk0 : 0<(Real.tanh 1)^2 := sq_pos_of_pos hr.1
  have hk1 : (Real.tanh 1)^2<1 := by nlinarith [hr.1,hr.2]
  have hu := actual_chosen_critical_root_spec ((Real.tanh 1)^2) hk0 hk1
  have hmono := (actual_critical_polynomial_is_strictly_decreasing _ hk0 hk1).antitoneOn
  have hlo : 0<criticalPolynomial ((Real.tanh 1)^2) 0.617919996 := by
    unfold criticalPolynomial
    nlinarith [hk.1,hk.2]
  have hhi : criticalPolynomial ((Real.tanh 1)^2) 0.617919998<0 := by
    unfold criticalPolynomial
    nlinarith [hk.1,hk.2]
  constructor
  · by_contra h
    have he := hmono hu.1.1.le (by norm_num : (0:ℝ)≤0.617919996) (le_of_not_gt h)
    rw [hu.2] at he
    linarith
  · by_contra h
    have he := hmono (by norm_num : (0:ℝ)≤0.617919998) hu.1.1.le (le_of_not_gt h)
    rw [hu.2] at he
    linarith

theorem actual_attaining_slope_rigorous_enclosure :
    (0.786078873:ℝ)<attainedSlope ∧ attainedSlope<0.786078876 := by
  have hu := actual_unique_critical_root_rigorous_enclosure
  have hu0 : 0≤criticalRoot ((Real.tanh 1)^2) := by linarith [hu.1]
  have he : attainedSlope^2=criticalRoot ((Real.tanh 1)^2) := Real.sq_sqrt hu0
  have hs : 0≤attainedSlope := Real.sqrt_nonneg _
  constructor <;> nlinarith [hu.1,hu.2]

end SafeLearning.CompleteModulesCoupledTanhCounterexample30
