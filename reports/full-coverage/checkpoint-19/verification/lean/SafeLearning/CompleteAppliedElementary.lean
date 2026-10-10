import Mathlib
import SafeLearning.PrimersApplied
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedElementary
open Filter
open scoped Topology

theorem d_ready_derivative (t : ℝ) :
    HasDerivAt (fun s : ℝ => 3*Real.exp (-2*s)) (-2*(3*Real.exp (-2*t))) t := by
  convert (((hasDerivAt_id t).const_mul (-2)).exp.const_mul 3) using 1 <;>
    (try ext s) <;> simp only [id_eq] <;> ring

theorem d_ready_quadratic_sandwich (x y : ℝ) :
    x^2+y^2≤x^2+2*y^2 ∧ x^2+2*y^2≤2*(x^2+y^2) := by
  constructor <;> nlinarith [sq_nonneg x,sq_nonneg y]

theorem outer_product_psd (x y : ℝ) :
    0≤x^2+4*x*y+4*y^2 := by nlinarith [sq_nonneg (x+2*y)]

theorem outer_product_not_pd : (-2:ℝ)≠0 ∧ (-2:ℝ)^2+4*(-2)*1+4*1^2=0 := by norm_num

theorem nonlinear_equilibria (x : ℝ) : -x+x^2=0 ↔ x=0 ∨ x=1 := by
  constructor
  · intro h
    have hh : x*(x-1)=0 := by nlinarith
    rcases mul_eq_zero.mp hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

theorem feedback_quarter_closed_form (x : ℕ → ℝ)
    (hstep : ∀ n, x (n+1)=(1/2)*x n-(1/4)*x n) :
    ∀ n, x n=(1/4:ℝ)^n*x 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [hstep n,ih]; ring

theorem feedback_quarter_converges (x0 : ℝ) :
    Tendsto (fun n : ℕ => (1/4:ℝ)^n*x0) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)).mul_const x0

theorem discount_infinite_sum : (∑' n : ℕ, (2:ℝ)*(1/2)^n)=4 := by
  rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)]
  norm_num

theorem discount_partial_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, (2:ℝ)*(1/2)^n)=4*(1-(1/2)^N) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih]; ring

theorem discount_partial_sum_limit :
    Tendsto (fun N : ℕ => 4*(1-(1/2:ℝ)^N)) atTop (𝓝 4) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub h).const_mul 4

theorem undiscounted_diverges :
    Tendsto (fun N : ℕ => ∑ _n ∈ Finset.range N, (2:ℝ)) atTop atTop := by
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (by norm_num)

theorem parameter_derivative (theta x : ℝ) :
    HasDerivAt (fun p : ℝ => p*x) x theta := by simpa using (hasDerivAt_id theta).mul_const x

theorem input_derivative (theta x : ℝ) :
    HasDerivAt (fun z : ℝ => theta*z) theta x := by simpa using (hasDerivAt_id x).const_mul theta

theorem one_state_constraint (p : ℝ) :
    5*p≤2 ↔ p≤2/5 := by constructor <;> intro h <;> linarith

theorem one_state_optimum (p : ℝ) (hc : 5*p≤2) : 10*p≤4 := by linarith

theorem one_state_occupancy (p : ℝ) :
    (1-4/5:ℝ)*(∑' n : ℕ, (4/5:ℝ)^n*p)=p := by
  rw [tsum_mul_right,tsum_geometric_of_abs_lt_one (by norm_num : |(4/5:ℝ)|<1)]
  ring

theorem reward_sigmoid_derivative (theta : ℝ) :
    HasDerivAt (fun p : ℝ => 4*Real.sigmoid p)
      (4*Real.sigmoid theta*(1-Real.sigmoid theta)) theta := by
  convert (Real.hasDerivAt_sigmoid theta).const_mul 4 using 1 <;> ring

theorem score_log_sigmoid (theta : ℝ) :
    HasDerivAt (fun p : ℝ => Real.log (Real.sigmoid p)) (1-Real.sigmoid theta) theta := by
  have hp : Real.sigmoid theta≠0 := (Real.sigmoid_pos theta).ne'
  convert (Real.hasDerivAt_sigmoid theta).log hp using 1
  field_simp

theorem two_logits_stay (a b c : ℝ) (ha : |a-3|≤2/5)
    (hb : |b-1|≤2/5) (hc : |c|≤2/5) :
    (6/5:ℝ)≤a-b ∧ (11/5:ℝ)≤a-c ∧ b<a ∧ c<a := by
  have h1 := abs_le.mp ha
  have h2 := abs_le.mp hb
  have h3 := abs_le.mp hc
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem binary_affine_robust (delta : ℝ) (hd : |delta|<3/2) :
    0<2*(1+delta)+1 := by
  have hh := abs_lt.mp hd
  linarith

theorem binary_affine_boundary :
    (2:ℝ)*(-1/2)+1=0 ∧ |(-1/2:ℝ)-1|=3/2 ∧
    2*(1+(-3/2:ℝ))+1=0 := by norm_num

def IsLipschitzBound (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ x y, |f x-f y|≤L*|x-y|

theorem scalar_exact_lipschitz (a b L : ℝ) :
    IsLipschitzBound (fun x => a*x+b) L ↔ |a|≤L := by
  constructor
  · intro h
    have hh := h 1 0
    simpa using hh
  · intro h x y
    have he : a*x+b-(a*y+b)=a*(x-y) := by ring
    rw [he,abs_mul]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

theorem residual_scalar_constants :
    IsLipschitzBound (fun x : ℝ => x+(1/5)*x) (6/5) ∧
    IsLipschitzBound (fun x : ℝ => x-(4/5)*x) (1/5) ∧
    ¬ IsLipschitzBound (fun x : ℝ => x-(4/5)*x) 0 := by
  have h1 : (fun x : ℝ => x+(1/5)*x)=(fun x : ℝ => (6/5)*x+0) := by ext x; ring
  have h2 : (fun x : ℝ => x-(4/5)*x)=(fun x : ℝ => (1/5)*x+0) := by ext x; ring
  rw [h1,h2,scalar_exact_lipschitz,scalar_exact_lipschitz,scalar_exact_lipschitz]
  norm_num

theorem relu_pair_exact_lipschitz (L : ℝ) :
    IsLipschitzBound (fun x : ℝ => max 0 x-max 0 (-x)) L ↔ 1≤L := by
  simp_rw [SafeLearning.PrimersApplied.relu_identity]
  simpa using scalar_exact_lipschitz 1 0 L

theorem one_step_unique_minimizer (x u : ℝ) :
    u^2+(x+u)^2=x^2/2 ↔ u=-x/2 := by
  rw [SafeLearning.PrimersApplied.one_step_quadratic_minimizer]
  constructor
  · intro h
    have hh : (u+x/2)^2=0 := by linarith
    have hz := sq_eq_zero_iff.mp hh
    linarith
  · intro h
    rw [h]
    ring

theorem one_step_derivative (x u : ℝ) :
    HasDerivAt (fun v : ℝ => v^2+(x+v)^2) (4*u+2*x) u := by
  convert ((hasDerivAt_id u).pow 2).add
    (((hasDerivAt_const u x).add (hasDerivAt_id u)).pow 2) using 1 <;>
      (try ext t) <;> simp only [Pi.add_apply,Pi.pow_apply,id_eq] <;> ring

theorem mpc_two_step_unique (u v : ℝ) :
    u^2+v^2+(3+u+v)^2=3 ↔ u=-1 ∧ v=-1 := by
  have he : u^2+v^2+(3+u+v)^2=3+(u+1)^2+(v+1)^2+(u+v+2)^2 := by ring
  rw [he]
  constructor
  · intro h
    have hu : (u+1)^2=0 := by nlinarith [sq_nonneg (v+1),sq_nonneg (u+v+2)]
    have hv : (v+1)^2=0 := by nlinarith [sq_nonneg (u+1),sq_nonneg (u+v+2)]
    have hu' := sq_eq_zero_iff.mp hu
    have hv' := sq_eq_zero_iff.mp hv
    constructor <;> linarith
  · rintro ⟨rfl,rfl⟩
    norm_num

end SafeLearning.CompleteAppliedElementary
