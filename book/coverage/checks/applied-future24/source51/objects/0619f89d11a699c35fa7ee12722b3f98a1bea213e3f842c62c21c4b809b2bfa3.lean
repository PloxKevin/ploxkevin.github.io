import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsAlgorithms

theorem scaling_iteration (q x₀ : ℝ) (n : ℕ) :
    (fun x : ℝ => q*x)^[n] x₀=q^n*x₀ := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih,pow_succ]; ring

theorem scaling_converges_iff (q x₀ : ℝ) (hx : x₀≠0) :
    Tendsto (fun n => (fun x : ℝ => q*x)^[n] x₀) atTop (𝓝 0) ↔ |q|<1 := by
  simp only [scaling_iteration]
  constructor
  · intro h
    have hh := h.mul_const x₀⁻¹
    have heq : (fun n : ℕ => q^n*x₀*x₀⁻¹)=(fun n => q^n) := by
      ext n; field_simp
    rw [heq,zero_mul] at hh
    exact tendsto_pow_atTop_nhds_zero_iff.mp hh
  · intro h
    simpa using (tendsto_pow_atTop_nhds_zero_iff.mpr h).mul_const x₀

theorem scalar_gradient_converges_iff (eta x₀ : ℝ) (hx : x₀≠0) :
    Tendsto (fun n => (fun x : ℝ => x-eta*(4*x))^[n] x₀) atTop (𝓝 0) ↔
      0<eta ∧ eta<1/2 := by
  have heq : (fun x : ℝ => x-eta*(4*x))=(fun x => (1-4*eta)*x) := by ext x; ring
  rw [heq,scaling_converges_iff _ _ hx]
  exact SafeLearning.PrimersFoundations.gradient_step_threshold eta

theorem scalar_gradient_objective_decreases (eta x : ℝ)
    (h₀ : 0<eta) (h₁ : eta<1/2) :
    2*(x-eta*(4*x))^2 ≤ 2*x^2 := by
  have ha := SafeLearning.PrimersFoundations.gradient_step_threshold eta |>.mpr ⟨h₀,h₁⟩
  have hs : (1-4*eta)^2≤1 := by
    have hh := abs_lt.mp ha
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg x)
  nlinarith

theorem expanding_scaling_norm (q x₀ : ℝ) (hq : 1 < |q|) (hx : x₀≠0) :
    Tendsto (fun n => |(fun x : ℝ => q*x)^[n] x₀|) atTop atTop := by
  simp only [scaling_iteration,abs_mul,abs_pow]
  exact (tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const (abs_pos.mpr hx)

def diagonalStep (eta : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ((1-eta)*x.1,(1-10*eta)*x.2)

def diagonalObjective (x : ℝ × ℝ) : ℝ := (x.1^2+10*x.2^2)/2

theorem diagonal_iteration (eta : ℝ) (x₀ : ℝ × ℝ) (n : ℕ) :
    (diagonalStep eta)^[n] x₀=((1-eta)^n*x₀.1,(1-10*eta)^n*x₀.2) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih]; simp only [diagonalStep,pow_succ]; congr 1 <;> ring

theorem slow_coordinate_objective (n : ℕ) (hn : 1≤n) :
    diagonalObjective ((diagonalStep (1/10))^[n] (10,1))=50*(81/100 : ℝ)^n := by
  rw [diagonal_iteration]
  have hn₀ : n≠0 := by omega
  norm_num [diagonalObjective,zero_pow hn₀]
  rw [mul_pow,← pow_mul,Nat.mul_comm n 2,pow_mul]
  norm_num
  ring

theorem balanced_step_objective (n : ℕ) :
    diagonalObjective ((diagonalStep (2/11))^[n] (10,1))=55*(81/121 : ℝ)^n := by
  rw [diagonal_iteration]
  norm_num [diagonalObjective]
  rw [mul_pow,← pow_mul,← pow_mul]
  rw [Nat.mul_comm n 2,pow_mul,pow_mul]
  norm_num
  ring

theorem slow_coordinate_minimal_budget (n : ℕ) :
    diagonalObjective ((diagonalStep (1/10))^[n] (10,1))≤1/1000000 ↔ 85≤n := by
  by_cases hn : n=0
  · subst n; norm_num [diagonalObjective]
  rw [slow_coordinate_objective n (by omega)]
  have hmono : Antitone (fun k : ℕ => (81/100 : ℝ)^k) :=
    pow_right_anti₀ (by norm_num) (by norm_num)
  have hb := SafeLearning.PrimersFoundations.legacy_gradient_thresholds
  constructor
  · intro h; by_contra hnot
    have hh := hmono (show n≤84 by omega)
    nlinarith [hb.1]
  · intro h; have hh := hmono h
    nlinarith [hb.2.1]

theorem balanced_step_minimal_budget (n : ℕ) :
    diagonalObjective ((diagonalStep (2/11))^[n] (10,1))≤1/1000000 ↔ 45≤n := by
  rw [balanced_step_objective]
  have hmono : Antitone (fun k : ℕ => (81/121 : ℝ)^k) :=
    pow_right_anti₀ (by norm_num) (by norm_num)
  have hb := SafeLearning.PrimersFoundations.legacy_gradient_thresholds
  constructor
  · intro h; by_contra hnot
    have hh := hmono (show n≤44 by omega)
    nlinarith [hb.2.2.1]
  · intro h; have hh := hmono h
    nlinarith [hb.2.2.2]

def diagonalContraction (eta : ℝ) : ℝ := max |1-eta| |1-10*eta|

theorem best_constant_diagonal_step (eta : ℝ) :
    9/11≤diagonalContraction eta ∧
      (diagonalContraction eta=9/11 ↔ eta=2/11) := by
  have h₁ := (le_abs_self (1-eta)).trans (le_max_left |1-eta| |1-10*eta|)
  have h₂ := (neg_le_abs (1-10*eta)).trans (le_max_right |1-eta| |1-10*eta|)
  change 1-eta≤diagonalContraction eta at h₁
  change -(1-10*eta)≤diagonalContraction eta at h₂
  constructor
  · linarith
  · constructor
    · intro heq; rw [heq] at h₁ h₂; linarith
    · rintro rfl; norm_num [diagonalContraction]

theorem diagonal_newton_one_step :
    (10 : ℝ)-(10/1)=0 ∧ (1 : ℝ)-(10/10)=0 ∧
      diagonalObjective (0,0)=0 := by norm_num [diagonalObjective]

theorem diagonal_gradient_and_hessian (x y : ℝ) :
    HasDerivAt (fun z : ℝ => diagonalObjective (z,y)) x x ∧
    HasDerivAt (fun z : ℝ => diagonalObjective (x,z)) (10*y) y ∧
    HasDerivAt (fun z : ℝ => z) 1 x ∧
    HasDerivAt (fun z : ℝ => 10*z) 10 y := by
  refine ⟨?_,?_,hasDerivAt_id x,?_⟩
  · convert (((hasDerivAt_id x).pow 2).add_const (10*y^2)).div_const 2 using 1 <;>
      simp [diagonalObjective,id_eq] <;> ring
  · convert ((hasDerivAt_const y (x^2)).add (((hasDerivAt_id y).pow 2).const_mul 10)).div_const 2 using 1 <;>
      simp [diagonalObjective,id_eq] <;> ring
  · simpa using (hasDerivAt_id y).const_mul 10

theorem newton_diagonal_independent_of_conditioning (a b x y : ℝ)
    (ha : a≠0) (hb : b≠0) :
    x-(a*x)/a=0 ∧ y-(b*y)/b=0 := by
  constructor <;> field_simp <;> ring

theorem unstable_diagonal_coordinate :
    Tendsto (fun n => |((diagonalStep (21/100))^[n] (10,1)).2|) atTop atTop := by
  have h := expanding_scaling_norm (-(11/10 : ℝ)) 1 (by norm_num) (by norm_num)
  simp only [scaling_iteration,diagonal_iteration] at *
  norm_num at *
  exact h

end SafeLearning.CompleteFoundationsAlgorithms
