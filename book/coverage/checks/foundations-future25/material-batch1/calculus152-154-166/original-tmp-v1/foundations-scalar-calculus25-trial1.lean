import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsScalarCalculusMaterial25

theorem actual_arbitrary_real_weighted_sum_derivative
    (f g : ℝ→ℝ) (a b x df dg : ℝ)
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg x) :
    HasDerivAt (fun t=>a*f t+b*g t) (a*df+b*dg) x := by
  exact (hf.const_mul a).add (hg.const_mul b)

theorem actual_arbitrary_real_product_derivative
    (f g : ℝ→ℝ) (x df dg : ℝ)
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg x) :
    HasDerivAt (fun t=>f t*g t) (df*g x+f x*dg) x := by
  exact hf.mul hg

theorem actual_arbitrary_real_composition_derivative
    (f g : ℝ→ℝ) (x df dg : ℝ)
    (hf : HasDerivAt f df (g x)) (hg : HasDerivAt g dg x) :
    HasDerivAt (fun t=>f (g t)) (df*dg) x := by
  exact hf.comp x hg

theorem actual_literal_square_exp_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ=>t^2*Real.exp t)
      (2*x*Real.exp x+x^2*Real.exp x) x := by
  convert ((hasDerivAt_id x).pow 2).mul (Real.hasDerivAt_exp x) using 1 <;> simp

theorem actual_literal_square_exp_derivative_at_one :
    deriv (fun t : ℝ=>t^2*Real.exp t) 1=3*Real.exp 1 := by
  rw [(actual_literal_square_exp_derivative 1).deriv]
  ring

theorem actual_literal_affine_inner_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ=>2*t+1) 2 x := by
  simpa using ((hasDerivAt_id x).const_mul 2).add_const 1

theorem actual_literal_affine_square_outer_inner_and_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ=>t^2) (2*(2*x+1)) (2*x+1) ∧
    HasDerivAt (fun t : ℝ=>2*t+1) 2 x ∧
    HasDerivAt (fun t : ℝ=>(2*t+1)^2) (4*(2*x+1)) x := by
  refine ⟨?_,actual_literal_affine_inner_derivative x,?_⟩
  · simpa using (hasDerivAt_id (2*x+1)).pow 2
  · convert (actual_literal_affine_inner_derivative x).pow 2 using 1 <;> simp <;> ring

theorem actual_literal_affine_square_derivative_at_one :
    deriv (fun t : ℝ=>(2*t+1)^2) 1=12 := by
  rw [(actual_literal_affine_square_outer_inner_and_derivative 1).2.2.deriv]
  norm_num

theorem actual_literal_shifted_square_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ=>(t-1)^2) (2*(x-1)) x := by
  simpa using ((hasDerivAt_id x).sub_const 1).pow 2

theorem actual_literal_exp_twice_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ=>Real.exp (2*t)) (2*Real.exp (2*x)) x := by
  convert (Real.hasDerivAt_exp (2*x)).comp x ((hasDerivAt_id x).const_mul 2) using 1 <;> ring

theorem actual_frozen_coordinate_partial_uses_only_that_coordinate
    {n : ℕ} (f : (Fin n→ℝ)→ℝ) (x : Fin n→ℝ) (i : Fin n)
    (df : (Fin n→ℝ)→L[ℝ]ℝ) (hf : HasFDerivAt f df x) :
    HasDerivAt (fun t=>f (Function.update x i t)) (df (Pi.single i 1)) (x i) := by
  have hd : HasFDerivAt f df (Function.update x i (x i)) := by simpa using hf
  exact hd.comp_hasDerivAt (hasDerivAt_update x i (x i))

theorem actual_arbitrary_curve_derivative_uses_the_entire_velocity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E→ℝ) (curve : ℝ→E) (t : ℝ) (velocity : E)
    (df : E→L[ℝ]ℝ) (hf : HasFDerivAt f df (curve t))
    (hc : HasDerivAt curve velocity t) :
    HasDerivAt (fun s=>f (curve s)) (df velocity) t := by
  exact hf.comp_hasDerivAt hc

theorem actual_literal_halfline_boundary_has_unique_minimum :
    IsMinOn (fun t : ℝ=>(t-2)^2) (Iic 1) 1 ∧
    ((1:ℝ)-2)^2=1 ∧
    (∀ t : ℝ,t≤1→((t-2)^2=1↔t=1)) ∧
    (∀ t : ℝ,t<1→1<(t-2)^2) := by
  refine ⟨?_,by norm_num,?_,?_⟩
  · intro t ht
    have hs:=sq_nonneg (t-1)
    norm_num at *
    nlinarith
  · intro t ht
    constructor
    · intro he
      have hs:=sq_nonneg (t-1)
      nlinarith
    · intro he;subst t;norm_num
  · intro t ht
    have hs:=sq_nonneg (t-1)
    nlinarith

theorem actual_literal_boundary_optimizer_has_nonzero_ordinary_derivative :
    HasDerivAt (fun t : ℝ=>(t-2)^2) (-2) 1 ∧
    deriv (fun t : ℝ=>(t-2)^2) 1≠0 := by
  have hd : HasDerivAt (fun t : ℝ=>(t-2)^2) (-2) 1 := by
    simpa using ((hasDerivAt_id (1:ℝ)).sub_const 2).pow 2
  exact ⟨hd,by rw [hd.deriv];norm_num⟩

end SafeLearning.CompleteFoundationsScalarCalculusMaterial25
