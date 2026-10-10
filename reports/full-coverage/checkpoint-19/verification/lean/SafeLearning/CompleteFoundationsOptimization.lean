import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsOptimization

def lin2 (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem quadratic_frechet_derivative (p : ℝ × ℝ) :
    HasFDerivAt (fun z : ℝ × ℝ => z.1^2+z.1*z.2+2*z.2^2)
      (lin2 (2*p.1+p.2) (p.1+4*p.2)) p := by
  have hx : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  convert ((hx.pow 2).add (hx.mul hy)).add ((hy.pow 2).const_mul 2) using 1 <;>
    ext z <;> simp [lin2] <;> ring

theorem exp_quadratic_frechet_derivative (p : ℝ × ℝ) :
    HasFDerivAt (fun z : ℝ × ℝ => Real.exp z.1+z.2^2)
      (lin2 (Real.exp p.1) (2*p.2)) p := by
  have hx : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  convert hx.exp.add (hy.pow 2) using 1 <;> ext z <;> simp [lin2] <;> ring

theorem legacy_exp_frechet_derivative (p : ℝ × ℝ) :
    HasFDerivAt (fun z : ℝ × ℝ => z.1^2*z.2+Real.exp z.2)
      (lin2 (2*p.1*p.2) (p.1^2+Real.exp p.2)) p := by
  have hx : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  convert ((hx.pow 2).mul hy).add hy.exp using 1 <;> ext z <;> simp [lin2] <;> ring

theorem least_squares_frechet_derivative (p : ℝ × ℝ) :
    HasFDerivAt (fun z : ℝ × ℝ => (z.1-1)^2+(2*z.2-1)^2)
      (lin2 (2*(p.1-1)) (4*(2*p.2-1))) p := by
  have hx : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  convert ((hx.sub_const 1).pow 2).add (((hy.const_mul 2).sub_const 1).pow 2) using 1 <;>
    ext z <;> simp [lin2] <;> ring

theorem quadratic_hessian_partials (x y : ℝ) :
    HasDerivAt (fun z : ℝ => 2*z+y) 2 x ∧
    HasDerivAt (fun z : ℝ => 2*x+z) 1 y ∧
    HasDerivAt (fun z : ℝ => z+4*y) 1 x ∧
    HasDerivAt (fun z : ℝ => x+4*z) 4 y := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa using ((hasDerivAt_id x).const_mul 2).add_const y
  · simpa using (hasDerivAt_id y).const_add (2*x)
  · simpa using (hasDerivAt_id x).add_const (4*y)
  · simpa using ((hasDerivAt_id y).const_mul 4).const_add x

theorem derivative_numerical_values :
    2*(1 : ℝ)+(-1)=1 ∧ (1 : ℝ)+4*(-1)= -3 ∧
    (1 : ℝ)*0+(-3)*1= -3 ∧ (2 : ℝ)*(0-1)= -2 ∧
    (4 : ℝ)*(2*0-1)= -4 ∧ (-2*(1 : ℝ)-4*1^3)= -6 := by norm_num

theorem quadratic_vertical_remainder (t : ℝ) :
    (1^2+1*(-1+t)+2*(-1+t)^2)-(1^2+1*(-1)+2*(-1)^2)= -3*t+2*t^2 := by ring

theorem parameter_quadratic_psd (a : ℝ) :
    (∀ x y : ℝ, 0 ≤ x^2+y^2+a*x*y) ↔ |a| ≤ 2 := by
  constructor
  · intro h
    have h₁ := h 1 1
    have h₂ := h 1 (-1)
    apply abs_le.mpr; constructor <;> nlinarith
  · intro ha x y
    have h := abs_le.mp ha
    have h₁ := mul_nonneg (show 0 ≤ 2+a by linarith [h.1]) (sq_nonneg (x+y))
    have h₂ := mul_nonneg (show 0 ≤ 2-a by linarith [h.2]) (sq_nonneg (x-y))
    nlinarith

theorem parameter_quadratic_convex_iff (a : ℝ) :
    ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => z.1^2+z.2^2+a*z.1*z.2) ↔ |a| ≤ 2 := by
  constructor
  · rintro ⟨hc,h⟩
    have h₁ := @h (1,1) (by trivial) (-1,-1) (by trivial)
      (1/2 : ℝ) (1/2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have h₂ := @h (1,-1) (by trivial) (-1,1) (by trivial)
      (1/2 : ℝ) (1/2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h₁ h₂
    apply abs_le.mpr; constructor <;> linarith
  · intro ha
    refine ⟨convex_univ,?_⟩
    intro x _ y _ s t hs ht hst
    have hp := (parameter_quadratic_psd a).2 ha (x.1-y.1) (x.2-y.2)
    have hm := mul_nonneg (mul_nonneg hs ht) hp
    change (s*x.1+t*y.1)^2+(s*x.2+t*y.2)^2+a*(s*x.1+t*y.1)*(s*x.2+t*y.2) ≤
      s*(x.1^2+x.2^2+a*x.1*x.2)+t*(y.1^2+y.2^2+a*y.1*y.2)
    have he : s*(x.1^2+x.2^2+a*x.1*x.2)+t*(y.1^2+y.2^2+a*y.1*y.2)-
      ((s*x.1+t*y.1)^2+(s*x.2+t*y.2)^2+a*(s*x.1+t*y.1)*(s*x.2+t*y.2))=
      s*t*((x.1-y.1)^2+(x.2-y.2)^2+a*(x.1-y.1)*(x.2-y.2)) := by
      have ht' : t=1-s := by linarith
      rw [ht']; ring
    linarith

theorem parameter_strict_curvature_iff (a : ℝ) :
    (∃ μ : ℝ, 0 < μ ∧ ∀ x y : ℝ,
      μ*(x^2+y^2) ≤ 2*(x^2+y^2+a*x*y)) ↔ |a|<2 := by
  constructor
  · rintro ⟨μ,hμ,h⟩
    have h₁ := h 1 1
    have h₂ := h 1 (-1)
    exact abs_lt.mpr ⟨by nlinarith,by nlinarith⟩
  · intro ha
    refine ⟨2-|a|,by linarith,?_⟩
    intro x y
    have h₁ : 0 ≤ |a|+a := by linarith [neg_abs_le a]
    have h₂ : 0 ≤ |a|-a := by linarith [le_abs_self a]
    have hp := mul_nonneg h₁ (sq_nonneg (x+y))
    have hm := mul_nonneg h₂ (sq_nonneg (x-y))
    nlinarith

theorem restricted_square_conjugate_supremum (y : ℝ) :
    IsLUB ((fun x : ℝ => y*x-x^2/2) '' Ici 0) (if 0 ≤ y then y^2/2 else 0) := by
  by_cases hy : 0 ≤ y
  · simp only [if_pos hy]
    constructor
    · rintro z ⟨x,hx,rfl⟩
      nlinarith [sq_nonneg (x-y)]
    · intro z hz
      have hh := hz (show y*y-y^2/2 ∈ ((fun x : ℝ => y*x-x^2/2) '' Ici 0) from ⟨y,hy,rfl⟩)
      nlinarith
  · simp only [if_neg hy]
    constructor
    · rintro z ⟨x,hx,rfl⟩
      have hxy : y*x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hx
      nlinarith [sq_nonneg x]
    · intro z hz
      have hh := hz (show (0 : ℝ) ∈ ((fun x : ℝ => y*x-x^2/2) '' Ici 0) from ⟨0,by simp,by ring⟩)
      exact hh

theorem translated_square_conjugate_supremum (e : ℝ) :
    IsLUB ((fun w : ℝ => w*e-(w-1)^2/2) '' Ici 0)
      (if -1 ≤ e then e+e^2/2 else -1/2) := by
  by_cases he : -1 ≤ e
  · simp only [if_pos he]
    constructor
    · rintro z ⟨w,hw,rfl⟩; nlinarith [sq_nonneg (w-(1+e))]
    · intro z hz
      have hh := hz (show (1+e)*e-((1+e)-1)^2/2 ∈
        ((fun w : ℝ => w*e-(w-1)^2/2) '' Ici 0) from ⟨1+e,by simp only [mem_Ici]; linarith,rfl⟩)
      nlinarith
  · simp only [if_neg he]
    constructor
    · rintro z ⟨w,hw,rfl⟩
      exact SafeLearning.PrimersFoundations.translated_conjugate_negative w e hw (by linarith)
    · intro z hz
      exact hz ⟨0,by simp,by norm_num⟩

theorem constrained_scalar_unique (x : ℝ) (hx : x ≤ 1) :
    4 ≤ (x-3)^2 ∧ ((x-3)^2=4 ↔ x=1) := by
  constructor
  · nlinarith [sq_nonneg (x-1)]
  · constructor <;> intro h <;> nlinarith [sq_nonneg (x-1)]

theorem scalar_kkt_certificates :
    (1 : ℝ)-1≤0 ∧ (0 : ℝ)≤4 ∧ (4 : ℝ)*(1-1)=0 ∧
    2*((1 : ℝ)-3)+4=0 ∧ (3 : ℝ)-4<0 ∧
    (0 : ℝ)*(3-4)=0 ∧ 2*((3 : ℝ)-3)+0=0 := by norm_num

theorem halfspace_unique_optimum (x y : ℝ) (h : x+y ≤ 1) :
    9/4 ≤ ((x-2)^2+(y-2)^2)/2 ∧
    (((x-2)^2+(y-2)^2)/2=9/4 ↔ x=1/2 ∧ y=1/2) := by
  constructor
  · nlinarith [sq_nonneg (x-y),sq_nonneg (x+y-1)]
  · constructor
    · intro he; constructor <;> nlinarith [sq_nonneg (x-y),sq_nonneg (x+y-1)]
    · rintro ⟨rfl,rfl⟩; norm_num

theorem halfspace_kkt_certificate :
    (1/2 : ℝ)+1/2-1=0 ∧ (-1/2 : ℝ)<0 ∧ (0 : ℝ)≤3/2 ∧
    ((1/2 : ℝ)-2)+3/2=0 ∧ (3/2 : ℝ)*(1/2+1/2-1)=0 := by norm_num

theorem penalty_unique_optimum (x : ℝ) :
    3/4 ≤ (x-2)^2+3*(max (x-1) 0)^2 ∧
    ((x-2)^2+3*(max (x-1) 0)^2=3/4 ↔ x=5/4) := by
  by_cases hx : x ≤ 1
  · rw [max_eq_right (by linarith)]
    constructor
    · nlinarith [sq_nonneg (x-1)]
    · constructor <;> intro h <;> nlinarith [sq_nonneg (x-1)]
  · rw [max_eq_left (by linarith)]
    constructor
    · nlinarith [sq_nonneg (x-5/4)]
    · constructor <;> intro h <;> nlinarith [sq_nonneg (x-5/4)]

theorem approximate_kkt_minimal_tolerance (ε : ℝ) :
    (|2*((9/10 : ℝ)-2)+11/5| ≤ ε ∧
      (11/5 : ℝ)*(1-9/10) ≤ ε) ↔ 11/50 ≤ ε := by
  norm_num
  intro h; linarith

theorem qp_unique_optimum (x y : ℝ) :
    0 ≤ (x-1)^2+2*(y+1)^2 ∧
    ((x-1)^2+2*(y+1)^2=0 ↔ x=1 ∧ y= -1) := by
  constructor
  · positivity
  · constructor
    · intro h; constructor <;> nlinarith [sq_nonneg (x-1),sq_nonneg (y+1)]
    · rintro ⟨rfl,rfl⟩; norm_num

theorem finite_controller_margins :
    min (3/5 : ℝ) (1/10)=1/10 ∧ min (7/20 : ℝ) (3/10)=3/10 ∧
    min (4/5 : ℝ) (-1/20)= -1/20 ∧
    (1/10 : ℝ)<3/10 ∧ (-1/20 : ℝ)<3/10 ∧
    max (3/5 : ℝ) (1/10)< max (4/5 : ℝ) (-1/20) ∧
    max (7/20 : ℝ) (3/10)< max (4/5 : ℝ) (-1/20) := by norm_num

end SafeLearning.CompleteFoundationsOptimization
