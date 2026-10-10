import SafeLearning.CompleteFoundationsOptimization
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.Deriv.Abs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set
open scoped BigOperators Matrix
namespace SafeLearning.CompleteFoundationsParameterizedConvex
abbrev E := EuclideanSpace ℝ (Fin 2)
def point (x y : ℝ) : E := WithLp.toLp 2 ![x,y]
def objective (a : ℝ) (x : E) : ℝ := (x 0)^2+(x 1)^2+a*x 0*x 1
def sourceH (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![2,a;a,2]
def hessian (a : ℝ) : E →L[ℝ] E := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (sourceH a)
def coordinate (i : Fin 2) : E →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 =>  ℝ) i

theorem actual_norm_square (x : E) : ‖x‖^2=(x 0)^2+(x 1)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs]

theorem actual_hessian_coordinates (a : ℝ) (x : E) :
    hessian a x=point (2*x 0+a*x 1) (a*x 0+2*x 1) := by
  ext i
  change (sourceH a *ᵥ (x : Fin 2→ℝ)) i=(![2*x 0+a*x 1,a*x 0+2*x 1] : Fin 2→ℝ) i
  fin_cases i  <;>  simp [sourceH,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail]

theorem actual_gradient (a : ℝ) (x : E) :
    HasGradientAt (objective a) (hessian a x) x := by
  have h0 := (coordinate 0).hasFDerivAt (x:=x)
  have h1 := (coordinate 1).hasFDerivAt (x:=x)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((h0.pow 2).add (h1.pow 2)).add ((h0.mul h1).const_mul a) using 1
  · funext y
    simp [objective,coordinate,PiLp.proj,PiLp.projₗ]
    ring
  · ext u
    rw [actual_hessian_coordinates]
    simp [point,coordinate,PiLp.proj,PiLp.projₗ,InnerProductSpace.toDual_apply_apply,
      PiLp.inner_apply,Fin.sum_univ_succ]
    ring

theorem actual_hessian (a : ℝ) (x : E) :
    HasFDerivAt (gradient (objective a)) (hessian a) x := by
  have hg : gradient (objective a)=hessian a := funext (fun x=> (actual_gradient a x).gradient)
  rw [hg]
  exact (hessian a).hasFDerivAt

theorem actual_full_hessian_eigenvalues (a lambda : ℝ) :
    (∃ x : E,x ≠ 0 ∧ hessian a x=lambda • x) ↔ lambda=2+a ∨ lambda=2-a := by
  constructor
  · rintro ⟨x,hx,he⟩
    have h0 := congrArg (fun u : E=> u 0) he
    have h1 := congrArg (fun u : E=> u 1) he
    rw [actual_hessian_coordinates] at h0 h1
    simp [point] at h0 h1
    have hnon : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hx
      ext i
      fin_cases i  <;>  simp [hn]
    have h0' : (lambda-2)*x 0=a*x 1 := by linarith
    have h1' : (lambda-2)*x 1=a*x 0 := by linarith
    have hp : ((lambda-2)^2-a^2)*x 0=0 := by
      calc
        ((lambda-2)^2-a^2)*x 0=(lambda-2)*((lambda-2)*x 0)-a*(a*x 0) := by ring
        _=(lambda-2)*(a*x 1)-a*((lambda-2)*x 1) := by rw [h0',←h1']
        _=0 := by ring
    have hq : ((lambda-2)^2-a^2)*x 1=0 := by
      calc
        ((lambda-2)^2-a^2)*x 1=(lambda-2)*((lambda-2)*x 1)-a*(a*x 1) := by ring
        _=(lambda-2)*(a*x 0)-a*((lambda-2)*x 0) := by rw [h1',←h0']
        _=0 := by ring
    have heq : (lambda-2)^2=a^2 := by
      rcases hnon with hnon|hnon
      · exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hnon)
      · exact sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_right hnon)
    have hr : (lambda-2-a)*(lambda-2+a)=0 := by nlinarith [heq]
    rcases mul_eq_zero.mp hr with hr|hr
    · left;linarith
    · right;linarith
  · intro h
    rcases h with rfl|rfl
    · refine ⟨point 1 1,?_,?_⟩
      · intro hz;have := congrArg (fun u : E=> u 0) hz;simp [point] at this
      · rw [actual_hessian_coordinates];ext i;fin_cases i  <;>  simp [point]  <;>  ring
    · refine ⟨point 1 (-1),?_,?_⟩
      · intro hz;have := congrArg (fun u : E=> u 0) hz;simp [point] at this
      · rw [actual_hessian_coordinates];ext i;fin_cases i  <;>  simp [point]  <;>  ring

theorem actual_convex_iff (a : ℝ) : ConvexOn ℝ univ (objective a) ↔ |a| ≤ 2 := by
  constructor
  · intro hf
    have h1 := hf.2 (show point 1 1 ∈ univ by trivial) (show point (-1) (-1) ∈ univ by trivial)
      (show 0 ≤ (1/2:ℝ) by norm_num) (show 0 ≤ (1/2:ℝ) by norm_num) (show (1/2:ℝ)+1/2=1 by norm_num)
    have h2 := hf.2 (show point 1 (-1) ∈ univ by trivial) (show point (-1) 1 ∈ univ by trivial)
      (show 0 ≤ (1/2:ℝ) by norm_num) (show 0 ≤ (1/2:ℝ) by norm_num) (show (1/2:ℝ)+1/2=1 by norm_num)
    norm_num [objective,point] at h1 h2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · intro ha
    refine ⟨convex_univ,?_⟩
    intro x _ y _ s t hs ht hst
    have hp := (SafeLearning.CompleteFoundationsOptimization.parameter_quadratic_psd a).2 ha (x 0-y 0) (x 1-y 1)
    have hm := mul_nonneg (mul_nonneg hs ht) hp
    change (s*x 0+t*y 0)^2+(s*x 1+t*y 1)^2+a*(s*x 0+t*y 0)*(s*x 1+t*y 1) ≤
      s*((x 0)^2+(x 1)^2+a*x 0*x 1)+t*((y 0)^2+(y 1)^2+a*y 0*y 1)
    have he : s*((x 0)^2+(x 1)^2+a*x 0*x 1)+t*((y 0)^2+(y 1)^2+a*y 0*y 1)-
      ((s*x 0+t*y 0)^2+(s*x 1+t*y 1)^2+a*(s*x 0+t*y 0)*(s*x 1+t*y 1))=
      s*t*((x 0-y 0)^2+(x 1-y 1)^2+a*(x 0-y 0)*(x 1-y 1)) := by
      have ht' : t=1-s := by linarith
      rw [ht'];ring
    linarith

theorem actual_sharp_lower_curvature (a : ℝ) (x : E) :
    (2-|a|)*‖x‖^2 ≤ 2*objective a x := by
  rw [actual_norm_square]
  have hp := mul_nonneg (show 0 ≤ |a|+a by linarith [neg_abs_le a]) (sq_nonneg (x 0+x 1))
  have hm := mul_nonneg (show 0 ≤ |a|-a by linarith [le_abs_self a]) (sq_nonneg (x 0-x 1))
  unfold objective
  nlinarith

theorem actual_strong_convex_constant (a : ℝ) :
    StrongConvexOn univ (2-|a|) (objective a) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ s t hs ht hst
  have hp := actual_sharp_lower_curvature a (x-y)
  rw [actual_norm_square] at hp
  simp only [PiLp.sub_apply] at hp
  have hm := mul_nonneg (mul_nonneg hs ht) (show 0 ≤ objective a (x-y)-(2-|a|)/2*‖x-y‖^2 by linarith [actual_sharp_lower_curvature a (x-y)])
  change objective a (s • x+t • y) ≤ s*objective a x+t*objective a y-s*t*((2-|a|)/2*‖x-y‖^2)
  simp only [objective,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hm ⊢
  rw [actual_norm_square] at hm ⊢
  simp only [PiLp.sub_apply] at hm ⊢
  have ht' : t=1-s := by linarith
  rw [ht'] at hm ⊢
  nlinarith

theorem actual_strong_convex_iff (a : ℝ) :
    (∃ mu : ℝ,0 < mu ∧ StrongConvexOn univ mu (objective a)) ↔ |a| < 2 := by
  constructor
  · rintro ⟨mu,hmu,hf⟩
    have h1 := hf.2 (show point 1 1 ∈ univ by trivial) (show point (-1) (-1) ∈ univ by trivial)
      (show 0 ≤ (1/2:ℝ) by norm_num) (show 0 ≤ (1/2:ℝ) by norm_num) (show (1/2:ℝ)+1/2=1 by norm_num)
    have h2 := hf.2 (show point 1 (-1) ∈ univ by trivial) (show point (-1) 1 ∈ univ by trivial)
      (show 0 ≤ (1/2:ℝ) by norm_num) (show 0 ≤ (1/2:ℝ) by norm_num) (show (1/2:ℝ)+1/2=1 by norm_num)
    change objective a ((1/2:ℝ) • point 1 1+(1/2:ℝ) • point (-1) (-1)) ≤
      (1/2)*objective a (point 1 1)+(1/2)*objective a (point (-1) (-1))-(1/2)*(1/2)*(mu/2*‖point 1 1-point (-1) (-1)‖^2) at h1
    change objective a ((1/2:ℝ) • point 1 (-1)+(1/2:ℝ) • point (-1) 1) ≤
      (1/2)*objective a (point 1 (-1))+(1/2)*objective a (point (-1) 1)-(1/2)*(1/2)*(mu/2*‖point 1 (-1)-point (-1) 1‖^2) at h2
    rw [actual_norm_square] at h1 h2
    norm_num [objective,point] at h1 h2
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · intro ha
    exact ⟨2-|a|,by linarith,actual_strong_convex_constant a⟩

theorem actual_boundary_flat_directions :
    (∀ t : ℝ,objective 2 (point t (-t))=0) ∧ (∀ t : ℝ,objective (-2) (point t t)=0) := by
  constructor  <;>  intro t  <;>  simp [objective,point]  <;>  ring

def IsSubgradientAtZero (s : ℝ) : Prop := ∀ y : ℝ,|0|+s*(y-0) ≤ |y|

theorem actual_abs_all_subgradients (s : ℝ) : IsSubgradientAtZero s ↔ s ∈ Icc (-1) 1 := by
  constructor
  · intro h
    have hp:=h 1
    have hn:=h (-1)
    norm_num at hp hn
    exact ⟨by linarith,by linarith⟩
  · rintro ⟨hl,hu⟩ y
    simp only [abs_zero,sub_zero,zero_add]
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy];nlinarith [mul_le_mul_of_nonneg_right hu hy]
    · have hy' : y < 0 := lt_of_not_ge hy
      rw [abs_of_neg hy'];nlinarith [mul_le_mul_of_nonpos_right hl hy'.le]

theorem actual_zero_subgradient_and_global_minimum :
    IsSubgradientAtZero 0 ∧ ∀ y : ℝ,|(0:ℝ)| ≤ |y| := by
  exact ⟨(actual_abs_all_subgradients 0).2 (by norm_num),fun y=>by simpa using abs_nonneg y⟩

theorem actual_abs_no_derivative_at_zero : ¬DifferentiableAt ℝ (abs : ℝ→ℝ) 0 :=
  not_differentiableAt_abs_zero
end SafeLearning.CompleteFoundationsParameterizedConvex
