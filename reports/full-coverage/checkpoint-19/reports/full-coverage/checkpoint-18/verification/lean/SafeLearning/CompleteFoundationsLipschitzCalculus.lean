import SafeLearning.PrimersFoundations
import SafeLearning.CompleteFoundationsAlgorithms

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology NNReal

namespace SafeLearning.CompleteFoundationsLipschitzCalculus

theorem derivative_bound_iff_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : Set E) (f : E → F) (L : ℝ≥0) (hopen : IsOpen D) (hconvex : Convex ℝ D)
    (hf : ∀ x ∈ D, DifferentiableAt ℝ f x) :
    LipschitzOnWith L f D ↔ ∀ x ∈ D, ‖fderiv ℝ f x‖≤(L : ℝ) := by
  constructor
  · intro h x hx
    exact norm_fderiv_le_of_lipschitzOn ℝ (hopen.mem_nhds hx) h
  · intro h
    exact hconvex.lipschitzOnWith_of_nnnorm_fderiv_le hf
      (fun x hx => (NNReal.coe_le_coe).mp (h x hx))

theorem c1_locally_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 1 f) : LocallyLipschitz f := hf.locallyLipschitz

theorem absolute_and_sine_lipschitz :
    LipschitzWith 1 (fun x : ℝ => |x|) ∧ LipschitzWith 1 Real.sin := by
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y
  · exact Real.lipschitzWith_sin

theorem square_lipschitz_on_radius (R x y : ℝ) (hR : 0≤R)
    (hx : x ∈ Icc (-R) R) (hy : y ∈ Icc (-R) R) :
    |x^2-y^2|≤2*R*|x-y| := by
  have hxabs : |x|≤R := abs_le.mpr hx
  have hyabs : |y|≤R := abs_le.mpr hy
  have hsum : |x+y|≤2*R := (abs_add_le x y).trans (by linarith)
  have hid : x^2-y^2=(x-y)*(x+y) := by ring
  rw [hid,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg (x-y))]

theorem square_interval_sharp (L : ℝ)
    (h : ∀ x ∈ Icc (-2 : ℝ) 2, ∀ y ∈ Icc (-2 : ℝ) 2,
      |x^2-y^2|≤L*|x-y|) : 4≤L := by
  have hL := h 1 (by norm_num) 0 (by norm_num)
  norm_num at hL
  by_contra hnot
  have hsmall : L<4 := lt_of_not_ge hnot
  let y : ℝ := L/2
  have hy : y ∈ Icc (-2 : ℝ) 2 := by dsimp [y];constructor <;> linarith
  have hh := h 2 (by norm_num) y hy
  have hdiff : 0≤(2 : ℝ)^2-y^2 := by dsimp [y];nlinarith
  have hdiff' : 0≤(2 : ℝ)-y := by dsimp [y];linarith
  rw [abs_of_nonneg hdiff,abs_of_nonneg hdiff'] at hh
  have hp := sq_pos_of_pos (show 0<4-L by linarith)
  dsimp [y] at hh
  nlinarith

theorem square_not_globally_lipschitz :
    ¬ ∃ L : ℝ, ∀ x y : ℝ, |x^2-y^2|≤L*|x-y| := by
  rintro ⟨L,hL⟩
  let x : ℝ := |L|+1
  have hx : 0<x := by dsimp [x];positivity
  have h := hL x 0
  simp only [zero_pow (by decide : 2≠0),sub_zero,abs_of_pos hx] at h
  rw [abs_of_nonneg (sq_nonneg x)] at h
  have hprod := mul_pos hx (show 0<x-L by dsimp [x];linarith [le_abs_self L])
  nlinarith

theorem square_gradient_smooth :
    (∀ x : ℝ, HasDerivAt (fun z : ℝ => z^2) (2*x) x) ∧
      LipschitzWith 2 (fun x : ℝ => 2*x) := by
  constructor
  · intro x; simpa using (hasDerivAt_id x).fun_pow 2
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,NNReal.coe_ofNat] using
      SafeLearning.PrimersFoundations.square_derivative_lipschitz x y |>.le

theorem square_gradient_constant_sharp (L : ℝ)
    (h : ∀ x y : ℝ, |2*x-2*y|≤L*|x-y|) : 2≤L := by
  have hh := h 1 0
  norm_num at hh
  exact hh

theorem square_locally_lipschitz : LocallyLipschitz (fun x : ℝ => x^2) := by
  exact (show ContDiff ℝ 1 (fun x : ℝ => x^2) from contDiff_id.pow 2).locallyLipschitz

def stepFunction (x : ℝ) : ℝ := if 0<x then 1 else 0

theorem step_not_continuous_at_zero : ¬ ContinuousAt stepFunction 0 := by
  intro h
  have ht := h.tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have heq : (fun n : ℕ => stepFunction (1/((n : ℝ)+1)))=(fun _ => (1 : ℝ)) := by
    ext n
    simp only [stepFunction,if_pos (show 0<1/((n : ℝ)+1) by positivity)]
  simp only [Function.comp_def] at ht
  rw [heq] at ht
  have hneq := tendsto_nhds_unique ht (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num [stepFunction] at hneq

theorem sqrt_not_lipschitz_on_unit :
    ¬ ∃ L : ℝ≥0, LipschitzOnWith L Real.sqrt (Icc (0 : ℝ) 1) := by
  rintro ⟨L,hL⟩
  let t : ℝ := 1/((L : ℝ)+1)
  have ht : 0<t := by dsimp [t];positivity
  have ht₁ : t≤1 := by
    dsimp [t]
    rw [div_le_iff₀ (by positivity)]
    linarith [L.coe_nonneg]
  have hx : t^2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg t,by nlinarith⟩
  have h := hL.dist_le_mul (t^2) hx 0 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  rw [Real.dist_eq,Real.dist_eq,Real.sqrt_sq ht.le,Real.sqrt_zero,sub_zero,sub_zero,
    abs_of_pos ht,abs_of_nonneg (sq_nonneg t)] at h
  have heq : ((L : ℝ)+1)*t=1 := by dsimp [t];field_simp
  have hm : ((L : ℝ)+1)*t^2=t := by linear_combination t*heq
  nlinarith [sq_pos_of_pos ht]

theorem square_root_continuous_but_not_lipschitz :
    ContinuousOn Real.sqrt (Icc (0 : ℝ) 1) ∧
      ¬ ∃ L : ℝ≥0, LipschitzOnWith L Real.sqrt (Icc (0 : ℝ) 1) := by
  exact ⟨Real.continuous_sqrt.continuousOn,sqrt_not_lipschitz_on_unit⟩

theorem real_lipschitz_chord_and_continuity {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) :
    (∀ x y, |f x-f y|≤(L : ℝ)*dist x y) ∧ Continuous f := by
  exact ⟨fun x y => by simpa only [Real.dist_eq] using hf.dist_le_mul x y,hf.continuous⟩

theorem composition_lipschitz {X Y Z : Type*}
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    (f : Y → Z) (g : X → Y) (Lf Lg : ℝ≥0)
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g) :
    LipschitzWith (Lf*Lg) (f ∘ g) := hf.comp hg

theorem two_argument_lipschitz {A X : Type*} [PseudoMetricSpace A] [PseudoMetricSpace X]
    (g : A → X → ℝ) (La Lx : ℝ≥0)
    (ha : ∀ x, LipschitzWith La (fun a => g a x))
    (hx : ∀ a, LipschitzWith Lx (g a)) (a a' : A) (x x' : X) :
    |g a x-g a' x'|≤(La : ℝ)*dist a a'+(Lx : ℝ)*dist x x' := by
  have h₁ := (ha x).dist_le_mul a a'
  have h₂ := (hx a').dist_le_mul x x'
  rw [Real.dist_eq] at h₁ h₂
  have hid : g a x-g a' x'=(g a x-g a' x)+(g a' x-g a' x') := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add h₁ h₂)

theorem sum_lipschitz {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) (Lf Lg : ℝ≥0)
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g) :
    LipschitzWith (Lf+Lg) (fun x => f x+g x) := hf.add hg

theorem scaled_lipschitz {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (L : ℝ≥0) (a : ℝ) (hf : LipschitzWith L f) :
    ∀ x y, |a*f x-a*f y| ≤ |a| * (L : ℝ)*dist x y := by
  intro x y
  have hh := hf.dist_le_mul x y
  rw [Real.dist_eq] at hh
  have hid : a*f x-a*f y=a*(f x-f y) := by ring
  rw [hid,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg a)]

theorem bounded_product_lipschitz {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) (Lf Lg Mf Mg : ℝ≥0)
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hMf : ∀ x, |f x|≤(Mf : ℝ)) (hMg : ∀ x, |g x|≤(Mg : ℝ)) :
    ∀ x y, |f x*g x-f y*g y|≤((Mf : ℝ)*(Lg : ℝ)+(Mg : ℝ)*(Lf : ℝ))*dist x y := by
  intro x y
  have h₁ := hf.dist_le_mul x y
  have h₂ := hg.dist_le_mul x y
  rw [Real.dist_eq] at h₁ h₂
  have hid : f x*g x-f y*g y=f x*(g x-g y)+g y*(f x-f y) := by ring
  rw [hid]
  calc
    _ ≤ |f x*(g x-g y)|+|g y*(f x-f y)| := abs_add_le _ _
    _ = |f x| * |g x-g y|+|g y| * |f x-f y| := by rw [abs_mul,abs_mul]
    _ ≤ (Mf : ℝ)*((Lg : ℝ)*dist x y)+(Mg : ℝ)*((Lf : ℝ)*dist x y) :=
      add_le_add (mul_le_mul (hMf x) h₂ (abs_nonneg _) Mf.coe_nonneg)
        (mul_le_mul (hMg y) h₁ (abs_nonneg _) Mg.coe_nonneg)
    _ = _ := by ring

theorem reciprocal_lipschitz {X : Type*} [PseudoMetricSpace X]
    (g : X → ℝ) (L : ℝ≥0) (c : ℝ) (hc : 0<c)
    (hg : LipschitzWith L g) (haway : ∀ x, c≤|g x|) :
    ∀ x y, |(g x)⁻¹-(g y)⁻¹|≤((L : ℝ)/c^2)*dist x y := by
  intro x y
  have hxp : 0 < |g x| := hc.trans_le (haway x)
  have hyp : 0 < |g y| := hc.trans_le (haway y)
  have hx : g x≠0 := abs_pos.mp hxp
  have hy : g y≠0 := abs_pos.mp hyp
  have hid : (g x)⁻¹-(g y)⁻¹=(g y-g x)/(g x*g y) := by field_simp
  have hprod : c*c ≤ |g x| * |g y| := mul_le_mul (haway x) (haway y) hc.le (abs_nonneg _)
  have h := hg.dist_le_mul x y
  rw [Real.dist_eq] at h
  rw [hid,abs_div,abs_mul,abs_sub_comm]
  calc
    _ ≤ ((L : ℝ)*dist x y)/(|g x| * |g y|) :=
      div_le_div_of_nonneg_right h (mul_pos hxp hyp).le
    _ ≤ ((L : ℝ)*dist x y)/(c*c) :=
      div_le_div_of_nonneg_left (mul_nonneg L.coe_nonneg dist_nonneg) (mul_pos hc hc) hprod
    _ = _ := by ring

theorem uniformly_close_infima {I : Type*} [Nonempty I] (a b : I → ℝ) (d : ℝ)
    (ha : BddBelow (range a)) (hb : BddBelow (range b))
    (hclose : ∀ i, |a i-b i|≤d) : |(⨅ i,a i)-(⨅ i,b i)|≤d := by
  have h₁ : (⨅ i,a i)-d≤⨅ i,b i := by
    apply le_ciInf
    intro i
    have hh := (abs_le.mp (hclose i)).2
    have hi := ciInf_le ha i
    linarith
  have h₂ : (⨅ i,b i)-d≤⨅ i,a i := by
    apply le_ciInf
    intro i
    have hh := (abs_le.mp (hclose i)).1
    have hi := ciInf_le hb i
    linarith
  rw [abs_le]
  constructor <;> linarith

theorem infima_difference_le_sup {I : Type*} [Nonempty I] (a b : I → ℝ)
    (ha : BddBelow (range a)) (hb : BddBelow (range b))
    (hd : BddAbove (range (fun i => |a i-b i|))) :
    |(⨅ i,a i)-(⨅ i,b i)|≤⨆ i,|a i-b i| := by
  exact uniformly_close_infima a b _ ha hb (fun i => le_ciSup hd i)

theorem nonexpansive_iterate {X : Type*} [PseudoMetricSpace X]
    (F : X → X) (hF : LipschitzWith 1 F) (n : ℕ) :
    LipschitzWith 1 F^[n] := by simpa using hF.iterate n

theorem nonexpansive_scalar_euler_iff (h k : ℝ) :
    LipschitzWith 1 (fun x : ℝ => (1-h*k)*x) ↔ 0≤h*k ∧ h*k≤2 := by
  constructor
  · intro hh
    have ht := hh.dist_le_mul 1 0
    simp only [Real.dist_eq,mul_one,mul_zero,sub_zero,NNReal.coe_one,one_mul,
      abs_one] at ht
    have ha := abs_le.mp ht
    constructor <;> linarith
  · rintro ⟨h₀,h₂⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,Real.dist_eq,← mul_sub,abs_mul]
    have ha : |1-h*k|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    simpa using mul_le_mul_of_nonneg_right ha (abs_nonneg (x-y))

theorem nonexpansive_trajectory_margin_lipschitz {X : Type*} [PseudoMetricSpace X]
    (F : X → X) (g : X → ℝ) (L : ℝ≥0)
    (hF : LipschitzWith 1 F) (hg : LipschitzWith L g)
    (hfinite : ∀ x, BddBelow (range (fun n : ℕ => g (F^[n] x)))) :
    LipschitzWith L (fun x => ⨅ n : ℕ,g (F^[n] x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  apply uniformly_close_infima _ _ _ (hfinite x) (hfinite y)
  intro n
  have hh := hg.dist_le_mul (F^[n] x) (F^[n] y)
  rw [Real.dist_eq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (by simpa using (nonexpansive_iterate F hF n).dist_le_mul x y) L.coe_nonneg)

theorem scalar_quadratic_derivative (L x : ℝ) :
    HasDerivAt (fun z : ℝ => (L/2)*z^2) (L*x) x := by
  convert ((hasDerivAt_id x).pow 2).const_mul (L/2) using 1 <;> simp [id_eq] <;> ring

theorem scalar_gradient_general_iteration (L eta x₀ : ℝ) (n : ℕ) :
    (fun x : ℝ => x-eta*(L*x))^[n] x₀=(1-eta*L)^n*x₀ := by
  have heq : (fun x : ℝ => x-eta*(L*x))=(fun x => (1-eta*L)*x) := by
    ext x; ring
  rw [heq,SafeLearning.CompleteFoundationsAlgorithms.scaling_iteration]

theorem scalar_gradient_general_converges_iff (L eta x₀ : ℝ)
    (hL : 0<L) (hx : x₀≠0) :
    Tendsto (fun n => (fun x : ℝ => x-eta*(L*x))^[n] x₀) atTop (𝓝 0) ↔
      0<eta ∧ eta<2/L := by
  have heq : (fun x : ℝ => x-eta*(L*x))=(fun x => (1-eta*L)*x) := by
    ext x; ring
  rw [heq,SafeLearning.CompleteFoundationsAlgorithms.scaling_converges_iff _ _ hx,abs_lt]
  rw [lt_div_iff₀ hL]
  constructor
  · rintro ⟨h₁,h₂⟩
    constructor
    · by_contra hnot
      have hprod : eta*L≤0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hL.le
      linarith
    · linarith
  · rintro ⟨h₁,h₂⟩
    have hprod : 0<eta*L := mul_pos h₁ hL
    constructor <;> linarith

theorem scalar_gradient_zero_start (L eta : ℝ) (n : ℕ) :
    (fun x : ℝ => x-eta*(L*x))^[n] 0=0 := by
  rw [scalar_gradient_general_iteration]
  simp

theorem scalar_gradient_zero_converges (L eta : ℝ) :
    Tendsto (fun n => (fun x : ℝ => x-eta*(L*x))^[n] 0) atTop (𝓝 0) := by
  simpa only [scalar_gradient_zero_start] using (tendsto_const_nhds (x := (0 : ℝ)))

end SafeLearning.CompleteFoundationsLipschitzCalculus
