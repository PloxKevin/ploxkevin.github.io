import SafeLearning.Modules

set_option autoImplicit false
noncomputable section
open Set
open scoped NNReal
namespace SafeLearning.CompleteModulesNetworks

def twoNeuron (x y : ℝ) : ℝ := (max (x+2*y) 0+max (x-2*y) 0)/2

theorem two_neuron_max_affine (x y : ℝ) :
    twoNeuron x y=max (max 0 x) (max (x/2+y) (x/2-y)) := by
  unfold twoNeuron
  simp only [max_def]
  split_ifs <;> linarith

theorem abs_max_pair_bound (a b c d r : ℝ)
    (ha : |a-c| ≤ r) (hb : |b-d| ≤ r) : |max a b-max c d| ≤ r := by
  exact (abs_max_sub_max_le_max a b c d).trans (max_le ha hb)

theorem linear_gradient_l2 (a b dx dy r : ℝ) (hr : 0 ≤ r)
    (h : dx^2+dy^2 ≤ r^2) :
    |a*dx+b*dy| ≤ Real.sqrt (a^2+b^2)*r := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ a^2+b^2)
  have hn := Real.sqrt_nonneg (a^2+b^2)
  have hc : (a*dx+b*dy)^2+(b*dx-a*dy)^2=(a^2+b^2)*(dx^2+dy^2) := by ring
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ a^2+b^2)
  have hb : (a*dx+b*dy)^2 ≤ (Real.sqrt (a^2+b^2)*r)^2 := by
    rw [mul_pow,hs]
    nlinarith [sq_nonneg (b*dx-a*dy)]
  exact abs_le_of_sq_le_sq hb (mul_nonneg hn hr)

theorem two_neuron_lipschitz_l2 (x y xb yb r : ℝ) (hr : 0 ≤ r)
    (hd : (x-xb)^2+(y-yb)^2 ≤ r^2) :
    |twoNeuron x y-twoNeuron xb yb| ≤ Real.sqrt (5/4)*r := by
  rw [two_neuron_max_affine,two_neuron_max_affine]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5/4)
  have hn := Real.sqrt_nonneg (5/4:ℝ)
  have hge : (1:ℝ) ≤ Real.sqrt (5/4) := by nlinarith
  apply abs_max_pair_bound
  · apply abs_max_pair_bound
    · simp; positivity
    · have hx : |x-xb| ≤ r := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (y-yb)]) hr
      exact hx.trans (by nlinarith)
  · apply abs_max_pair_bound
    · have hl := linear_gradient_l2 (1/2) 1 (x-xb) (y-yb) r hr hd
      rw [show (1/2:ℝ)^2+1^2=5/4 by norm_num] at hl
      simp only [one_mul] at hl
      convert hl using 1 <;> ring
    · have hl := linear_gradient_l2 (1/2) (-1) (x-xb) (y-yb) r hr hd
      rw [show (1/2:ℝ)^2+(-1)^2=5/4 by norm_num] at hl
      convert hl using 1 <;> ring

theorem linear_gradient_box (a b dx dy r : ℝ)
    (hx : |dx| ≤ r) (hy : |dy| ≤ r) : |a*dx+b*dy| ≤ (|a|+|b|)*r := by
  calc |a*dx+b*dy| ≤ |a*dx|+|b*dy| := abs_add_le _ _
    _ = |a| *|dx|+|b| *|dy| := by rw [abs_mul,abs_mul]
    _ ≤ (|a|+|b|)*r := by
      nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg a),mul_le_mul_of_nonneg_left hy (abs_nonneg b)]

theorem two_neuron_lipschitz_box (x y xb yb r : ℝ) (hr : 0 ≤ r)
    (hx : |x-xb| ≤ r) (hy : |y-yb| ≤ r) :
    |twoNeuron x y-twoNeuron xb yb| ≤ (3/2)*r := by
  rw [two_neuron_max_affine,two_neuron_max_affine]
  apply abs_max_pair_bound
  · apply abs_max_pair_bound
    · simp; positivity
    · exact hx.trans (by nlinarith)
  · apply abs_max_pair_bound
    · have hl := linear_gradient_box (1/2) 1 (x-xb) (y-yb) r hx hy
      norm_num at hl
      convert hl using 1 <;> ring
    · have hl := linear_gradient_box (1/2) (-1) (x-xb) (y-yb) r hx hy
      norm_num at hl
      convert hl using 1 <;> ring

theorem physical_correction_box (x y xb yb : ℝ)
    (hx : |x-xb| ≤ 1/50) (hy : |y-yb| ≤ 1/50) :
    |2*twoNeuron x y-2*twoNeuron xb yb| ≤ 3/50 := by
  have h := two_neuron_lipschitz_box x y xb yb (1/50) (by norm_num) hx hy
  have hid : 2*twoNeuron x y-2*twoNeuron xb yb=2*(twoNeuron x y-twoNeuron xb yb) := by ring
  rw [hid,abs_mul]
  norm_num
  linarith

theorem physical_box_bound_attained :
    |2*twoNeuron (1/50) (51/50)-2*twoNeuron 0 1|=3/50 := by
  norm_num [twoNeuron]

theorem exact_l2_slope_attained :
    twoNeuron (1/2) 2-twoNeuron 0 1=5/4 ∧
    ((1/2:ℝ)-0)^2+(2-1)^2=5/4 := by norm_num [twoNeuron]

theorem exact_l2_gain_necessary (L : ℝ) (hL : 0 ≤ L)
    (hgain : ∀ x y xb yb : ℝ,
      |twoNeuron x y-twoNeuron xb yb| ≤ L*Real.sqrt ((x-xb)^2+(y-yb)^2)) :
    Real.sqrt (5/4) ≤ L := by
  have h := hgain (1/2) 2 0 1
  rw [exact_l2_slope_attained.1,exact_l2_slope_attained.2] at h
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 5/4)] at h
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5/4)
  have hp : (0:ℝ) < Real.sqrt (5/4) := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

theorem relu_incremental_sector (x y : ℝ) :
    0 ≤ (max x 0-max y 0)*((x-y)-(max x 0-max y 0)) := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [max_eq_left hx,max_eq_left hy]; ring_nf; exact le_rfl
  · rw [max_eq_left hx,max_eq_right (le_of_not_ge hy)]
    nlinarith
  · rw [max_eq_right (le_of_not_ge hx),max_eq_left hy]
    nlinarith
  · rw [max_eq_right (le_of_not_ge hx),max_eq_right (le_of_not_ge hy)]
    norm_num

theorem diagonal_relu_incremental_qc {ι : Type*} [Fintype ι]
    (weight x y : ι → ℝ) (hw : ∀ i, 0 ≤ weight i) :
    0 ≤ ∑ i, 2*weight i*(max (x i) 0-max (y i) 0)*
      ((x i-y i)-(max (x i) 0-max (y i) 0)) := by
  apply Finset.sum_nonneg
  intro i _
  have h := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hw i))
    (relu_incremental_sector (x i) (y i))
  convert h using 1 <;> ring

theorem leaky_relu_incremental_sector (alpha x y : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    0 ≤ ((max x (alpha*x)-max y (alpha*y))-alpha*(x-y))*
      ((x-y)-(max x (alpha*x)-max y (alpha*y))) := by
  have hx : max x (alpha*x) = if 0 ≤ x then x else alpha*x := by
    split_ifs with h
    · exact max_eq_left (by nlinarith)
    · exact max_eq_right (by nlinarith)
  have hy : max y (alpha*y) = if 0 ≤ y then y else alpha*y := by
    split_ifs with h
    · exact max_eq_left (by nlinarith)
    · exact max_eq_right (by nlinarith)
  rw [hx,hy]
  by_cases hp : 0 ≤ x <;> by_cases hq : 0 ≤ y
  all_goals simp only [hp,hq,if_true,if_false]
  · have hid : (x-y-alpha*(x-y))*((x-y)-(x-y))=0 := by ring
    rw [hid]
  · have h₁ : 0 ≤ x*(1-alpha) := mul_nonneg hp (by linarith)
    have h₂ : 0 ≤ (-y)*(1-alpha) := mul_nonneg (by linarith) (by linarith)
    have hid : ((x-alpha*y)-alpha*(x-y))*((x-y)-(x-alpha*y))=
      (x*(1-alpha))*((-y)*(1-alpha)) := by ring
    rw [hid]; exact mul_nonneg h₁ h₂
  · have hid : ((alpha*x-y)-alpha*(x-y))*((x-y)-(alpha*x-y))=
      (y*(1-alpha))*((-x)*(1-alpha)) := by ring
    rw [hid]
    exact mul_nonneg (mul_nonneg hq (by linarith))
      (mul_nonneg (by linarith) (by linarith))
  · have hid : ((alpha*x-alpha*y)-alpha*(x-y))*((x-y)-(alpha*x-alpha*y))=0 := by ring
    rw [hid]

theorem affine_interval_center_radius {ι : Type*} [Fintype ι]
    (weight center radius input : ι → ℝ) (bias : ℝ)
    (hinput : ∀ i, |input i-center i| ≤ radius i) :
    |((∑ i, weight i*input i)+bias)-((∑ i, weight i*center i)+bias)| ≤
      ∑ i, |weight i| *radius i := by
  have hid : ((∑ i, weight i*input i)+bias)-((∑ i, weight i*center i)+bias)=
      ∑ i, weight i*(input i-center i) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid]
  calc
    _ ≤ ∑ i, |weight i*(input i-center i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |weight i| *radius i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hinput i) (abs_nonneg _)

theorem affine_interval_upper_attained {ι : Type*} [Fintype ι]
    (weight center radius : ι → ℝ) :
    (∑ i, weight i*(center i+(if 0 ≤ weight i then radius i else -radius i)))=
      (∑ i, weight i*center i)+(∑ i, |weight i| *radius i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rw [abs_of_nonneg h]; ring
  · rw [abs_of_nonpos (le_of_not_ge h)]; ring

theorem affine_interval_lower_attained {ι : Type*} [Fintype ι]
    (weight center radius : ι → ℝ) :
    (∑ i, weight i*(center i-(if 0 ≤ weight i then radius i else -radius i)))=
      (∑ i, weight i*center i)-(∑ i, |weight i| *radius i) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rw [abs_of_nonneg h]; ring
  · rw [abs_of_nonpos (le_of_not_ge h)]; ring

theorem relu_interval_sound (lo hi x : ℝ) (h : x ∈ Icc lo hi) :
    max x 0 ∈ Icc (max lo 0) (max hi 0) := by
  exact ⟨max_le_max h.1 le_rfl,max_le_max h.2 le_rfl⟩

theorem relu_triangle_general (lo hi x : ℝ) (hl : lo < 0) (hh : 0 < hi)
    (hx : x ∈ Icc lo hi) : max x 0 ≤ hi*(x-lo)/(hi-lo) := by
  have hd : 0 < hi-lo := by linarith
  apply (le_div_iff₀ hd).mpr
  by_cases hp : 0 ≤ x
  · rw [max_eq_left hp]
    have hm := mul_nonneg (by linarith : 0 ≤ -lo) (by linarith [hx.2] : 0 ≤ hi-x)
    nlinarith
  · rw [max_eq_right (le_of_not_ge hp)]
    have hm := mul_nonneg (le_of_lt hh) (by linarith [hx.1] : 0 ≤ x-lo)
    nlinarith

theorem relu_lower_line_general (slope x : ℝ) (hs : slope ∈ Icc 0 1) :
    slope*x ≤ max x 0 := by
  by_cases hp : 0 ≤ x
  · rw [max_eq_left hp]; nlinarith [hs.2]
  · rw [max_eq_right (le_of_not_ge hp)]; exact mul_nonpos_of_nonneg_of_nonpos hs.1 (le_of_not_ge hp)

theorem approximate_orthogonal_operator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Q Qhat : E →L[ℝ] E) (error : ℝ)
    (hQ : ‖Q‖ ≤ 1) (herror : ‖Qhat-Q‖ ≤ error) : ‖Qhat‖ ≤ 1+error := by
  calc ‖Qhat‖ = ‖Q+(Qhat-Q)‖ := by congr 1; abel
    _ ≤ ‖Q‖+‖Qhat-Q‖ := norm_add_le _ _
    _ ≤ 1+error := add_le_add hQ herror

theorem finite_stage_lipschitz_composition {X : Type*} [PseudoMetricSpace X]
    (stage : ℕ → X → X) (composite : ℕ → X → X) (K : ℝ≥0)
    (hstage : ∀ n, LipschitzWith K (stage n)) (hzero : composite 0=id)
    (hstep : ∀ n, composite (n+1)=stage n ∘ composite n) :
    ∀ n, LipschitzWith (K^n) (composite n) := by
  intro n
  induction n with
  | zero => rw [hzero,pow_zero]; exact LipschitzWith.id
  | succ n ih =>
    rw [hstep,pow_succ,mul_comm]
    exact (hstage n).comp ih

end SafeLearning.CompleteModulesNetworks
