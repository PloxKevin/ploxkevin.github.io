import SafeLearning.CompleteAppliedComparisonFilter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteAppliedComparisonFilterNumbers
open CompleteAppliedComparisonFilter

theorem actual_differentiable_source_subsolution_has_the_true_bound
    (v : ℝ → ℝ) (h0 : v 0=3)
    (hd : ∀ t : ℝ,0 ≤ t → DifferentiableAt ℝ v t)
    (hb : ∀ t : ℝ,0 ≤ t → deriv v t ≤ -2*v t+1) :
    ∀ t : ℝ,0 ≤ t → v t ≤ comparison t := by
  intro t ht
  exact actual_every_classical_subsolution_obeys_the_comparison v (deriv v) t
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt) h0
    (fun s hs => (hd s hs.1).hasDerivAt) (fun s hs => hb s hs.1) t ⟨ht,le_rfl⟩

theorem actual_source_barrier_derivative_and_Lie_quantities (x u : ℝ) :
    HasDerivAt (fun y : ℝ => 1-y) (-1) x ∧
    (-1:ℝ)*0=0 ∧ (-1:ℝ)*1=-1 ∧
    ((-1:ℝ)*u+2*(1-x) ≥ 0 ↔ u ≤ 2*(1-x)) := by
  refine ⟨by simpa using (hasDerivAt_id x).const_sub 1,by norm_num,by norm_num,?_⟩
  constructor <;> intro h <;> linarith

def exponentialPolynomial (x : ℝ) : ℝ := ∑ i∈Finset.range 20,x^i/(i.factorial:ℝ)

theorem actual_exponential_degree_twenty_error (x : ℝ) (hx : |x| ≤ 2) :
    |Real.exp x-exponentialPolynomial x| ≤ 1/1000000000000 := by
  have hr : ‖(x:ℂ)‖/(Nat.succ 20:ℝ) ≤ 1/2 := by
    simp only [Complex.norm_real,Real.norm_eq_abs]
    norm_num
    linarith
  have hb := Complex.exp_bound' hr
  have h : |Real.exp x-exponentialPolynomial x| ≤
      |x|^20/(Nat.factorial 20:ℝ)*2 := by
    dsimp only [exponentialPolynomial]
    convert hb using 1 <;> norm_cast
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 20
  norm_num [Nat.factorial] at h hp
  nlinarith

theorem actual_three_source_exponential_enclosures :
    (13533528323/100000000000:ℝ) < Real.exp (-2) ∧
    Real.exp (-2) < 13533528324/100000000000 ∧
    (36787944116/100000000000:ℝ) < Real.exp (-1) ∧
    Real.exp (-1) < 36787944118/100000000000 ∧
    (271828182845/100000000000:ℝ) < Real.exp 1 ∧
    Real.exp 1 < 271828182847/100000000000 := by
  have h2 := actual_exponential_degree_twenty_error (-2) (by norm_num)
  have hn1 := actual_exponential_degree_twenty_error (-1) (by norm_num)
  have h1 := actual_exponential_degree_twenty_error 1 (by norm_num)
  norm_num [exponentialPolynomial,Finset.sum_range_succ,Nat.factorial,abs_le] at h2 hn1 h1
  constructor
  · linarith [h2.1]
  constructor
  · linarith [h2.2]
  constructor
  · linarith [hn1.1]
  constructor
  · linarith [hn1.2]
  constructor <;> linarith [h1.1,h1.2]

theorem actual_comparison_at_one_and_valid_rounded_upper_bound :
    |comparison 1-(838:ℝ)/1000| ≤ 1/2000 ∧
    (838:ℝ)/1000 < comparison 1 ∧ comparison 1 < (839:ℝ)/1000 := by
  obtain ⟨hl,hu,_⟩ := actual_three_source_exponential_enclosures
  norm_num [comparison,abs_le]
  constructor
  · constructor <;> linarith
  constructor <;> linarith

theorem actual_comparison_is_an_admitted_counterexample_to_the_printed_bound :
    comparison 0=3 ∧
    (∀ t : ℝ,HasDerivAt comparison (-2*comparison t+1) t) ∧
    ¬comparison 1 ≤ (838:ℝ)/1000 := by
  exact ⟨(actual_comparison_initial_and_ODE 0).1,
    fun t => (actual_comparison_initial_and_ODE t).2,
    not_le.mpr actual_comparison_at_one_and_valid_rounded_upper_bound.2.1⟩

def difference (t : ℝ) : ℝ := 1-t-Real.exp (-2*t)

theorem actual_source_barrier_difference_is_concave :
    ConcaveOn ℝ (Icc (0:ℝ) (1/2)) difference := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have h := convexOn_exp.2 (mem_univ (-2*x)) (mem_univ (-2*y)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  rw [show a*(-2*x)+b*(-2*y)=-2*(a*x+b*y) by ring] at h
  dsimp only [difference]
  have hlinear : a*(1-x)+b*(1-y)=1-(a*x+b*y) := by
    nlinarith [hab]
  nlinarith

theorem actual_endpoint_and_post_switch_factor_rounding :
    difference 0=0 ∧
    (0:ℝ) < difference (1/2) ∧
    |difference (1/2)-(132:ℝ)/1000| ≤ 1/2000 ∧
    difference (1/2) ≠ (132:ℝ)/1000 ∧
    |(1/2)*Real.exp 1-(1359:ℝ)/1000| ≤ 1/2000 ∧
    (1359:ℝ)/1000 < (1/2)*Real.exp 1 ∧
    1 ≤ (1/2)*Real.exp 1 := by
  obtain ⟨_,_,hnl,hnu,hl,hu⟩ := actual_three_source_exponential_enclosures
  refine ⟨by norm_num [difference],?_,?_,?_,?_,?_,?_⟩
  · norm_num [difference];linarith
  · norm_num [difference,abs_le];constructor <;> linarith
  · norm_num [difference];intro he;linarith
  · rw [abs_le];constructor <;> linarith
  · linarith
  · linarith

theorem actual_concavity_proves_the_pre_switch_bound (t : ℝ)
    (ht : t∈Icc (0:ℝ) (1/2)) : Real.exp (-2*t) ≤ 1-t := by
  have h := actual_source_barrier_difference_is_concave.2
    (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/2))
    (by norm_num : (1/2:ℝ)∈Icc (0:ℝ) (1/2))
    (show 0 ≤ 1-2*t by linarith [ht.2])
    (show 0 ≤ 2*t by linarith [ht.1])
    (show (1-2*t)+(2*t)=1 by ring)
  simp only [smul_eq_mul] at h
  rw [show (1-2*t)*0+(2*t)*(1/2)=t by ring,
    actual_endpoint_and_post_switch_factor_rounding.1,mul_zero,zero_add] at h
  have hn := mul_nonneg (by linarith [ht.1] : 0 ≤ 2*t)
    actual_endpoint_and_post_switch_factor_rounding.2.1.le
  dsimp only [difference] at h hn
  linarith

theorem actual_post_switch_exact_barrier_factor (t : ℝ) (ht : 1/2 < t) :
    1-filteredTrajectory t=(1/2)*Real.exp 1*Real.exp (-2*t) ∧
    Real.exp (-2*t) ≤ 1-filteredTrajectory t := by
  have he : Real.exp (-2*(t-1/2))=Real.exp 1*Real.exp (-2*t) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hs : 1-filteredTrajectory t=(1/2)*Real.exp 1*Real.exp (-2*t) := by
    dsimp only [filteredTrajectory]
    rw [if_neg (not_le.mpr ht),he]
    ring
  refine ⟨hs,?_⟩
  rw [hs]
  nlinarith [Real.exp_pos (-2*t),actual_endpoint_and_post_switch_factor_rounding.2.2.2.2.2.2]

end SafeLearning.CompleteAppliedComparisonFilterNumbers
