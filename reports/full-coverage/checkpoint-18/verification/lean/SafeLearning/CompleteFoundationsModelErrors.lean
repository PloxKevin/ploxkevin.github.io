import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology NNReal

namespace SafeLearning.CompleteFoundationsModelErrors

def errorEnvelope (L e d₀ : ℝ) (n : ℕ) : ℝ :=
  L^n*d₀+e*∑ j ∈ Finset.range n,L^j

theorem error_envelope_step (L e d₀ : ℝ) (n : ℕ) :
    errorEnvelope L e d₀ (n+1)=L*errorEnvelope L e d₀ n+e := by
  have hgeom := geom_sum_mul L n
  simp only [errorEnvelope,Finset.sum_range_succ,pow_succ]
  linear_combination -e*hgeom

theorem recurrence_envelope (d : ℕ → ℝ) (L e : ℝ) (hL : 0≤L)
    (hrec : ∀ n,d (n+1)≤L*d n+e) (n : ℕ) :
    d n≤errorEnvelope L e (d 0) n := by
  induction n with
  | zero => simp [errorEnvelope]
  | succ n ih =>
    rw [error_envelope_step]
    exact (hrec n).trans (add_le_add (mul_le_mul_of_nonneg_left ih hL) (le_refl e))

theorem envelope_geometric_form (L e d₀ : ℝ) (hL : L≠1) (n : ℕ) :
    errorEnvelope L e d₀ n=L^n*d₀+e*(L^n-1)/(L-1) := by
  rw [errorEnvelope,geom_sum_eq hL]
  ring

theorem envelope_unit_factor (e d₀ : ℝ) (n : ℕ) :
    errorEnvelope 1 e d₀ n=d₀+e*n := by simp [errorEnvelope]

theorem model_distance_recurrence {X : Type*} [PseudoMetricSpace X]
    (F H : X → X) (L : ℝ≥0) (e : ℝ)
    (hF : LipschitzWith L F) (hmodel : ∀ x,dist (F x) (H x)≤e)
    (x₀ y₀ : X) (n : ℕ) :
    dist (F^[n+1] x₀) (H^[n+1] y₀)≤(L : ℝ)*dist (F^[n] x₀) (H^[n] y₀)+e := by
  rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
  exact (dist_triangle _ (F (H^[n] y₀)) _).trans
    (add_le_add (hF.dist_le_mul _ _) (hmodel _))

theorem model_distance_envelope {X : Type*} [PseudoMetricSpace X]
    (F H : X → X) (L : ℝ≥0) (e : ℝ)
    (hF : LipschitzWith L F) (hmodel : ∀ x,dist (F x) (H x)≤e)
    (x₀ y₀ : X) (n : ℕ) :
    dist (F^[n] x₀) (H^[n] y₀)≤errorEnvelope (L : ℝ) e (dist x₀ y₀) n := by
  simpa using recurrence_envelope (fun n => dist (F^[n] x₀) (H^[n] y₀))
    (L : ℝ) e L.coe_nonneg (model_distance_recurrence F H L e hF hmodel x₀ y₀) n

theorem affine_iterations (L e x₀ : ℝ) (n : ℕ) :
    (fun x : ℝ => L*x+e)^[n] x₀=errorEnvelope L e x₀ n := by
  induction n with
  | zero => simp [errorEnvelope]
  | succ n ih => rw [Function.iterate_succ_apply',ih,error_envelope_step]

theorem zero_predictor_iterations (L : ℝ) (n : ℕ) :
    (fun x : ℝ => L*x)^[n] 0=0 := by
  simpa using affine_iterations L 0 0 n

theorem nonnegative_error_envelope (L e : ℝ) (hL : 0≤L) (he : 0≤e) (n : ℕ) :
    0≤errorEnvelope L e 0 n := by
  simp only [errorEnvelope,mul_zero,zero_add]
  exact mul_nonneg he (Finset.sum_nonneg (fun j _ => pow_nonneg hL j))

theorem actual_affine_model_attains_bound (L e : ℝ) (hL : 0≤L) (he : 0≤e) (n : ℕ) :
    dist ((fun x : ℝ => L*x+e)^[n] 0) ((fun x : ℝ => L*x)^[n] 0)=
      errorEnvelope L e 0 n := by
  rw [affine_iterations,zero_predictor_iterations,Real.dist_eq,sub_zero,
    abs_of_nonneg (nonnegative_error_envelope L e hL he n)]

theorem affine_model_one_step_error (L e : ℝ) (he : 0≤e) (x : ℝ) :
    dist (L*x+e) (L*x)=e := by
  rw [Real.dist_eq]
  simpa using abs_of_nonneg he

theorem affine_model_lipschitz (L : ℝ≥0) (e : ℝ) :
    LipschitzWith L (fun x : ℝ => (L : ℝ)*x+e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.dist_eq,show (L : ℝ)*x+e-((L : ℝ)*y+e)=(L : ℝ)*(x-y) by ring,
    abs_mul,abs_of_nonneg L.coe_nonneg]

theorem exact_source_error_envelope (n : ℕ) :
    errorEnvelope (6/5) (1/100) 0 n=(1/20 : ℝ)*((6/5)^n-1) := by
  rw [envelope_geometric_form _ _ _ (by norm_num)]
  ring

theorem source_error_numbers :
    errorEnvelope (6/5) (1/100) 0 5=74416/1000000 ∧
    errorEnvelope (6/5) (1/100) 0 6=992992/10000000 ∧
    (6/5 : ℝ)^5=248832/100000 ∧ (6/5 : ℝ)^6=2985984/1000000 := by
  norm_num [errorEnvelope,Finset.sum_range_succ]

theorem source_true_margin_bounds {X : Type*} [PseudoMetricSpace X]
    (x y : ℕ → X) (h : X → ℝ) (hh : LipschitzWith 2 h)
    (hstart : x 0=y 0)
    (hrec : ∀ n,dist (x (n+1)) (y (n+1))≤(6/5)*dist (x n) (y n)+1/100)
    (hpred : ∀ n,h (y n)=1/5) :
    51168/1000000≤h (x 5) ∧ 14016/10000000≤h (x 6) := by
  have hzero : dist (x 0) (y 0)=0 := by rw [hstart,dist_self]
  have hd₅ := SafeLearning.PrimersFoundations.state_error_recurrence
    (fun n => dist (x n) (y n)) hzero hrec 5
  have hd₆ := SafeLearning.PrimersFoundations.state_error_recurrence
    (fun n => dist (x n) (y n)) hzero hrec 6
  have hs₅ := hh.dist_le_mul (y 5) (x 5)
  have hs₆ := hh.dist_le_mul (y 6) (x 6)
  rw [Real.dist_eq,hpred 5,dist_comm] at hs₅
  rw [Real.dist_eq,hpred 6,dist_comm] at hs₆
  norm_num at hd₅ hd₆ hs₅ hs₆
  have ht₅ := le_abs_self ((1/5 : ℝ)-h (x 5))
  have ht₆ := le_abs_self ((1/5 : ℝ)-h (x 6))
  constructor <;> linarith

theorem source_bounds_nonnegative :
    (0 : ℝ)<51168/1000000 ∧ (0 : ℝ)<14016/10000000 ∧
    (1/100 : ℝ)<errorEnvelope (6/5) (1/100) 0 5 := by
  norm_num [errorEnvelope,Finset.sum_range_succ]

theorem source_teaching_ten_step_bound :
    errorEnvelope (11/10) (1/100) 0 10=15937424601/100000000000 ∧
    errorEnvelope (11/10) (1/100) 0 10≤159375/1000000 ∧
    159374/1000000<errorEnvelope (11/10) (1/100) 0 10 := by
  norm_num [errorEnvelope,Finset.sum_range_succ]

end SafeLearning.CompleteFoundationsModelErrors
