import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeARGaussianAlgebra

def coefficient (k sigma : ℝ) (t j : ℕ) : ℝ :=
  if j<t then sigma*(1-k)^(t-1-j) else 0

def design (k sigma : ℝ) (T : ℕ) : Matrix (Fin (T+1)) (Fin T) ℝ :=
  fun t j => coefficient k sigma t.val j.val

def trueMean (k goal : ℝ) (t : ℕ) : ℝ := goal*(1-(1-k)^t)
def trueVariance (k sigma : ℝ) (t : ℕ) : ℝ :=
  sigma^2*∑i∈Finset.range t,(1-k)^(2*i)

def freshNoise {T : ℕ} (w : Fin T→ℝ) (t : ℕ) : ℝ :=
  ∑j:Fin T,if j.val=t then w j else 0

def trajectory {T : ℕ} (k goal sigma : ℝ) (w : Fin T→ℝ) : ℕ→ℝ
  | 0 => 0
  | t+1 => trajectory k goal sigma w t-k*(trajectory k goal sigma w t-goal)+
      sigma*freshNoise w t

theorem actual_fresh_noise_is_the_corresponding_finite_product_coordinate
    {T : ℕ} (w : Fin T→ℝ) (t : ℕ) (ht : t<T) : freshNoise w t=w ⟨t,ht⟩ := by
  unfold freshNoise
  have he : (fun j:Fin T=>if j.val=t then w j else 0)=
      (fun j:Fin T=>if j=⟨t,ht⟩ then w j else 0) := by
    funext j
    have hi : j.val=t ↔ j=⟨t,ht⟩ := by constructor <;> intro h;exact Fin.ext h;simpa [h]
    simp only [hi]
  rw [he]
  simp

theorem actual_trajectory_satisfies_the_literal_initial_condition_and_source_recursion
    {T : ℕ} (k goal sigma : ℝ) (w : Fin T→ℝ) :
    trajectory k goal sigma w 0=0 ∧ ∀t (ht:t<T),
      trajectory k goal sigma w (t+1)=trajectory k goal sigma w t-
        k*(trajectory k goal sigma w t-goal)+sigma*w ⟨t,ht⟩ := by
  refine ⟨rfl,?_⟩
  intro t ht
  rw [trajectory,actual_fresh_noise_is_the_corresponding_finite_product_coordinate w t ht]

theorem actual_impulse_coefficients_have_the_true_one_step_recursion
    (k sigma : ℝ) (t j : ℕ) :
    coefficient k sigma (t+1) j=(1-k)*coefficient k sigma t j+
      if j=t then sigma else 0 := by
  by_cases hlt : j<t
  · have hnew : j<t+1 := by omega
    have hneq : j≠t := by omega
    have hexp : t+1-1-j=(t-1-j)+1 := by omega
    simp only [coefficient,ite_eq_left hlt,ite_eq_left hnew,ite_eq_right hneq,hexp,pow_succ]
    ring
  · by_cases heq : j=t
    · subst j
      simp [coefficient]
    · have hnew : ¬j<t+1 := by omega
      simp only [coefficient,ite_eq_right hlt,ite_eq_right hnew,ite_eq_right heq,mul_zero,zero_add]

theorem actual_recursive_trajectory_is_exactly_the_finite_affine_noise_transformation
    {T : ℕ} (k goal sigma : ℝ) (w : Fin T→ℝ) (t : ℕ) :
    trajectory k goal sigma w t=trueMean k goal t+
      ∑j:Fin T,coefficient k sigma t j.val*w j := by
  induction t with
  | zero => simp [trajectory,trueMean,coefficient]
  | succ t ih =>
    simp only [trajectory,ih,actual_impulse_coefficients_have_the_true_one_step_recursion]
    simp only [add_mul,Finset.sum_add_distrib]
    have hf : (∑j:Fin T,(1-k)*coefficient k sigma t j.val*w j)=
        (1-k)*∑j:Fin T,coefficient k sigma t j.val*w j := by
      simp only [mul_assoc,Finset.mul_sum]
    have hi : (∑j:Fin T,(if j.val=t then sigma else 0)*w j)=sigma*freshNoise w t := by
      unfold freshNoise
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    rw [hf,hi]
    simp only [trueMean,pow_succ]
    ring

theorem actual_finite_vector_trajectory_is_the_affine_matrix_map
    {T : ℕ} (k goal sigma : ℝ) (w : Fin T→ℝ) :
    (fun t:Fin (T+1)=>trajectory k goal sigma w t.val)=
      (fun t:Fin (T+1)=>trueMean k goal t.val)+(design k sigma T)*ᵥw := by
  funext t
  exact actual_recursive_trajectory_is_exactly_the_finite_affine_noise_transformation
    k goal sigma w t.val

theorem finite_product_sum_truncates_to_the_actual_time_range
    (T t : ℕ) (ht:t≤T) (f : ℕ→ℝ) :
    (∑j:Fin T,if j.val<t then f j.val else 0)=∑j∈Finset.range t,f j := by
  change (∑j:Fin T,(fun i:ℕ=>if i<t then f i else 0) j.val)=_
  rw [Fin.sum_univ_eq_sum_range]
  have he : (∑j∈Finset.range t,if j<t then f j else 0)=
      ∑j∈Finset.range T,if j<t then f j else 0 := by
    apply Finset.sum_subset (Finset.range_mono ht)
    intro j hj hnot
    simp only [Finset.mem_range] at hnot
    simp [hnot]
  rw [←he]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]

theorem actual_squared_impulse_weights_sum_to_the_printed_variance
    (k sigma : ℝ) (T t : ℕ) (ht:t≤T) :
    (∑j:Fin T,(coefficient k sigma t j.val)^2)=trueVariance k sigma t := by
  calc
    (∑j:Fin T,(coefficient k sigma t j.val)^2)=
        ∑j:Fin T,if j.val<t then sigma^2*(1-k)^(2*(t-1-j.val)) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      unfold coefficient
      split_ifs
      · rw [mul_pow,←pow_mul]
        congr 2
        omega
      · simp
    _ =∑j∈Finset.range t,sigma^2*(1-k)^(2*(t-1-j)) :=
      finite_product_sum_truncates_to_the_actual_time_range T t ht
        (fun j=>sigma^2*(1-k)^(2*(t-1-j)))
    _ =trueVariance k sigma t := by
      unfold trueVariance
      rw [←Finset.mul_sum]
      congr 1
      exact Finset.sum_range_reflect (fun j=>(1-k)^(2*j)) t

theorem actual_earlier_and_later_impulse_weights_have_the_printed_covariance_product
    (k sigma : ℝ) (s t j : ℕ) (hst:s≤t) :
    coefficient k sigma s j*coefficient k sigma t j=
      (1-k)^(t-s)*(coefficient k sigma s j)^2 := by
  by_cases hjs : j<s
  · have hjt : j<t := lt_of_lt_of_le hjs hst
    have hexp : t-1-j=(t-s)+(s-1-j) := by omega
    simp only [coefficient,ite_eq_left hjs,ite_eq_left hjt,hexp,pow_add]
    ring
  · simp [coefficient,hjs]

theorem actual_affine_design_gram_is_the_true_temporal_covariance
    (k sigma : ℝ) (T : ℕ) (s t : Fin (T+1)) (hst:s.val≤t.val) :
    ((design k sigma T)*(design k sigma T)ᵀ) s t=
      (1-k)^(t.val-s.val)*trueVariance k sigma s.val := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,design,
    actual_earlier_and_later_impulse_weights_have_the_printed_covariance_product k sigma
      s.val t.val _ hst,←Finset.mul_sum]
  rw [actual_squared_impulse_weights_sum_to_the_printed_variance
    k sigma T s.val (by omega)]

theorem actual_zero_noise_scale_is_the_deterministic_mean_trajectory
    {T : ℕ} (k goal : ℝ) (w : Fin T→ℝ) (t : ℕ) :
    trajectory k goal 0 w t=trueMean k goal t := by
  rw [actual_recursive_trajectory_is_exactly_the_finite_affine_noise_transformation]
  simp [coefficient]

theorem actual_state_variance_is_nonnegative (k sigma : ℝ) (t : ℕ) :
    0≤trueVariance k sigma t := by
  unfold trueVariance
  apply mul_nonneg (sq_nonneg sigma)
  apply Finset.sum_nonneg
  intro i hi
  rw [show 2*i=i*2 by omega,pow_mul]
  exact sq_nonneg _

theorem actual_positive_time_and_nonzero_noise_have_strictly_positive_variance
    (k sigma : ℝ) (t : ℕ) (ht:0<t) (hsigma:sigma≠0) : 0<trueVariance k sigma t := by
  unfold trueVariance
  apply mul_pos (sq_pos_of_ne_zero hsigma)
  have hsum : (1:ℝ)≤∑i∈Finset.range t,(1-k)^(2*i) := by
    have hz : 0∈Finset.range t := Finset.mem_range.mpr ht
    have h := Finset.single_le_sum (f:=fun i=>(1-k)^(2*i)) (s:=Finset.range t)
      (fun i hi=>by rw [show 2*i=i*2 by omega,pow_mul];exact sq_nonneg _) hz
    simpa using h
  linarith

end SafeLearning.CompleteModulesLandscapeARGaussianAlgebra
