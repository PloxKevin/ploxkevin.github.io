import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators
namespace SafeLearning.CompleteAppliedTransientAmplification

abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
def dynamics : Matrix (Fin 2) (Fin 2) ℝ := !![1/2,10;0,1/2]
def nilpotentPart : Matrix (Fin 2) (Fin 2) ℝ := !![0,10;0,0]
def step (x : E) : E := WithLp.toLp 2 (dynamics *ᵥ (x : Fin 2 → ℝ))
def trajectory (initial : E) (n : ℕ) : E :=
  point ((1/2:ℝ)^n*(initial 0+20*(n:ℝ)*initial 1)) ((1/2:ℝ)^n*initial 1)

theorem actual_nilpotent_decomposition :
    dynamics=(1/2:ℝ) • (1:Matrix (Fin 2) (Fin 2) ℝ)+nilpotentPart ∧
    nilpotentPart^2=0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [dynamics,nilpotentPart,pow_two,Matrix.mul_apply,Fin.sum_univ_two]

theorem actual_matrix_power_all_times (n : ℕ) :
    dynamics^n=!![(1/2:ℝ)^n,20*(n:ℝ)*(1/2:ℝ)^n;0,(1/2:ℝ)^n] := by
  induction n with
  | zero => ext i j;fin_cases i <;> fin_cases j <;> norm_num
  | succ n ih =>
    rw [pow_succ,ih]
    ext i j;fin_cases i <;> fin_cases j <;>
      simp [dynamics,Matrix.mul_apply,Fin.sum_univ_two,pow_succ,Nat.cast_add] <;> ring

theorem actual_positive_time_binomial_formula (n : ℕ) (hn : 1≤n) :
    dynamics^n=(1/2:ℝ)^n • (1:Matrix (Fin 2) (Fin 2) ℝ)+
      ((n:ℝ)*(1/2:ℝ)^(n-1)) • nilpotentPart := by
  have hpow : (1/2:ℝ)^n=(1/2:ℝ)^(n-1)*(1/2) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  rw [actual_matrix_power_all_times]
  simp only [one_div,inv_pow] at hpow
  ext i j;fin_cases i <;> fin_cases j <;> simp [nilpotentPart] <;> rw [hpow] <;> ring

theorem actual_matrix_action (x : E) : step x=point (x 0/2+10*x 1) (x 1/2) := by
  ext i;fin_cases i <;> simp [step,point,dynamics,dotProduct,Fin.sum_univ_two] <;> ring

theorem actual_initial_and_recurrence (initial : E) :
    trajectory initial 0=initial ∧ ∀n,trajectory initial (n+1)=step (trajectory initial n) := by
  constructor
  · ext i;fin_cases i <;> simp [trajectory,point]
  · intro n;rw [actual_matrix_action]
    ext i;fin_cases i <;> simp [trajectory,point,pow_succ,Nat.cast_add] <;> ring

theorem actual_every_recurrence_is_this_trajectory (initial : E) (x : ℕ→E)
    (h0 : x 0=initial) (hnext : ∀n,x (n+1)=step (x n)) :
    ∀n,x n=trajectory initial n := by
  intro n;induction n with
  | zero => rw [h0,(actual_initial_and_recurrence initial).1]
  | succ n ih => rw [hnext,ih,(actual_initial_and_recurrence initial).2]

theorem actual_source_trajectory_formula (n : ℕ) (hn : 1≤n) :
    trajectory (point 0 1) n=point (10*(n:ℝ)*(1/2:ℝ)^(n-1)) ((1/2:ℝ)^n) := by
  have hpow : (1/2:ℝ)^n=(1/2:ℝ)^(n-1)*(1/2) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  simp only [one_div,inv_pow] at hpow
  ext i;fin_cases i <;> simp [trajectory,point] <;> rw [hpow] <;> ring

theorem actual_every_initial_trajectory_tends_to_zero (initial : E) :
    Tendsto (trajectory initial) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  have hn := tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  have hfirst : Tendsto (fun n:ℕ=>(1/2:ℝ)^n*(initial 0+20*(n:ℝ)*initial 1))
      atTop (𝓝 0) := by
    have h := (hp.mul_const (initial 0)).add (hn.const_mul (20*initial 1))
    convert h using 1 <;> (try ext n) <;> simp only [mul_zero,add_zero] <;> ring
  have hsecond := hp.mul_const (initial 1)
  have hf : Tendsto (fun n:ℕ=>![(1/2:ℝ)^n*(initial 0+20*(n:ℝ)*initial 1),
      (1/2:ℝ)^n*initial 1]) atTop (𝓝 (0:Fin 2→ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i;fin_cases i
    · simpa using hfirst
    · simpa using hsecond
  change Tendsto (fun n:ℕ=>WithLp.toLp 2 ![(1/2:ℝ)^n*(initial 0+20*(n:ℝ)*initial 1),
    (1/2:ℝ)^n*initial 1]) atTop (𝓝 (WithLp.toLp 2 (0:Fin 2→ℝ)))
  exact (PiLp.continuous_toLp (p:=2) (fun _ : Fin 2=>ℝ)).continuousAt.tendsto.comp hf

theorem actual_source_euclidean_transient_and_decimal :
    ‖trajectory (point 0 1) 0‖=1 ∧
    trajectory (point 0 1) 1=point 10 (1/2) ∧
    ‖trajectory (point 0 1) 1‖^2=401/4 ∧
    1<‖trajectory (point 0 1) 1‖ ∧
    (1001245/100000:ℝ)<‖trajectory (point 0 1) 1‖ ∧
    ‖trajectory (point 0 1) 1‖<(1001255/100000:ℝ) := by
  have hs : ‖point 10 (1/2)‖^2=(401/4:ℝ) := by
    have h := EuclideanSpace.real_norm_sq_eq (point 10 (1/2))
    norm_num [point,Fin.sum_univ_two] at h ⊢
    exact h
  have h0 : ‖point 0 1‖^2=(1:ℝ) := by
    simpa [point,Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq (point 0 1)
  have he : trajectory (point 0 1) 1=point 10 (1/2) := by
    ext i;fin_cases i <;> norm_num [trajectory,point]
  refine ⟨?_,he,?_,?_,?_,?_⟩
  · rw [(actual_initial_and_recurrence (point 0 1)).1]
    nlinarith [norm_nonneg (point 0 1)]
  all_goals rw [he]
  · exact hs
  all_goals nlinarith [norm_nonneg (point 10 (1/2))]

def weightedMagnitude (x : E) : ℝ := |x 0|+40*|x 1|

def actualLyapunovNorm : AddGroupNorm E where
  toFun := weightedMagnitude
  map_zero' := by simp [weightedMagnitude]
  add_le' := by
    intro x y
    change |x 0+y 0|+40*|x 1+y 1|≤(|x 0|+40*|x 1|)+(|y 0|+40*|y 1|)
    linarith [abs_add_le (x 0) (y 0),abs_add_le (x 1) (y 1)]
  neg' := by intro x;simp [weightedMagnitude]
  eq_zero_of_map_eq_zero' := by
    intro x hx
    dsimp [weightedMagnitude] at hx
    have h0 : x 0=0 := abs_eq_zero.mp (by linarith [abs_nonneg (x 0),abs_nonneg (x 1)])
    have h1 : x 1=0 := abs_eq_zero.mp (by linarith [abs_nonneg (x 0),abs_nonneg (x 1)])
    ext i;fin_cases i <;> simp [h0,h1]

theorem actual_lyapunov_norm_real_homogeneity (c : ℝ) (x : E) :
    actualLyapunovNorm (c • x)=|c| * actualLyapunovNorm x := by
  change |c*x 0|+40*|c*x 1|=|c| * (|x 0|+40*|x 1|)
  rw [abs_mul,abs_mul]
  ring

theorem actual_lyapunov_norm_contracts_every_step (x : E) :
    actualLyapunovNorm (step x)≤(3/4:ℝ)*actualLyapunovNorm x := by
  rw [actual_matrix_action]
  change |x 0/2+10*x 1|+40*|x 1/2|≤(3/4:ℝ)*(|x 0|+40*|x 1|)
  have h := abs_add_le (x 0/2) (10*x 1)
  norm_num [abs_div,abs_mul] at h ⊢
  linarith [abs_nonneg (x 0)]

end SafeLearning.CompleteAppliedTransientAmplification
