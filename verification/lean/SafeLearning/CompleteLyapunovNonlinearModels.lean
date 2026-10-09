import SafeLearning.CompleteCompactLyapunov
import SafeLearning.CompleteLyapunovCounterexample

namespace SafeLearning.CompleteLyapunovNonlinearModels

noncomputable section
open Set Filter
open scoped Topology

def nonlinearMap (x : ℝ) : ℝ := x-x^3

theorem actual_nonlinear_decrement (x : ℝ) :
    (nonlinearMap x)^2-x^2=x^4*(x^2-2) := by unfold nonlinearMap; ring

theorem actual_nonlinear_strict_decrease (x : ℝ) (hx : x ≠ 0) (hregion : x^2 < 2) :
    (nonlinearMap x)^2 < x^2 := by
  have hp : 0 < x^4 := by
    simpa only [← pow_mul] using sq_pos_of_pos (sq_pos_of_ne_zero hx)
  have hd : (nonlinearMap x)^2-x^2 < 0 := by
    rw [actual_nonlinear_decrement]
    exact mul_neg_of_pos_of_neg hp (by linarith)
  linarith

theorem actual_nonlinear_strict_decrease_region (x : ℝ) :
    (nonlinearMap x)^2 < x^2 ↔ 0 < |x| ∧ |x| < Real.sqrt 2 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  constructor
  · intro hd
    have hn : x ≠ 0 := by intro hz; norm_num [hz,nonlinearMap] at hd
    have hsq : x^2 < 2 := by
      by_contra hbad
      have hh : 0 ≤ x^4*(x^2-2) :=
        mul_nonneg (by positivity) (by linarith)
      rw [← actual_nonlinear_decrement] at hh
      linarith
    refine ⟨abs_pos.mpr hn,?_⟩
    apply (sq_lt_sq₀ (abs_nonneg x) (Real.sqrt_nonneg 2)).mp
    simpa only [sq_abs,hs] using hsq
  · rintro ⟨hn,ha⟩
    apply actual_nonlinear_strict_decrease x (abs_pos.mp hn)
    have h := (sq_lt_sq₀ (abs_nonneg x) (Real.sqrt_nonneg 2)).mpr ha
    simpa only [sq_abs,hs] using h

theorem actual_nonlinear_boundary_two_cycle :
    nonlinearMap (Real.sqrt 2) = -Real.sqrt 2 ∧
    nonlinearMap (-Real.sqrt 2) = Real.sqrt 2 ∧
    (Real.sqrt 2)^2 = 2 ∧ (-Real.sqrt 2)^2 = 2 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 2)^3=2*Real.sqrt 2 := by rw [pow_succ,hs]
  unfold nonlinearMap
  constructor
  · linarith
  · constructor
    · simp only [neg_pow,Odd.neg_one_pow (by decide : Odd 3),neg_one_mul]
      linarith
    · exact ⟨hs,by simpa using hs⟩

theorem actual_nonlinear_strict_sublevels_iff (c : ℝ) (hc : 0 < c) :
    (∀ x : ℝ, x^2 ≤ c → x ≠ 0 → (nonlinearMap x)^2 < x^2) ↔ c < 2 := by
  constructor
  · intro h
    by_contra hbad
    have hbound : 2 ≤ c := le_of_not_gt hbad
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
    have hd := h (Real.sqrt 2) (by simpa [hs] using hbound) hn
    rw [actual_nonlinear_boundary_two_cycle.1] at hd
    simpa using hd
  · intro h x hx hne
    exact actual_nonlinear_strict_decrease x hne (hx.trans_lt h)

theorem actual_nonlinear_uniform_decrement_on_positive_slice
    (x lower : ℝ) (hlower : 0 ≤ lower) (hlo : lower ≤ x^2) (hhi : x^2 ≤ 1) :
    (nonlinearMap x)^2-x^2 ≤ -lower^2 := by
  rw [actual_nonlinear_decrement]
  have hs : lower^2 ≤ x^4 := by
    nlinarith [sq_nonneg (x^2-lower)]
  have hm := mul_nonneg (sq_nonneg (x^2)) (show 0 ≤ 1-x^2 by linarith)
  nlinarith

theorem actual_nonlinear_sublevel_one_convergence (trajectory : ℕ → ℝ)
    (hi : (trajectory 0)^2 ≤ 1)
    (hstep : ∀ n, trajectory (n+1)=nonlinearMap (trajectory n)) :
    (∀ n, (trajectory n)^2 ≤ 1) ∧
    Tendsto trajectory atTop (𝓝 0) ∧
    Tendsto (fun n => (trajectory n)^2) atTop (𝓝 0) := by
  have hF : Continuous nonlinearMap := by unfold nonlinearMap; fun_prop
  have hV : Continuous (fun x : ℝ => x^2) := by fun_prop
  have hF0 : nonlinearMap 0=0 := by norm_num [nonlinearMap]
  have hdec : ∀ x : ℝ, x^2 ≤ 1 → x ≠ 0 → (nonlinearMap x)^2 < x^2 := by
    intro x hx hn
    exact actual_nonlinear_strict_decrease x hn (by linarith)
  have hcompact := CompleteLyapunovCounterexample.all_square_sublevels_compact 1
  have hinv := CompleteCompactLyapunov.sublevel_forward_invariance nonlinearMap
    (fun x : ℝ => x^2) trajectory 1 hF0 hstep hi hdec
  have ht := CompleteCompactLyapunov.compact_strict_lyapunov_convergence nonlinearMap
    (fun x : ℝ => x^2) trajectory 1 hF hV hcompact sq_nonneg hF0 hstep hi hdec
  refine ⟨hinv,ht,?_⟩
  simpa using ht.pow 2

theorem actual_relative_policy_error_one_step (error : ℝ → ℝ) (x : ℝ)
    (he : |error x| ≤ (1 / 10 : ℝ)*|x|) :
    |x+(-(1 / 2 : ℝ)*x+error x)| ≤ (3 / 5 : ℝ)*|x| := by
  have heq : x+(-(1 / 2 : ℝ)*x+error x)=(1 / 2 : ℝ)*x+error x := by ring
  rw [heq]
  calc
    _ ≤ |(1 / 2 : ℝ)*x|+|error x| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul]; norm_num; linarith

theorem actual_relative_policy_error_geometric_bound (error : ℝ → ℝ)
    (he : ∀ x, |error x| ≤ (1 / 10 : ℝ)*|x|) (trajectory : ℕ → ℝ)
    (hstep : ∀ n, trajectory (n+1)=trajectory n+(-(1 / 2 : ℝ)*trajectory n+error (trajectory n))) :
    ∀ n, |trajectory n| ≤ (3 / 5 : ℝ)^n*|trajectory 0| := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hstep]
    calc
      _ ≤ (3 / 5 : ℝ)*|trajectory n| := actual_relative_policy_error_one_step error _ (he _)
      _ ≤ (3 / 5 : ℝ)*((3 / 5 : ℝ)^n*|trajectory 0|) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem actual_relative_policy_error_converges_to_zero (error : ℝ → ℝ)
    (he : ∀ x, |error x| ≤ (1 / 10 : ℝ)*|x|) (trajectory : ℕ → ℝ)
    (hstep : ∀ n, trajectory (n+1)=trajectory n+(-(1 / 2 : ℝ)*trajectory n+error (trajectory n))) :
    Tendsto trajectory atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤3/5) (by norm_num : (3/5:ℝ)<1)
  have hb : Tendsto (fun n : ℕ => (3 / 5 : ℝ)^n*|trajectory 0|) atTop (𝓝 0) := by
    simpa using hpow.mul_const |trajectory 0|
  have habs := squeeze_zero (fun n => abs_nonneg (trajectory n))
    (actual_relative_policy_error_geometric_bound error he trajectory hstep) hb
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

theorem actual_relative_policy_error_square_decrement (error : ℝ → ℝ) (x : ℝ)
    (he : |error x| ≤ (1 / 10 : ℝ)*|x|) :
    (x+(-(1 / 2 : ℝ)*x+error x))^2 ≤ (9 / 25 : ℝ)*x^2 ∧
    (x+(-(1 / 2 : ℝ)*x+error x))^2-x^2 ≤ -(16 / 25 : ℝ)*x^2 := by
  have h := actual_relative_policy_error_one_step error x he
  have hh := (sq_le_sq₀ (abs_nonneg (x+(-(1 / 2 : ℝ)*x+error x)))
    (show 0 ≤ (3 / 5 : ℝ)*|x| by positivity)).mpr h
  simp only [mul_pow, sq_abs] at hh
  constructor <;> nlinarith

theorem actual_absolute_policy_error_nonzero_equilibrium :
    (∀ x : ℝ, |(1 / 10 : ℝ)| ≤ 1 / 10) ∧
    (∀ n : ℕ, (1 / 5 : ℝ)=(1 / 5)+(-(1 / 2 : ℝ)*(1 / 5)+1 / 10)) ∧
    ¬Tendsto (fun _ : ℕ => (1 / 5 : ℝ)) atTop (𝓝 0) := by
  refine ⟨by intro x; norm_num,by intro n; norm_num,?_⟩
  intro h
  have he := tendsto_nhds_unique
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 5 : ℝ)) atTop (𝓝 (1 / 5))) h
  norm_num at he

end
end SafeLearning.CompleteLyapunovNonlinearModels
