import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedBellman
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

def finiteMean {S : Type*} [Fintype S] (law : PMF S) (value : S → ℝ) : ℝ :=
  ∑ s, (law s).toReal*value s

theorem finite_weights_sum {S : Type*} [Fintype S] (law : PMF S) :
    (∑ s, (law s).toReal)=1 := by
  rw [← ENNReal.toReal_sum (fun s _ => law.apply_ne_top s)]
  have hh := law.tsum_coe
  rw [tsum_fintype] at hh
  rw [hh]
  norm_num

theorem finite_mean_difference_bound {S : Type*} [Fintype S]
    (law : PMF S) (V W : S → ℝ) (epsilon : ℝ)
    (h : ∀ s, |V s-W s|≤epsilon) :
    |finiteMean law V-finiteMean law W|≤epsilon := by
  have he : finiteMean law V-finiteMean law W=
      ∑ s,(law s).toReal*(V s-W s) := by
    unfold finiteMean
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs; ring
  rw [he]
  calc
    _≤∑ s, |(law s).toReal*(V s-W s)| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ s,(law s).toReal*epsilon := by
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left (h s) ENNReal.toReal_nonneg
    _=(∑ s,(law s).toReal)*epsilon := by rw [Finset.sum_mul]
    _=epsilon := by rw [finite_weights_sum,one_mul]

def valueNorm {S : Type*} [Fintype S] [Nonempty S] (V : S → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (fun s => |V s|)

theorem value_norm_pointwise {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (s : S) : |V s|≤valueNorm V := by
  classical
  exact Finset.le_sup' (fun s => |V s|) (Finset.mem_univ s)

theorem value_norm_le {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (bound : ℝ) (h : ∀ s,|V s|≤bound) : valueNorm V≤bound := by
  classical
  exact Finset.sup'_le Finset.univ_nonempty _ (fun s _ => h s)

theorem value_norm_nonnegative {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) : 0≤valueNorm V :=
  (abs_nonneg (V (Classical.choice inferInstance))).trans
    (value_norm_pointwise V _)

/-- This is the actual optimal Bellman backup: average over the normalized
transition law for each action, then maximize over the finite action set. -/
def bellman {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (transition : S → A → PMF S) (reward : S → A → ℝ) (gamma : ℝ)
    (V : S → ℝ) (s : S) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun a => reward s a+gamma*finiteMean (transition s a) V)

theorem bellman_pointwise_contraction {S A : Type*}
    [Fintype S] [Fintype A] [Nonempty A]
    (transition : S → A → PMF S) (reward : S → A → ℝ) (gamma epsilon : ℝ)
    (hg : 0≤gamma) (V W : S → ℝ) (h : ∀ s,|V s-W s|≤epsilon) (s : S) :
    |bellman transition reward gamma V s-bellman transition reward gamma W s|≤gamma*epsilon := by
  classical
  have hq : ∀ a, |(reward s a+gamma*finiteMean (transition s a) V)-
      (reward s a+gamma*finiteMean (transition s a) W)|≤gamma*epsilon := by
    intro a
    have he : (reward s a+gamma*finiteMean (transition s a) V)-
      (reward s a+gamma*finiteMean (transition s a) W)=
        gamma*(finiteMean (transition s a) V-finiteMean (transition s a) W) := by ring
    rw [he,abs_mul,abs_of_nonneg hg]
    exact mul_le_mul_of_nonneg_left (finite_mean_difference_bound (transition s a) V W epsilon h) hg
  have hupper : bellman transition reward gamma V s≤
      bellman transition reward gamma W s+gamma*epsilon := by
    apply Finset.sup'_le Finset.univ_nonempty
    intro a ha
    have ha' := Finset.le_sup' (fun b => reward s b+gamma*finiteMean (transition s b) W) ha
    change reward s a+gamma*finiteMean (transition s a) W≤bellman transition reward gamma W s at ha'
    have hh := (abs_le.mp (hq a)).2
    linarith
  have hlower : bellman transition reward gamma W s≤
      bellman transition reward gamma V s+gamma*epsilon := by
    apply Finset.sup'_le Finset.univ_nonempty
    intro a ha
    have ha' := Finset.le_sup' (fun b => reward s b+gamma*finiteMean (transition s b) V) ha
    change reward s a+gamma*finiteMean (transition s a) V≤bellman transition reward gamma V s at ha'
    have hh := (abs_le.mp (hq a)).1
    linarith
  rw [abs_le]
  constructor <;> linarith

theorem bellman_contraction {S A : Type*}
    [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (transition : S → A → PMF S) (reward : S → A → ℝ) (gamma : ℝ)
    (hg : 0≤gamma) (V W : S → ℝ) :
    valueNorm (fun s => bellman transition reward gamma V s-bellman transition reward gamma W s)
      ≤gamma*valueNorm (fun s => V s-W s) := by
  apply value_norm_le
  intro s
  exact bellman_pointwise_contraction transition reward gamma _ hg V W
    (value_norm_pointwise (fun s => V s-W s)) s

theorem bellman_residual_error {S A : Type*}
    [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (transition : S → A → PMF S) (reward : S → A → ℝ) (gamma residual : ℝ)
    (hg0 : 0≤gamma) (hg1 : gamma<1) (V fixed : S → ℝ)
    (hf : ∀ s,bellman transition reward gamma fixed s=fixed s)
    (hr : valueNorm (fun s => bellman transition reward gamma V s-V s)≤residual) :
    valueNorm (fun s => V s-fixed s)≤residual/(1-gamma) := by
  have he : valueNorm (fun s => V s-fixed s)≤
      residual+gamma*valueNorm (fun s => V s-fixed s) := by
    apply value_norm_le
    intro s
    have hres := (value_norm_pointwise
      (fun s => bellman transition reward gamma V s-V s) s).trans hr
    have hc := bellman_pointwise_contraction transition reward gamma _ hg0 V fixed
      (value_norm_pointwise (fun s => V s-fixed s)) s
    rw [hf s] at hc
    have htri := abs_add_le (V s-bellman transition reward gamma V s)
      (bellman transition reward gamma V s-fixed s)
    have hd : |V s-bellman transition reward gamma V s|=
        |bellman transition reward gamma V s-V s| := abs_sub_comm _ _
    rw [hd] at htri
    have hsum : V s-bellman transition reward gamma V s+
        (bellman transition reward gamma V s-fixed s)=V s-fixed s := by ring
    rw [hsum] at htri
    exact htri.trans (add_le_add hres hc)
  apply (le_div_iff₀ (by linarith : 0<1-gamma)).mpr
  nlinarith

theorem source_residual_bound {S A : Type*}
    [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (transition : S → A → PMF S) (reward : S → A → ℝ) (V fixed : S → ℝ)
    (hf : ∀ s,bellman transition reward (9/10) fixed s=fixed s)
    (hr : valueNorm (fun s => bellman transition reward (9/10) V s-V s)=3/100) :
    valueNorm (fun s => V s-fixed s)≤3/10 := by
  have hh := bellman_residual_error transition reward (9/10) (3/100)
    (by norm_num) (by norm_num) V fixed hf hr.le
  norm_num at hh
  exact hh

theorem source_tighter_residual_bound {S A : Type*}
    [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (transition : S → A → PMF S) (reward : S → A → ℝ) (V fixed : S → ℝ)
    (hf : ∀ s,bellman transition reward (9/10) fixed s=fixed s)
    (hr : valueNorm (fun s => bellman transition reward (9/10) V s-V s)≤1/100) :
    valueNorm (fun s => V s-fixed s)≤1/10 := by
  have hh := bellman_residual_error transition reward (9/10) (1/100)
    (by norm_num) (by norm_num) V fixed hf hr
  norm_num at hh
  exact hh

theorem value_norm_eq_sup_distance {S : Type*} [Fintype S] [Nonempty S]
    (V W : S → ℝ) : valueNorm (fun s => V s-W s)=dist V W := by
  apply le_antisymm
  · apply value_norm_le
    intro s
    simpa only [Real.dist_eq] using dist_le_pi_dist V W s
  · apply (dist_pi_le_iff (value_norm_nonnegative (fun s => V s-W s))).mpr
    intro s
    simpa only [Real.dist_eq] using value_norm_pointwise (fun s => V s-W s) s

theorem bellman_contracting {S A : Type*}
    [Fintype S] [Fintype A] [Nonempty A]
    (transition : S → A → PMF S) (reward : S → A → ℝ) (gamma : ℝ≥0)
    (hg : gamma<1) : ContractingWith gamma (bellman transition reward (gamma : ℝ)) := by
  refine ⟨hg,LipschitzWith.of_dist_le_mul ?_⟩
  intro V W
  apply (dist_pi_le_iff (mul_nonneg gamma.coe_nonneg dist_nonneg)).mpr
  intro s
  have hh := bellman_pointwise_contraction transition reward (gamma : ℝ)
    (dist V W) gamma.coe_nonneg V W (fun s => by
      simpa only [Real.dist_eq] using dist_le_pi_dist V W s) s
  simpa only [Real.dist_eq] using hh

theorem bellman_fixed_point_exists_unique_and_iteration_converges {S A : Type*}
    [Fintype S] [Fintype A] [Nonempty A]
    (transition : S → A → PMF S) (reward : S → A → ℝ) (gamma : ℝ≥0)
    (hg : gamma<1) (initial : S → ℝ) :
    ∃ fixed : S → ℝ,
      (∀ s,bellman transition reward (gamma : ℝ) fixed s=fixed s) ∧
      Filter.Tendsto (fun n : ℕ => (bellman transition reward (gamma : ℝ))^[n] initial)
        Filter.atTop (nhds fixed) ∧
      (∀ other : S → ℝ, (∀ s,bellman transition reward (gamma : ℝ) other s=other s) → other=fixed) := by
  have hc := bellman_contracting transition reward gamma hg
  obtain ⟨fixed,hfixed,hconvergence,herror⟩ := hc.exists_fixedPoint initial (edist_ne_top _ _)
  refine ⟨fixed,fun s => congrFun hfixed s,hconvergence,?_⟩
  intro other hother
  exact hc.fixedPoint_unique' (funext hother) hfixed

end SafeLearning.CompleteAppliedBellman
