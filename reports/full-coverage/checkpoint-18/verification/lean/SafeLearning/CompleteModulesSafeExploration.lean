import SafeLearning.Modules
import SafeLearning.BookApplications

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SafeLearning.CompleteModulesSafeExploration

-- The no-crossing theorem uses the actual unsafe separating point and actual
-- Lipschitz regularity. It does not assume the desired unreachable-set result.
theorem no_lipschitz_jump_over_unsafe (f : ℝ → ℝ) (L level z a candidate lower : ℝ)
    (hL : 0 ≤ L) (hf : ∀ x y, |f x-f y| ≤ L*|x-y|)
    (hunsafe : f z < level) (hleft : a < z) (hconfidence : lower ≤ f a)
    (hcertificate : level ≤ lower-L*|a-candidate|) : candidate < z := by
  by_contra h
  have hright : z ≤ candidate := le_of_not_gt h
  have hsmall : |a-z| ≤ |a-candidate| := by
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    linarith
  have hactual := (abs_le.mp (hf a z)).2
  have hdist := mul_le_mul_of_nonneg_left hsmall hL
  linarith

theorem safeopt_never_crosses_unsafe (f : ℝ → ℝ) (safe : ℕ → Set ℝ)
    (lower : ℕ → ℝ → ℝ) (L level z : ℝ)
    (hL : 0 ≤ L) (hf : ∀ x y, |f x-f y| ≤ L*|x-y|)
    (hunsafe : f z < level) (hseed : ∀ x ∈ safe 0, x < z)
    (hconfidence : ∀ n x, lower n x ≤ f x)
    (hupdate : ∀ n, safe (n+1)=safe n ∪
      {x | ∃ a ∈ safe n, level ≤ lower n a-L*|a-x|}) :
    ∀ n x, x ∈ safe n → x < z := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    intro x hx
    rw [hupdate n] at hx
    rcases hx with hx | ⟨a,ha,hcertificate⟩
    · exact ih x hx
    · exact no_lipschitz_jump_over_unsafe f L level z a x (lower n a)
        hL hf hunsafe (ih a ha) (hconfidence n a) hcertificate

-- Asymmetric/heteroscedastic noise: only the positive-error envelope is used.
theorem asymmetric_noise_query_safety {X : Type*}
    (f : X → ℝ) (safe : ℕ → Set X) (query : ℕ → X)
    (observation noise upperNoise : ℕ → ℝ)
    (modulus : X → X → ℝ) (level : ℝ)
    (hseed : ∀ x ∈ safe 0, level ≤ f x)
    (hobs : ∀ n, observation n=f (query n)+noise n)
    (hnoise : ∀ n, noise n ≤ upperNoise n)
    (hregularity : ∀ a x, f a-modulus a x ≤ f x)
    (hquery : ∀ n, query n ∈ safe n)
    (hupdate : ∀ n, safe (n+1)=safe n ∪
      {x | level ≤ observation n-upperNoise n-modulus (query n) x}) :
    (∀ n x, x ∈ safe n → level ≤ f x) ∧ ∀ n, level ≤ f (query n) := by
  have hi : ∀ n x, x ∈ safe n → level ≤ f x := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n ih =>
      intro x hx
      rw [hupdate n] at hx
      rcases hx with hx | hx
      · exact ih x hx
      · have ho := hobs n
        have hn := hnoise n
        have hr := hregularity (query n) x
        change level ≤ observation n-upperNoise n-modulus (query n) x at hx
        linarith
  exact ⟨hi,fun n => hi n (query n) (hquery n)⟩

theorem general_modulus_safety_transfer (sourceValue actual observation error modulus level : ℝ)
    (hobs : observation-sourceValue ≤ error)
    (hregularity : sourceValue-modulus ≤ actual)
    (hgate : level ≤ observation-error-modulus) : level ≤ actual := by
  linarith

theorem holder_query_safety {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (safe : ℕ → Set X) (query : ℕ → X)
    (observation noise upperNoise : ℕ → ℝ) (C exponent level : ℝ)
    (hseed : ∀ x ∈ safe 0, level ≤ f x)
    (hobs : ∀ n, observation n=f (query n)+noise n)
    (hnoise : ∀ n, noise n ≤ upperNoise n)
    (hholder : ∀ a x, |f a-f x| ≤ C*(dist a x)^exponent)
    (hquery : ∀ n, query n ∈ safe n)
    (hupdate : ∀ n, safe (n+1)=safe n ∪
      {x | level ≤ observation n-upperNoise n-C*(dist (query n) x)^exponent}) :
    (∀ n x, x ∈ safe n → level ≤ f x) ∧ ∀ n, level ≤ f (query n) := by
  apply asymmetric_noise_query_safety f safe query observation noise upperNoise
    (fun a x => C*(dist a x)^exponent) level hseed hobs hnoise
  · intro a x
    have h := (abs_le.mp (hholder a x)).2
    linarith
  · exact hquery
  · exact hupdate

theorem lipschitz_query_safety {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (safe : ℕ → Set X) (query : ℕ → X)
    (observation noise upperNoise : ℕ → ℝ) (L level : ℝ)
    (hseed : ∀ x ∈ safe 0, level ≤ f x)
    (hobs : ∀ n, observation n=f (query n)+noise n)
    (hnoise : ∀ n, noise n ≤ upperNoise n)
    (hlipschitz : ∀ a x, |f a-f x| ≤ L*dist a x)
    (hquery : ∀ n, query n ∈ safe n)
    (hupdate : ∀ n, safe (n+1)=safe n ∪
      {x | level ≤ observation n-upperNoise n-L*dist (query n) x}) :
    (∀ n x, x ∈ safe n → level ≤ f x) ∧ ∀ n, level ≤ f (query n) := by
  apply asymmetric_noise_query_safety f safe query observation noise upperNoise
    (fun a x => L*dist a x) level hseed hobs hnoise
  · intro a x
    have h := (abs_le.mp (hlipschitz a x)).2
    linarith
  · exact hquery
  · exact hupdate

theorem downward_cone_is_lipschitz (measurement allowance L z : ℝ) (hL : 0 ≤ L) :
    ∀ x y, |(measurement-allowance-L*|x-z|)-
      (measurement-allowance-L*|y-z|)| ≤ L*|x-y| := by
  intro x y
  have hr : |(|x-z|)-(|y-z|)| ≤ |x-y| := by
    simpa only [sub_sub_sub_cancel_right] using abs_abs_sub_abs_le_abs_sub (x-z) (y-z)
  calc
    |(measurement-allowance-L*|x-z|)-(measurement-allowance-L*|y-z|)| =
      L*|(|x-z|)-(|y-z|)| := by
        rw [show (measurement-allowance-L*|x-z|)-
          (measurement-allowance-L*|y-z|) = -(L*(|x-z|-|y-z|)) by ring,
          abs_neg,abs_mul,abs_of_nonneg hL]
    _ ≤ L*|x-y| := mul_le_mul_of_nonneg_left hr hL

theorem downward_cone_matches_observation (measurement allowance L z : ℝ) :
    (measurement-allowance-L*|z-z|)+allowance=measurement := by
  simp

theorem beyond_cone_is_unsafe (measurement allowance L z level x : ℝ)
    (hL : 0 < L) (hbeyond : (measurement-allowance-level)/L < |x-z|) :
    measurement-allowance-L*|x-z| < level := by
  have h := (div_lt_iff₀ hL).mp hbeyond
  linarith

theorem holder_half_radius (C slack distance : ℝ) (hC : 0 < C)
    (hs : 0 ≤ slack) (hd : 0 ≤ distance) :
    C*Real.sqrt distance ≤ slack ↔ distance ≤ (slack/C)^2 := by
  have hn := Real.sqrt_nonneg distance
  have hsq := Real.sq_sqrt hd
  have hratio : 0 ≤ slack/C := div_nonneg hs (le_of_lt hC)
  rw [mul_comm C (Real.sqrt distance), ← le_div_iff₀ hC]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem holder_half_beats_lipschitz (C slack : ℝ) (hC : 0 < C) (hs : 0 ≤ slack) :
    (slack/C)^2 > slack/C ↔ C < slack := by
  have hr : 0 ≤ slack/C := div_nonneg hs (le_of_lt hC)
  constructor
  · intro h
    have ht : 1 < slack/C := by nlinarith
    have he := (lt_div_iff₀ hC).mp ht
    linarith
  · intro h
    have ht : 1 < slack/C := (lt_div_iff₀ hC).mpr (by linarith)
    nlinarith

theorem negative_slack_has_no_modulus_ball (C slack distance : ℝ)
    (hC : 0 ≤ C) (hs : slack < 0) : ¬ C*Real.sqrt distance ≤ slack := by
  have h := mul_nonneg hC (Real.sqrt_nonneg distance)
  linarith

theorem holder_radius_example :
    ((3/10:ℝ)/3)=1/10 ∧ ((3/10:ℝ)/3)^2=1/100 := by norm_num

theorem holder_general_radius (C slack distance exponent : ℝ)
    (hC : 0 < C) (hs : 0 ≤ slack) (hd : 0 ≤ distance) (ha : 0 < exponent) :
    C*(distance^exponent) ≤ slack ↔ distance ≤ (slack/C)^(1/exponent) := by
  rw [mul_comm C (distance^exponent), ← le_div_iff₀ hC, one_div]
  exact (Real.le_rpow_inv_iff_of_pos hd (div_nonneg hs (le_of_lt hC)) ha).symm

theorem trajectory_suffix_infimum (margin : ℝ → ℝ) (switchTime : ℝ)
    (ht : 0 ≤ switchTime) (hbounded : BddBelow (margin '' Ici 0)) :
    sInf (margin '' Ici 0) ≤ sInf (margin '' Ici switchTime) := by
  apply csInf_le_csInf hbounded
  · exact (show (Ici switchTime).Nonempty from ⟨switchTime,Set.self_mem_Ici⟩).image margin
  · apply Set.image_mono
    intro t ht'
    exact le_trans ht ht'

theorem flow_restart_trajectory_suffix {X : Type*}
    (flow : ℝ → X → X) (margin : X → ℝ) (initial : X) (switchTime : ℝ)
    (ht : 0 ≤ switchTime)
    (hflow : ∀ t s x, flow t (flow s x)=flow (t+s) x)
    (hsafe : ∀ t, 0 ≤ t → 0 ≤ margin (flow t initial)) :
    ∀ t, 0 ≤ t → 0 ≤ margin (flow t (flow switchTime initial)) := by
  intro t ht'
  rw [hflow]
  exact hsafe (t+switchTime) (add_nonneg ht' ht)

theorem nonnegative_budget_suffix (cost : ℝ → ℝ≥0∞) (switchTime : ℝ)
    (ht : 0 ≤ switchTime) :
    (∫⁻ t in Ici switchTime, cost t) ≤ ∫⁻ t in Ici 0, cost t := by
  apply lintegral_mono_set
  intro t ht'
  exact le_trans ht ht'

theorem pointwise_prefix_tail_composes (margin : ℝ → ℝ) (switchTime : ℝ)
    (hprefix : ∀ t ∈ Icc 0 switchTime, 0 ≤ margin t)
    (htail : ∀ t ∈ Ici switchTime, 0 ≤ margin t) :
    ∀ t ∈ Ici (0:ℝ), 0 ≤ margin t := by
  intro t ht
  by_cases h : t ≤ switchTime
  · exact hprefix t ⟨ht,h⟩
  · exact htail t (le_of_not_ge h)

theorem budget_prefix_tail_does_not_compose :
    (3/5:ℝ) ≤ 1 ∧ (3/5:ℝ) ≤ 1 ∧ 1 < (3/5:ℝ)+(3/5:ℝ) := by norm_num

end SafeLearning.CompleteModulesSafeExploration
