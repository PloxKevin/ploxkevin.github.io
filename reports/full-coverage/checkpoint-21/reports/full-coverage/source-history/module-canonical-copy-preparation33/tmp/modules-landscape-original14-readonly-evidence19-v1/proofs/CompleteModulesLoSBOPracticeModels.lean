import SafeLearning.CompleteModulesLoSBOPracticeNumbers
import SafeLearning.CompleteModulesSafeExploration

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLoSBOPracticeModels
open SafeLearning.CompleteModulesLoSBOPracticeNumbers

def actualAccumulated (seed : Set ℝ) (query observation : ℕ → ℝ)
    (allowance slope threshold : ℝ) (n : ℕ) : Set ℝ :=
  seed ∪ {x | ∃ i < n, x ∈ actualCone (query i) (observation i) allowance slope threshold}

theorem actual_accumulated_history_retains_the_seed_and_every_earlier_certificate
    (seed : Set ℝ) (query observation : ℕ → ℝ) (allowance slope threshold : ℝ) :
    seed ⊆ actualAccumulated seed query observation allowance slope threshold 0 ∧
      ∀ n, actualAccumulated seed query observation allowance slope threshold n ⊆
        actualAccumulated seed query observation allowance slope threshold (n+1) := by
  constructor
  · exact fun _ h => Or.inl h
  · intro n x hx
    rcases hx with hx | ⟨i,hi,hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨i,Nat.lt_succ_of_lt hi,hx⟩

theorem actual_all_accumulated_points_and_every_member_query_are_safe_for_any_scores
    (f : ℝ → ℝ) (seed : Set ℝ) (query observation noise : ℕ → ℝ)
    (allowance slope threshold : ℝ)
    (hseed : ∀ x ∈ seed, threshold ≤ f x)
    (hobs : ∀ i, observation i=f (query i)+noise i)
    (hnoise : ∀ i, |noise i| ≤ allowance)
    (hlip : ∀ x y, |f x-f y| ≤ slope*|x-y|) :
    (∀ n x, x ∈ actualAccumulated seed query observation allowance slope threshold n → threshold ≤ f x) ∧
      ∀ choice : ℕ → ℝ,
        (∀ n, choice n ∈ actualAccumulated seed query observation allowance slope threshold n) →
        ∀ n, threshold ≤ f (choice n) := by
  have hs : ∀ n x, x ∈ actualAccumulated seed query observation allowance slope threshold n → threshold ≤ f x := by
    intro n x hx
    rcases hx with hx | ⟨i,hi,hx⟩
    · exact hseed x hx
    · have hn := (abs_le.mp (hnoise i)).2
      have hl := (abs_le.mp (hlip (query i) x)).2
      change threshold ≤ observation i-allowance-slope*|x-query i| at hx
      rw [abs_sub_comm x (query i)] at hx
      have ho := hobs i
      linarith
  exact ⟨hs,fun choice hc n => hs n (choice n) (hc n)⟩

def actualBump (height x : ℝ) : ℝ := height*min x (1-x)

theorem actual_bump_matches_both_observations_and_has_both_literal_linear_pieces (height : ℝ) :
    actualBump height 0=0 ∧ actualBump height 1=0 ∧
      (∀ x ∈ Icc (0:ℝ) (1/2), actualBump height x=height*x) ∧
      (∀ x ∈ Icc (1/2:ℝ) 1, actualBump height x=height*(1-x)) := by
  refine ⟨by norm_num [actualBump],by norm_num [actualBump],?_,?_⟩
  · intro x hx
    rw [actualBump,min_eq_left (by linarith [hx.2])]
  · intro x hx
    rw [actualBump,min_eq_right (by linarith [hx.1])]

theorem actual_bump_has_the_stated_global_lipschitz_bound (height : ℝ) (hh : 0 ≤ height) :
    ∀ x y, |actualBump height x-actualBump height y| ≤ height*|x-y| := by
  intro x y
  have h := abs_min_sub_min_le_max x (1-x) y (1-y)
  have he : (1-x)-(1-y)=-(x-y) := by ring
  rw [he,abs_neg,max_self] at h
  calc
    |actualBump height x-actualBump height y|=height*|min x (1-x)-min y (1-y)| := by
      rw [actualBump,actualBump,←mul_sub,abs_mul,abs_of_nonneg hh]
    _ ≤ height*|x-y| := mul_le_mul_of_nonneg_left h hh

theorem actual_bump_smallest_global_lipschitz_constant_is_exactly_every_positive_height
    (height : ℝ) (hh : 0 < height) :
    IsLeast {constant : ℝ | 0 ≤ constant ∧ ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      |actualBump height x-actualBump height y| ≤ constant*|x-y|} height := by
  constructor
  · exact ⟨hh.le,fun x _ y _ => actual_bump_has_the_stated_global_lipschitz_bound height hh.le x y⟩
  · intro constant hc
    have h := hc.2 0 (by norm_num) (1/2) (by norm_num)
    norm_num [actualBump,abs_of_nonneg hh.le,abs_mul] at h
    linarith

theorem actual_source_undersized_lipschitz_claim_can_admit_an_unsafe_point :
    (∀ x y, |((3/10:ℝ)-2*|x|)-(3/10-2*|y|)| ≤ 2*|x-y|) ∧
      (3/10:ℝ) ∈ actualCone 0 (3/10) 0 1 0 ∧
      ((3/10:ℝ)-2*|3/10|)<0 := by
  refine ⟨?_,by norm_num [actualCone],by norm_num⟩
  intro x y
  have h := abs_abs_sub_abs_le_abs_sub x y
  have he : ((3/10:ℝ)-2*|x|)-(3/10-2*|y|)=-(2*(|x|-|y|)) := by ring
  rw [he,abs_neg,abs_mul]
  norm_num
  linarith

theorem actual_observation_cone_under_bounded_spatial_and_temporal_drift
    {X : Type*} [PseudoMetricSpace X] (f : ℝ → X → ℝ)
    (s t observation noise allowance slope speed : ℝ) (z x : X)
    (hobs : observation=f s z+noise) (hnoise : |noise| ≤ allowance)
    (hlip : ∀ a b, |f s a-f s b| ≤ slope*dist a b)
    (hdrift : ∀ a, |f t a-f s a| ≤ speed*|t-s|) :
    observation-allowance-slope*dist z x-speed*|t-s| ≤ f t x := by
  have hn := (abs_le.mp hnoise).2
  have hl := (abs_le.mp (hlip z x)).2
  have ht := (abs_le.mp (hdrift x)).1
  linarith

theorem actual_source_drift_lower_bound_and_stationary_overstatement :
    (4/5:ℝ)-1/10-2*(1/5)-(1/20)*3=3/20 ∧
      (4/5:ℝ)-1/10-2*(1/5)=3/10 ∧ (3/10:ℝ)-3/20=3/20 := by norm_num

theorem actual_source_downward_cone_is_a_compatible_sharpness_witness
    (observation allowance slope center threshold : ℝ)
    (he : 0 ≤ allowance) (hl : 0 < slope) :
    |allowance| ≤ allowance ∧
      (observation-allowance-slope*|center-center|)+allowance=observation ∧
      (∀ x y, |(observation-allowance-slope*|x-center|)-
        (observation-allowance-slope*|y-center|)| ≤ slope*|x-y|) ∧
      ∀ x, (observation-allowance-threshold)/slope < |x-center| →
        observation-allowance-slope*|x-center| < threshold := by
  refine ⟨by rw [abs_of_nonneg he],?_,?_,?_⟩
  · simp
  · exact CompleteModulesSafeExploration.downward_cone_is_lipschitz observation allowance slope center hl.le
  · exact fun x hx => CompleteModulesSafeExploration.beyond_cone_is_unsafe observation allowance slope center threshold x hl hx

end SafeLearning.CompleteModulesLoSBOPracticeModels
