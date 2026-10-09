import SafeLearning.BookApplications
import SafeLearning.CoreAnalysis
import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators ENNReal NNReal

namespace SafeLearning.CompleteBookProjects

def projectInterval (lower upper nominal : ℝ) : ℝ := max lower (min upper nominal)

theorem projectInterval_mem (lower upper nominal : ℝ) (h : lower ≤ upper) :
    projectInterval lower upper nominal ∈ Icc lower upper := by
  constructor
  · exact le_max_left _ _
  · exact max_le h (min_le_left _ _)

theorem projectInterval_of_below (lower upper nominal : ℝ)
    (h : nominal ≤ lower) : projectInterval lower upper nominal = lower := by
  exact max_eq_left ((min_le_right _ _).trans h)

theorem projectInterval_of_above (lower upper nominal : ℝ)
    (hlu : lower ≤ upper) (h : upper ≤ nominal) :
    projectInterval lower upper nominal = upper := by
  simp [projectInterval, min_eq_left h, max_eq_right hlu]

theorem projectInterval_of_mem (lower upper nominal : ℝ)
    (h : nominal ∈ Icc lower upper) : projectInterval lower upper nominal = nominal := by
  simp [projectInterval, min_eq_right h.2, max_eq_right h.1]

theorem projectInterval_optimal (lower upper nominal u : ℝ)
    (hlu : lower ≤ upper) (hu : u ∈ Icc lower upper) :
    (projectInterval lower upper nominal-nominal)^2 ≤ (u-nominal)^2 := by
  by_cases hl : nominal ≤ lower
  · rw [projectInterval_of_below lower upper nominal hl]
    nlinarith [sq_nonneg (u-lower), hu.1]
  · by_cases hh : upper ≤ nominal
    · rw [projectInterval_of_above lower upper nominal hlu hh]
      nlinarith [sq_nonneg (u-upper), hu.2]
    · rw [projectInterval_of_mem lower upper nominal ⟨le_of_not_ge hl, le_of_not_ge hh⟩]
      simp only [sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      exact sq_nonneg _

theorem projectInterval_unique (lower upper nominal u : ℝ)
    (hlu : lower ≤ upper) (hu : u ∈ Icc lower upper)
    (heq : (u-nominal)^2 = (projectInterval lower upper nominal-nominal)^2) :
    u = projectInterval lower upper nominal := by
  by_cases hl : nominal ≤ lower
  · rw [projectInterval_of_below lower upper nominal hl] at heq ⊢
    nlinarith [sq_nonneg (u-lower), hu.1]
  · by_cases hh : upper ≤ nominal
    · rw [projectInterval_of_above lower upper nominal hlu hh] at heq ⊢
      nlinarith [sq_nonneg (u-upper), hu.2]
    · rw [projectInterval_of_mem lower upper nominal ⟨le_of_not_ge hl, le_of_not_ge hh⟩] at heq ⊢
      nlinarith [sq_nonneg (u-nominal)]

theorem intersect_intervals (a b c d : ℝ) :
    Icc a b ∩ Icc c d = Icc (max a c) (min b d) := by
  ext x
  simp only [mem_inter_iff, mem_Icc, max_le_iff, le_min_iff]
  tauto

theorem tank_robust_interval_iff (y u : ℝ) :
    (∀ x w : ℝ, |x-y| ≤ 1/10 → |w| ≤ 1/5 → x+u+w ∈ Icc 0 10) ↔
      u ∈ Icc (3/10-y) (97/10-y) := by
  constructor
  · intro h
    have hl := (h (y-1/10) (-1/5) (by norm_num) (by norm_num)).1
    have hh := (h (y+1/10) (1/5) (by norm_num) (by norm_num)).2
    constructor <;> linarith
  · intro hu x w hm hw
    exact BookApplications.tank_original_step x y u w hm hw hu

theorem tank_measurement_range (x y : ℝ) (hx : x ∈ Icc 0 10)
    (hm : |x-y| ≤ 1/10) : y ∈ Icc (-1/10) (101/10) := by
  rcases abs_le.mp hm with ⟨h₁,h₂⟩
  constructor <;> linarith [hx.1,hx.2]

theorem tank_original_decision :
    projectInterval (-1/10) 1 (-1) = -1/10 ∧
    (4/10 : ℝ)-1/10-1/10-1/5=0 ∧
    (4/10 : ℝ)+1/10-1/10+1/5=3/5 ∧
    (-1/10 : ℝ)-(-1)=9/10 := by norm_num [projectInterval]

theorem tank_upper_decision :
    (3/10 : ℝ)-49/5 = -19/2 ∧ (97/10 : ℝ)-49/5 = -1/10 ∧
    projectInterval (-1) (-1/10) (7/10) = -1/10 ∧
    (49/5 : ℝ)-1/10-1/10-1/5=47/5 ∧
    (49/5 : ℝ)+1/10-1/10+1/5=10 := by norm_num [projectInterval]

theorem tank_large_disturbance_interval (y u : ℝ) :
    (∀ x w : ℝ, |x-y| ≤ 1/10 → |w| ≤ 6/5 → x+u+w ∈ Icc 0 10) ↔
      u ∈ Icc (13/10-y) (87/10-y) := by
  constructor
  · intro h
    have hl := (h (y-1/10) (-6/5) (by norm_num) (by norm_num)).1
    have hh := (h (y+1/10) (6/5) (by norm_num) (by norm_num)).2
    constructor <;> linarith
  · intro hu x w hm hw
    exact BookApplications.robust_tank_step x y u w 10 (1/10) (6/5)
      hm hw (by linarith [hu.1]) (by linarith [hu.2])

theorem tank_large_disturbance_empty :
    Icc (-1 : ℝ) 1 ∩ Icc (13/10-(-1/10)) (87/10-(-1/10)) = ∅ := by
  ext u
  simp only [mem_inter_iff, mem_Icc, mem_empty_iff_false, iff_false]
  rintro ⟨⟨_,hu⟩,⟨hl,_⟩⟩
  linarith

theorem tank_large_disturbance_valid_counterexample :
    (0 : ℝ) ∈ Icc 0 10 ∧ |0-(-1/10 : ℝ)| ≤ 1/10 ∧
      ∀ u ∈ Icc (-1 : ℝ) 1, 0+u-6/5 < 0 := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro u hu
  linarith [hu.2]

theorem tank_feedback_quantifiers :
    (∀ y ∈ Icc (-1/10 : ℝ) (101/10), ∃ u ∈ Icc (-1 : ℝ) 1,
      ∀ x ∈ Icc (0 : ℝ) 10, |x-y| ≤ 1/10 →
        ∀ w : ℝ, |w| ≤ 1/5 → x+u+w ∈ Icc 0 10) ∧
    ¬ (∃ u : ℝ, ∀ x ∈ Icc (0 : ℝ) 10,
      ∀ w ∈ Icc (-1/5 : ℝ) (1/5), x+u+w ∈ Icc 0 10) := by
  constructor
  · intro y hy
    obtain ⟨u,hu,hs⟩ := BookApplications.tank_measurement_feedback y hy
    exact ⟨u,hu,fun x _ hm w hw => hs x w hm hw⟩
  · exact BookApplications.tank_no_shared_input

def tuningLower (observation error center a : ℝ) : ℝ :=
  observation-error-(1/2)*|a-center|

theorem tuning_lower_valid (g : ℝ → ℝ) (a center observation error : ℝ)
    (hobs : |g center-observation| ≤ error)
    (hlip : |g a-g center| ≤ (1/2)*|a-center|) :
    tuningLower observation error center a ≤ g a := by
  have ho := (abs_le.mp hobs).1
  have hl := (abs_le.mp hlip).1
  unfold tuningLower
  linarith

theorem tuning_first_set (a : ℝ) :
    (a ∈ Icc 0 1 ∧ 0 ≤ tuningLower (9/50) (1/50) (1/5) a) ↔
      a ∈ Icc 0 (13/25) := by
  unfold tuningLower
  constructor
  · rintro ⟨ha,hl⟩
    have h := le_abs_self (a-1/5)
    constructor <;> linarith [ha.1]
  · intro ha
    constructor
    · constructor <;> linarith [ha.1,ha.2]
    · have hab : |a-1/5| ≤ 8/25 := abs_le.mpr ⟨by linarith [ha.1],by linarith [ha.2]⟩
      linarith

theorem tuning_second_set (a : ℝ) :
    (a ∈ Icc 0 1 ∧ 0 ≤ tuningLower (7/50) (1/50) (1/2) a) ↔
      a ∈ Icc (13/50) (37/50) := by
  unfold tuningLower
  constructor
  · rintro ⟨_,hl⟩
    have h₁ := le_abs_self (a-1/2)
    have h₂ := neg_le_abs (a-1/2)
    constructor <;> linarith
  · intro ha
    constructor
    · constructor <;> linarith [ha.1,ha.2]
    · have hab : |a-1/2| ≤ 6/25 := abs_le.mpr ⟨by linarith [ha.1],by linarith [ha.2]⟩
      linarith

theorem tuning_union :
    Icc (0 : ℝ) (13/25) ∪ Icc (13/50) (37/50) = Icc 0 (37/50) := by
  ext a
  simp only [mem_union,mem_Icc]
  constructor
  · intro h
    rcases h with h|h <;> constructor <;> linarith [h.1,h.2]
  · intro h
    by_cases ha : a ≤ 13/25
    · exact Or.inl ⟨h.1,ha⟩
    · exact Or.inr ⟨by linarith,h.2⟩

theorem tuning_query_values :
    tuningLower (9/50) (1/50) (1/5) (3/5) = -1/25 ∧
    tuningLower (9/50) (1/50) (1/5) (1/2) = 1/100 ∧
    tuningLower (7/50) (1/50) (1/2) (3/5) = 7/100 := by
  norm_num [tuningLower]

theorem tuning_noisier_set (a : ℝ) :
    (a ∈ Icc 0 1 ∧ 0 ≤ tuningLower (9/50) (1/20) (1/5) a) ↔
      a ∈ Icc 0 (23/50) := by
  unfold tuningLower
  constructor
  · rintro ⟨ha,hl⟩
    have h := le_abs_self (a-1/5)
    constructor <;> linarith [ha.1]
  · intro ha
    constructor
    · constructor <;> linarith [ha.1,ha.2]
    · have hab : |a-1/5| ≤ 13/50 := abs_le.mpr ⟨by linarith [ha.1],by linarith [ha.2]⟩
      linarith

theorem tuning_noisier_query :
    tuningLower (9/50) (1/20) (1/5) (1/2) = -1/50 ∧
    tuningLower (9/50) (1/20) (1/5) (23/50) = 0 ∧
    ∀ a : ℝ, 0 ≤ tuningLower (9/50) (1/20) (1/5) a → a ≤ 23/50 := by
  refine ⟨by norm_num [tuningLower],by norm_num [tuningLower],?_⟩
  intro a ha
  unfold tuningLower at ha
  have h := le_abs_self (a-1/5)
  linarith

theorem tuning_performance_underdetermined :
    (3/5 : ℝ) ∈ Icc 0 (37/50) ∧ (7/10 : ℝ) ∈ Icc 0 (37/50) ∧
    (fun a : ℝ => a) (3/5) < (fun a : ℝ => a) (7/10) ∧
    (fun a : ℝ => -a) (3/5) > (fun a : ℝ => -a) (7/10) := by
  norm_num

theorem zero_lipschitz_constant (g : ℝ → ℝ)
    (h : ∀ a b, |g a-g b| ≤ 0) : ∀ a b, g a=g b := by
  intro a b
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (h a b) (abs_nonneg _)))

theorem zero_lipschitz_lower_certificate (g : ℝ → ℝ) (center lower : ℝ)
    (h : ∀ a b, |g a-g b| ≤ 0) (hl : lower ≤ g center) (hn : 0 ≤ lower) :
    ∀ a : ℝ, 0 ≤ g a := by
  intro a
  rw [zero_lipschitz_constant g h a center]
  exact hn.trans hl

theorem negative_lower_underdetermined :
    ∃ positive negative : ℝ → ℝ,
      (∀ a b, |positive a-positive b| ≤ 0 ∧ |negative a-negative b| ≤ 0) ∧
      (∀ a, (-1 : ℝ) ≤ positive a ∧ (-1 : ℝ) ≤ negative a) ∧
      (∀ a, 0 < positive a ∧ negative a < 0) := by
  refine ⟨fun _ => 1,fun _ => -1,?_,?_,?_⟩ <;> intros <;> norm_num

def scoreGap (dx dy : ℝ) : ℝ := 3/5+2*dx-dy

theorem score_box_lower (dx dy : ℝ) (hx : |dx| ≤ 1/5) (hy : |dy| ≤ 1/5) :
    0 ≤ scoreGap dx dy := by
  rcases abs_le.mp hx with ⟨hx₀,hx₁⟩
  rcases abs_le.mp hy with ⟨hy₀,hy₁⟩
  unfold scoreGap
  linarith

theorem score_box_tie : scoreGap (-1/5) (1/5)=0 := by norm_num [scoreGap]

theorem normalized_physical_box (e₁ e₂ : ℝ) :
    (|e₁| ≤ 1/10 ∧ |e₂| ≤ 2/5) ↔
      (|e₁/(1/2)| ≤ 1/5 ∧ |e₂/2| ≤ 1/5) := by
  simp only [abs_div]
  norm_num
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem normalized_score_lower (e₁ e₂ : ℝ)
    (he₁ : |e₁| ≤ 1/10) (he₂ : |e₂| ≤ 2/5) :
    0 ≤ scoreGap (e₁/(1/2)) (e₂/2) := by
  have h := (normalized_physical_box e₁ e₂).mp ⟨he₁,he₂⟩
  exact score_box_lower _ _ h.1 h.2

theorem unnormalized_radius_is_different :
    (1/5 : ℝ)^2+0^2 ≤ (1/5)^2 ∧
    ¬ (((1/5 : ℝ)/(1/2))^2+(0/2)^2 ≤ (1/5)^2) := by norm_num

theorem score_euclidean_strict (dx dy r : ℝ) (hr : 0 ≤ r)
    (hball : dx^2+dy^2 ≤ r^2) (hstrict : Real.sqrt 5*r < 3/5) :
    0 < scoreGap dx dy := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  have hab : (2*dx-dy)^2 ≤ 5*(dx^2+dy^2) := by
    nlinarith [sq_nonneg (dx+2*dy)]
  have hlo : -(Real.sqrt 5*r) ≤ 2*dx-dy := by
    nlinarith [mul_nonneg hn hr,sq_nonneg (Real.sqrt 5*r+(2*dx-dy))]
  unfold scoreGap
  linarith

theorem score_euclidean_one_fifth (dx dy : ℝ)
    (hball : dx^2+dy^2 ≤ (1/5)^2) : 0 < scoreGap dx dy := by
  apply score_euclidean_strict dx dy (1/5) (by norm_num) hball
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  nlinarith

theorem score_critical_tie :
    scoreGap (-6/25) (3/25) = 0 ∧
    (-6/25 : ℝ)^2+(3/25)^2 = ((3/5)/Real.sqrt 5)^2 := by
  constructor
  · norm_num [scoreGap]
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    simp only [div_pow]
    rw [hs]
    norm_num

theorem strict_radii_no_largest (critical r : ℝ) (hr : r < critical) :
    r < (r+critical)/2 ∧ (r+critical)/2 < critical := by constructor <;> linarith

theorem conformal_ranks :
    (⌈((19+1 : ℝ)*(1-1/10))⌉ : ℤ)=18 ∧
    (⌈((19+1 : ℝ)*(1-1/100))⌉ : ℤ)=20 ∧
    (18 : ℝ)/10=9/5 ∧ (19 : ℕ)<20 := by norm_num

def augmentedThreshold (n rank : ℕ) (finiteThreshold : ℝ) : EReal :=
  if n < rank then ⊤ else (finiteThreshold : EReal)

theorem unavailable_rank_infinite (finiteThreshold : ℝ) :
    augmentedThreshold 19 20 finiteThreshold = ⊤ := by
  norm_num [augmentedThreshold]

theorem infinite_threshold_covers (score : ℝ) :
    (score : EReal) ≤ augmentedThreshold 19 20 (19/10) := by
  rw [unavailable_rank_infinite]
  exact le_top

theorem four_failure_arithmetic :
    (1 : ℝ)-4*(1/10)=3/5 ∧ (9/10 : ℝ)^4=6561/10000 ∧
    4*(1/40 : ℝ)=1/10 ∧ 1/10 < 4*(1/10 : ℝ) := by norm_num

theorem four_failure_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (failure : Fin 4 → Set Ω)
    (h : ∀ i, μ (failure i) ≤ (1/10 : ℝ≥0∞)) :
    μ (⋃ i, failure i) ≤ (2/5 : ℝ≥0∞) := by
  calc μ (⋃ i, failure i) ≤ ∑ i, μ (failure i) := MeasureTheory.measure_iUnion_fintype_le μ failure
    _ ≤ ∑ _i : Fin 4, (1/10 : ℝ≥0∞) := Finset.sum_le_sum (fun i _ => h i)
    _ = 2/5 := by
      norm_num
      rw [← div_eq_mul_inv]
      apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
      norm_num

theorem four_failure_allocated {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (failure : Fin 4 → Set Ω)
    (h : ∀ i, μ (failure i) ≤ (1/40 : ℝ≥0∞)) :
    μ (⋃ i, failure i) ≤ (1/10 : ℝ≥0∞) := by
  calc μ (⋃ i, failure i) ≤ ∑ i, μ (failure i) := MeasureTheory.measure_iUnion_fintype_le μ failure
    _ ≤ ∑ _i : Fin 4, (1/40 : ℝ≥0∞) := Finset.sum_le_sum (fun i _ => h i)
    _ = 1/10 := by
      norm_num
      have h : (4 : ℝ≥0∞)/40=1/10 := by
        apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
        norm_num
      simpa only [div_eq_mul_inv,one_mul] using h

end SafeLearning.CompleteBookProjects
