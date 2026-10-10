import SafeLearning.CompleteModulesGoSafeToyGridGainBounds
import SafeLearning.CompleteModulesGoSafeToyGridCosines

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeToyGridLipschitz
open SafeLearning.CompleteModulesGoSafeToyAffine SafeLearning.CompleteModulesGoSafeToyFeasibility
open SafeLearning.CompleteModulesGoSafeToyGridGainBounds SafeLearning.CompleteModulesGoSafeToyGridCosines

abbrev GridPoint := Fin 25 × Fin 25

def actualGridSafety (p : GridPoint) : ℝ :=
  actualSourceSafety (actualGain ((p.2.val:ℝ)/24)) ((p.1.val:ℝ)/24)

def actualGridDistance (p q : GridPoint) : ℝ :=
  Real.sqrt (((p.1.val:ℝ)/24-(q.1.val:ℝ)/24)^2+((p.2.val:ℝ)/24-(q.2.val:ℝ)/24)^2)

theorem actual_source_grid_coordinate_belongs_to_the_unit_interval (i : Fin 25) :
    (i.val:ℝ)/24 ∈ Icc (0:ℝ) 1 := by
  have hi : (i.val:ℝ) ≤ 24 := by exact_mod_cast (show i.val ≤ 24 by omega)
  constructor
  · positivity
  · linarith

theorem actual_close_horizontal_and_nonzero_vertical_grid_steps_have_horizontal_distance_at_most_twice_vertical
    (i j k l : Fin 25) (hclose : max (i.val-j.val) (j.val-i.val) < 3) (hne : k ≠ l) :
    |(i.val:ℝ)/24-(j.val:ℝ)/24| ≤ 2*|(k.val:ℝ)/24-(l.val:ℝ)/24| := by
  have hij : i.val ≤ j.val+2 := by omega
  have hji : j.val ≤ i.val+2 := by omega
  have hijr : (i.val:ℝ) ≤ (j.val:ℝ)+2 := by exact_mod_cast hij
  have hjir : (j.val:ℝ) ≤ (i.val:ℝ)+2 := by exact_mod_cast hji
  have hx : |(i.val:ℝ)/24-(j.val:ℝ)/24| ≤ (2/24:ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hnev : k.val ≠ l.val := fun h => hne (Fin.ext h)
  have hy : (1/24:ℝ) ≤ |(k.val:ℝ)/24-(l.val:ℝ)/24| := by
    rcases lt_or_gt_of_ne hnev with h | h
    · have hn : k.val+1 ≤ l.val := by omega
      have hr : (k.val:ℝ)+1 ≤ (l.val:ℝ) := by exact_mod_cast hn
      rw [abs_of_nonpos (by linarith : (k.val:ℝ)/24-(l.val:ℝ)/24 ≤ 0)]
      linarith
    · have hn : l.val+1 ≤ k.val := by omega
      have hr : (l.val:ℝ)+1 ≤ (k.val:ℝ) := by exact_mod_cast hn
      rw [abs_of_nonneg (by linarith : 0 ≤ (k.val:ℝ)/24-(l.val:ℝ)/24)]
      linarith
  linarith

theorem actual_source_grid_difference_obeys_both_horizontal_vertical_triangle_bounds (p q : GridPoint) :
    |actualGridSafety p-actualGridSafety q| ≤
      (128/15)*|(p.1.val:ℝ)/24-(q.1.val:ℝ)/24|+(5/16)*|(p.2.val:ℝ)/24-(q.2.val:ℝ)/24| ∧
    (3 ≤ max (p.1.val-q.1.val) (q.1.val-p.1.val) →
      |actualGridSafety p-actualGridSafety q| ≤
        8*|(p.1.val:ℝ)/24-(q.1.val:ℝ)/24|+(5/16)*|(p.2.val:ℝ)/24-(q.2.val:ℝ)/24|) := by
  have hg := actual_source_gain_range_on_the_grid p.2
  have coef := actual_source_gain_cosine_coefficient_is_nonnegative_and_at_most_thirty_two_over_forty_five _ hg
  have ht := abs_sub_le (actualGridSafety p)
    (actualSourceSafety (actualGain ((p.2.val:ℝ)/24)) ((q.1.val:ℝ)/24)) (actualGridSafety q)
  have heq := actual_source_fixed_gain_margin_difference_is_the_literal_cosine_difference
    (actualGain ((p.2.val:ℝ)/24)) ((p.1.val:ℝ)/24) ((q.1.val:ℝ)/24) hg
  change |actualGridSafety p-actualSourceSafety (actualGain ((p.2.val:ℝ)/24)) ((q.1.val:ℝ)/24)| = _ at heq
  rw [heq] at ht
  have hv := actual_source_gain_difference_has_the_true_vertical_parameter_bound
    ((q.1.val:ℝ)/24) ((p.2.val:ℝ)/24) ((q.2.val:ℝ)/24)
    (actual_source_grid_coordinate_belongs_to_the_unit_interval p.2)
    (actual_source_grid_coordinate_belongs_to_the_unit_interval q.2)
  change |actualSourceSafety (actualGain ((p.2.val:ℝ)/24)) ((q.1.val:ℝ)/24)-actualGridSafety q| ≤ _ at hv
  have ht' : |actualGridSafety p-actualGridSafety q| ≤
      ((4/5)*actualGain ((p.2.val:ℝ)/24)/(1+actualGain ((p.2.val:ℝ)/24)))*
        |Real.cos (4*Real.pi*((p.1.val:ℝ)/24))-Real.cos (4*Real.pi*((q.1.val:ℝ)/24))|+
        (5/16)*|(p.2.val:ℝ)/24-(q.2.val:ℝ)/24| := by linarith
  have hcos := actual_source_grid_cosine_difference_is_at_most_twelve_times_parameter_distance p.1 q.1
  constructor
  · have hm := mul_le_mul coef.2 hcos (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 32/45)
    nlinarith
  · intro hfar
    have hc := actual_source_grid_columns_at_least_three_steps_apart_have_cosine_slope_at_most_eleven_and_one_quarter p.1 q.1 hfar
    have hm := mul_le_mul coef.2 hc (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 32/45)
    nlinarith

theorem actual_source_grid_difference_is_bounded_by_the_exact_grid_euclidean_constant (p q : GridPoint) :
    |actualGridSafety p-actualGridSafety q| ≤ (128/15)*actualGridDistance p q := by
  have hb := actual_source_grid_difference_obeys_both_horizontal_vertical_triangle_bounds p q
  have hs : actualGridDistance p q = Real.sqrt
      (|(p.1.val:ℝ)/24-(q.1.val:ℝ)/24|^2+|(p.2.val:ℝ)/24-(q.2.val:ℝ)/24|^2) := by
    simp only [actualGridDistance,sq_abs]
  rw [hs]
  by_cases hfar : 3 ≤ max (p.1.val-q.1.val) (q.1.val-p.1.val)
  · exact actual_far_horizontal_and_vertical_bounds_give_the_source_euclidean_grid_constant
      _ _ _ (abs_nonneg _) (abs_nonneg _) (hb.2 hfar)
  · by_cases hy : p.2=q.2
    · have hy0 : |(p.2.val:ℝ)/24-(q.2.val:ℝ)/24|=0 := by rw [hy];simp
      rw [hy0,zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero,Real.sqrt_sq (abs_nonneg _)]
      simpa only [hy0,mul_zero,add_zero] using hb.1
    · have hclose : max (p.1.val-q.1.val) (q.1.val-p.1.val)<3 := by omega
      exact actual_close_horizontal_steps_with_nonzero_vertical_steps_give_the_source_euclidean_grid_constant
        _ _ _ (abs_nonneg _) (abs_nonneg _)
        (actual_close_horizontal_and_nonzero_vertical_grid_steps_have_horizontal_distance_at_most_twice_vertical _ _ _ _ hclose hy) hb.1

theorem actual_source_grid_distance_is_positive_for_distinct_grid_points (p q : GridPoint) (hne : p ≠ q) :
    0 < actualGridDistance p q := by
  unfold actualGridDistance
  apply Real.sqrt_pos.2
  have hx := sq_nonneg ((p.1.val:ℝ)/24-(q.1.val:ℝ)/24)
  have hy := sq_nonneg ((p.2.val:ℝ)/24-(q.2.val:ℝ)/24)
  by_contra h
  have hz : ((p.1.val:ℝ)/24-(q.1.val:ℝ)/24)^2+((p.2.val:ℝ)/24-(q.2.val:ℝ)/24)^2=0 := by linarith
  have hx0 : (p.1.val:ℝ)=(q.1.val:ℝ) := by nlinarith
  have hy0 : (p.2.val:ℝ)=(q.2.val:ℝ) := by nlinarith
  have hxi : p.1.val=q.1.val := by exact_mod_cast hx0
  have hyi : p.2.val=q.2.val := by exact_mod_cast hy0
  exact hne (Prod.ext (Fin.ext hxi) (Fin.ext hyi))

def actualGridDifferenceQuotients : Set ℝ := {value | ∃ p q : GridPoint,
  p ≠ q ∧ value=|actualGridSafety p-actualGridSafety q|/actualGridDistance p q}

theorem actual_source_grid_has_the_largest_difference_quotient_one_hundred_twenty_eight_over_fifteen :
    IsGreatest actualGridDifferenceQuotients (128/15:ℝ) := by
  constructor
  · refine ⟨(3,24),(4,24),by decide,?_⟩
    have hc3 := (actual_source_cosine_and_sine_grid_columns_equal_the_exact_table (3:Fin 25)).1
    have hc4 := (actual_source_cosine_and_sine_grid_columns_equal_the_exact_table (4:Fin 25)).1
    norm_num [exactColumnCos] at hc3 hc4
    change (128/15:ℝ)=|actualSourceSafety (actualGain ((24:Fin 25).val/24)) ((3:Fin 25).val/24)-
      actualSourceSafety (actualGain ((24:Fin 25).val/24)) ((4:Fin 25).val/24)|/
      actualGridDistance (3,24) (4,24)
    norm_num [actualGain]
    rw [actual_source_zero_start_safety_is_the_true_equilibrium_margin 8 _ (by norm_num),
      actual_source_zero_start_safety_is_the_true_equilibrium_margin 8 _ (by norm_num)]
    norm_num [actualGridDistance,actualEquilibrium,actualReference,hc3,hc4]
  · rintro value ⟨p,q,hne,rfl⟩
    apply (div_le_iff₀ (actual_source_grid_distance_is_positive_for_distinct_grid_points p q hne)).mpr
    exact actual_source_grid_difference_is_bounded_by_the_exact_grid_euclidean_constant p q

end SafeLearning.CompleteModulesGoSafeToyGridLipschitz
