import SafeLearning.CompleteModulesTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteModulesGoSafeNoisyBackup

abbrev E := EuclideanSpace ℝ (Fin 2)
def actualCurrent : E := WithLp.toLp 2 ![1/5,1/20]
def actualSecondCenter : E := WithLp.toLp 2 ![3/10,1/10]
def actualFirstMargin : ℝ := 1/2-2*dist actualCurrent 0
def actualSecondMargin : ℝ := 3/10-2*dist actualCurrent actualSecondCenter

theorem actual_planar_euclidean_distance_has_the_literal_coordinate_formula (x y : E) :
    dist x y=Real.sqrt ((x 0-y 0)^2+(x 1-y 1)^2) := by
  simp [dist_eq_norm,EuclideanSpace.norm_eq,Fin.sum_univ_two,Real.norm_eq_abs,sq_abs]

theorem actual_source_planar_distances_and_their_exact_squares :
    dist actualCurrent 0=Real.sqrt (17/400) ∧
      dist actualCurrent actualSecondCenter=Real.sqrt (1/80) ∧
      (dist actualCurrent 0)^2=17/400 ∧
      (dist actualCurrent actualSecondCenter)^2=1/80 := by
  have h1 : dist actualCurrent 0=Real.sqrt (17/400) := by
    rw [actual_planar_euclidean_distance_has_the_literal_coordinate_formula]
    norm_num [actualCurrent]
  have h2 : dist actualCurrent actualSecondCenter=Real.sqrt (1/80) := by
    rw [actual_planar_euclidean_distance_has_the_literal_coordinate_formula]
    norm_num [actualCurrent,actualSecondCenter]
  refine ⟨h1,h2,?_,?_⟩
  · rw [h1];exact Real.sq_sqrt (by norm_num)
  · rw [h2];exact Real.sq_sqrt (by norm_num)

theorem actual_source_radii_before_and_after_the_two_measurement_error_allowance :
    (1/2:ℝ)/2-1/20=1/5 ∧ (3/10:ℝ)/2-1/20=1/10 ∧
      (1/20:ℝ)+2*(1/100)=7/100 ∧
      (1/2:ℝ)/2-7/100=9/50 ∧ (3/10:ℝ)/2-7/100=2/25 := by norm_num

theorem actual_distances_and_guaranteed_margins_have_all_printed_roundings_and_select_the_first_backup :
    |dist actualCurrent 0-(206/1000:ℝ)|<1/2000 ∧
      |dist actualCurrent actualSecondCenter-(112/1000:ℝ)|<1/2000 ∧
      (1/5:ℝ)<dist actualCurrent 0 ∧ (1/10:ℝ)<dist actualCurrent actualSecondCenter ∧
      |actualFirstMargin-(88/1000:ℝ)|<1/2000 ∧
      |actualSecondMargin-(76/1000:ℝ)|<1/2000 ∧
      0<actualFirstMargin ∧ 0<actualSecondMargin ∧ actualSecondMargin<actualFirstMargin ∧
      IsGreatest (Set.range (fun i : Fin 2=>![actualFirstMargin,actualSecondMargin] i)) actualFirstMargin := by
  have hs := actual_source_planar_distances_and_their_exact_squares
  have hn1 := dist_nonneg (x:=actualCurrent) (y:=(0:E))
  have hn2 := dist_nonneg (x:=actualCurrent) (y:=actualSecondCenter)
  have h1 : (20615/100000:ℝ)<dist actualCurrent 0 ∧ dist actualCurrent 0<(20616/100000:ℝ) := by
    constructor <;> nlinarith [hs.2.2.1]
  have h2 : (11180/100000:ℝ)<dist actualCurrent actualSecondCenter ∧
      dist actualCurrent actualSecondCenter<(11181/100000:ℝ) := by
    constructor <;> nlinarith [hs.2.2.2]
  have hmargin : actualSecondMargin<actualFirstMargin := by
    unfold actualFirstMargin actualSecondMargin
    linarith [h1.2,h2.1]
  refine ⟨?_,?_,by linarith [h1.1],by linarith [h2.1],?_,?_,?_,?_,hmargin,?_⟩
  · rw [abs_lt];constructor <;> linarith [h1.1,h1.2]
  · rw [abs_lt];constructor <;> linarith [h2.1,h2.2]
  · rw [abs_lt];unfold actualFirstMargin;constructor <;> linarith [h1.1,h1.2]
  · rw [abs_lt];unfold actualSecondMargin;constructor <;> linarith [h2.1,h2.2]
  · unfold actualFirstMargin;linarith [h1.2]
  · unfold actualSecondMargin;linarith [h2.2]
  · constructor
    · exact ⟨0,by simp⟩
    · rintro value ⟨i,rfl⟩
      fin_cases i
      · simp
      · simpa using hmargin.le

theorem actual_printed_finite_decimal_distances_are_not_exact_equalities :
    dist actualCurrent 0≠(206/1000:ℝ) ∧
      dist actualCurrent actualSecondCenter≠(112/1000:ℝ) := by
  have h := actual_source_planar_distances_and_their_exact_squares
  constructor <;> intro he
  · have h1 := h.2.2.1;rw [he] at h1;norm_num at h1
  · have h2 := h.2.2.2;rw [he] at h2;norm_num at h2

theorem actual_current_and_stored_measurement_errors_both_enter_the_distance_allowance
    {X : Type*} [PseudoMetricSpace X] (current stored measuredCurrent measuredStored : X)
    (radius : ℝ) (hc : dist current measuredCurrent ≤ radius)
    (hs : dist stored measuredStored ≤ radius) :
    dist current stored ≤ dist measuredCurrent measuredStored+2*radius := by
  have h1 := dist_triangle current measuredCurrent stored
  have h2 := dist_triangle measuredCurrent measuredStored stored
  rw [dist_comm measuredStored stored] at h2
  linarith

theorem actual_measured_backup_test_with_point_zero_seven_is_conservative_for_true_motion_point_zero_five
    {X : Type*} [PseudoMetricSpace X] (current stored measuredCurrent measuredStored : X)
    (lower : ℝ) (hc : dist current measuredCurrent ≤ (1/100:ℝ))
    (hs : dist stored measuredStored ≤ (1/100:ℝ))
    (htest : 2*(dist measuredCurrent measuredStored+7/100) ≤ lower) :
    2*(dist current stored+1/20) ≤ lower := by
  have h := actual_current_and_stored_measurement_errors_both_enter_the_distance_allowance
    current stored measuredCurrent measuredStored (1/100) hc hs
  linarith

theorem actual_independent_current_and_stored_good_error_events_have_the_source_probability
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (currentError storedError : Ω→X)
    (goodError : Set X) (hgood : MeasurableSet goodError)
    (hind : IndepFun currentError storedError μ) (delta : ℝ) (hd : delta ≤ 1)
    (hc : Real.sqrt (1-delta) ≤ μ.real (currentError ⁻¹' goodError))
    (hs : Real.sqrt (1-delta) ≤ μ.real (storedError ⁻¹' goodError)) :
    (1-delta) ≤ μ.real (currentError ⁻¹' goodError∩storedError ⁻¹' goodError) := by
  have hm := hind.measure_inter_preimage_eq_mul goodError goodError hgood hgood
  have hr : μ.real (currentError ⁻¹' goodError∩storedError ⁻¹' goodError)=
      μ.real (currentError ⁻¹' goodError)*μ.real (storedError ⁻¹' goodError) := by
    simp only [Measure.real,hm,ENNReal.toReal_mul]
  have hp := mul_le_mul hc hs (Real.sqrt_nonneg (1-delta)) (measureReal_nonneg)
  have hsq : Real.sqrt (1-delta)^2=1-delta := Real.sq_sqrt (by linarith)
  rw [hr]
  nlinarith [hp]

end SafeLearning.CompleteModulesGoSafeNoisyBackup
