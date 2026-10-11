import SafeLearning.Modules

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Matrix

namespace SafeLearning.CompleteModulesPhysicalSensorBox28

def normalizeTemperature (T : ℝ) : ℝ := (T-40)/10
def normalizeDistance (d : ℝ) : ℝ := (d-1/2)/(1/10)
def normalizedCorrection (x y : ℝ) : ℝ := max (x+2*y) 0+max (x-2*y) 0
def physicalCorrection (T d : ℝ) : ℝ :=
  normalizedCorrection (normalizeTemperature T) (normalizeDistance d)
def normalizedNetwork (x y : ℝ) : ℝ := normalizedCorrection x y/2
def sdpBound : ℝ := 2*Real.sqrt (4/3)*(Real.sqrt 2*(1/50))
def scalingThreshold : ℝ := (3/50)/sdpBound
def certificate : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-4/3,0,1/3,1/3;0,-4/3,2/3,-2/3;
      1/3,2/3,-5/12,1/4;1/3,-2/3,1/4,-5/12]
def affineRow (a b : ℝ) : (ℝ×ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ

private theorem abs_max_pair_bound (a b c d r : ℝ)
    (ha : |a-c| ≤ r) (hb : |b-d| ≤ r) : |max a b-max c d| ≤ r := by
  exact (abs_max_sub_max_le_max a b c d).trans (max_le ha hb)

private theorem relu_incremental_sector (x y : ℝ) :
    0 ≤ (max x 0-max y 0)*((x-y)-(max x 0-max y 0)) := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [max_eq_left hx,max_eq_left hy];ring_nf;exact le_rfl
  · rw [max_eq_left hx,max_eq_right (le_of_not_ge hy)];nlinarith
  · rw [max_eq_right (le_of_not_ge hx),max_eq_left hy];nlinarith
  · rw [max_eq_right (le_of_not_ge hx),max_eq_right (le_of_not_ge hy)];norm_num

theorem actual_preprocessing_difference_equalities (T d Tb db : ℝ) :
    normalizeTemperature T-normalizeTemperature Tb=(T-Tb)/10 ∧
    normalizeDistance d-normalizeDistance db=10*(d-db) := by
  dsimp [normalizeTemperature,normalizeDistance]
  constructor <;> ring

theorem actual_hardware_error_box_is_normalized (T d Tb db : ℝ)
    (hT : |T-Tb| ≤ 1/5) (hd : |d-db| ≤ 1/500) :
    |normalizeTemperature T-normalizeTemperature Tb| ≤ 1/50 ∧
    |normalizeDistance d-normalizeDistance db| ≤ 1/50 := by
  rw [actual_preprocessing_difference_equalities T d Tb db |>.1,
    actual_preprocessing_difference_equalities T d Tb db |>.2,abs_div,abs_mul]
  norm_num
  constructor <;> linarith

theorem actual_normalized_box_has_the_euclidean_radius (dx dy : ℝ)
    (hx : |dx| ≤ 1/50) (hy : |dy| ≤ 1/50) :
    dx^2+dy^2 ≤ (Real.sqrt 2*(1/50))^2 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hx2:=sq_le_sq₀ (abs_nonneg dx) (by norm_num : (0:ℝ) ≤ 1/50) |>.mpr hx
  have hy2:=sq_le_sq₀ (abs_nonneg dy) (by norm_num : (0:ℝ) ≤ 1/50) |>.mpr hy
  rw [sq_abs] at hx2 hy2
  rw [mul_pow,hs]
  linarith

theorem actual_certificate_quadratic_sum_of_squares (v : Fin 4 → ℝ) :
    v ⬝ᵥ (certificate *ᵥ v)=
      -(4/3)*(v 0-(v 2+v 3)/4)^2-(4/3)*(v 1-(v 2-v 3)/2)^2 := by
  simp [certificate,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_sdp_certificate_is_negative_semidefinite : (-certificate).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [certificate,Matrix.conjTranspose_apply]
  · intro v
    simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg]
    rw [actual_certificate_quadratic_sum_of_squares]
    nlinarith [sq_nonneg (v 0-(v 2+v 3)/4),sq_nonneg (v 1-(v 2-v 3)/2)]

theorem actual_sdp_certificate_is_the_source_incremental_lmi (dx dy dz1 dz2 : ℝ) :
    (![dx,dy,dz1,dz2]:Fin 4 → ℝ) ⬝ᵥ
        (certificate *ᵥ (![dx,dy,dz1,dz2]:Fin 4 → ℝ))=
      ((dz1+dz2)/2)^2-(4/3)*(dx^2+dy^2)+
        (2/3)*(dz1*((dx+2*dy)-dz1)+dz2*((dx-2*dy)-dz2)) := by
  rw [actual_certificate_quadratic_sum_of_squares]
  norm_num
  ring

theorem actual_network_sdp_squared_gain (x y xb yb : ℝ) :
    (normalizedNetwork x y-normalizedNetwork xb yb)^2 ≤
      (4/3)*((x-xb)^2+(y-yb)^2) := by
  let dz1:=max (x+2*y) 0-max (xb+2*yb) 0
  let dz2:=max (x-2*y) 0-max (xb-2*yb) 0
  have h1:=relu_incremental_sector (x+2*y) (xb+2*yb)
  have h2:=relu_incremental_sector (x-2*y) (xb-2*yb)
  have hm:=actual_sdp_certificate_is_negative_semidefinite.dotProduct_mulVec_nonneg
    (![x-xb,y-yb,dz1,dz2]:Fin 4 → ℝ)
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg] at hm
  rw [actual_sdp_certificate_is_the_source_incremental_lmi] at hm
  have he : normalizedNetwork x y-normalizedNetwork xb yb=(dz1+dz2)/2 := by
    dsimp [normalizedNetwork,normalizedCorrection,dz1,dz2]
    ring
  rw [he]
  dsimp [dz1,dz2] at hm
  nlinarith

theorem actual_physical_sdp_bound (x y xb yb r : ℝ) (hr : 0 ≤ r)
    (hinput : (x-xb)^2+(y-yb)^2 ≤ r^2) :
    |normalizedCorrection x y-normalizedCorrection xb yb| ≤ 2*Real.sqrt (4/3)*r := by
  have hg:=actual_network_sdp_squared_gain x y xb yb
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4/3)
  have he : normalizedCorrection x y-normalizedCorrection xb yb=
      2*(normalizedNetwork x y-normalizedNetwork xb yb) := by dsimp [normalizedNetwork];ring
  have hn : 0 ≤ 2*Real.sqrt (4/3)*r := by positivity
  apply abs_le_of_sq_le_sq _ hn
  rw [he]
  nlinarith

theorem actual_hardware_sdp_error_bound (T d Tb db : ℝ)
    (hT : |T-Tb| ≤ 1/5) (hd : |d-db| ≤ 1/500) :
    |physicalCorrection T d-physicalCorrection Tb db| ≤ sdpBound := by
  have h:=actual_hardware_error_box_is_normalized T d Tb db hT hd
  exact actual_physical_sdp_bound _ _ _ _ _ (by positivity)
    (actual_normalized_box_has_the_euclidean_radius _ _ h.1 h.2)

theorem actual_physical_correction_is_max_of_four_affine_regions (x y : ℝ) :
    normalizedCorrection x y=max (max 0 (2*x)) (max (x+2*y) (x-2*y)) := by
  dsimp [normalizedCorrection]
  simp only [max_def]
  split_ifs <;> linarith

theorem actual_four_activation_region_formulae (x y : ℝ) :
    (x+2*y ≤ 0 → x-2*y ≤ 0 → normalizedCorrection x y=0) ∧
    (0 ≤ x+2*y → x-2*y ≤ 0 → normalizedCorrection x y=x+2*y) ∧
    (x+2*y ≤ 0 → 0 ≤ x-2*y → normalizedCorrection x y=x-2*y) ∧
    (0 ≤ x+2*y → 0 ≤ x-2*y → normalizedCorrection x y=2*x) := by
  repeat' constructor
  all_goals intro h1 h2
  · rw [normalizedCorrection,max_eq_right h1,max_eq_right h2];ring
  · rw [normalizedCorrection,max_eq_left h1,max_eq_right h2];ring
  · rw [normalizedCorrection,max_eq_right h1,max_eq_left h2];ring
  · rw [normalizedCorrection,max_eq_left h1,max_eq_left h2];ring

theorem actual_region_rows_coordinate_derivatives (a b : ℝ) :
    affineRow a b (1,0)=a ∧ affineRow a b (0,1)=b := by
  simp [affineRow]

theorem actual_four_open_region_frechet_derivatives (p : ℝ×ℝ) :
    (p.1+2*p.2 < 0 → p.1-2*p.2 < 0 →
      HasFDerivAt (fun q : ℝ×ℝ => normalizedCorrection q.1 q.2) (affineRow 0 0) p) ∧
    (0 < p.1+2*p.2 → p.1-2*p.2 < 0 →
      HasFDerivAt (fun q : ℝ×ℝ => normalizedCorrection q.1 q.2) (affineRow 1 2) p) ∧
    (p.1+2*p.2 < 0 → 0 < p.1-2*p.2 →
      HasFDerivAt (fun q : ℝ×ℝ => normalizedCorrection q.1 q.2) (affineRow 1 (-2)) p) ∧
    (0 < p.1+2*p.2 → 0 < p.1-2*p.2 →
      HasFDerivAt (fun q : ℝ×ℝ => normalizedCorrection q.1 q.2) (affineRow 2 0) p) := by
  have hc1 : Continuous (fun q : ℝ×ℝ => q.1+2*q.2) := by fun_prop
  have hc2 : Continuous (fun q : ℝ×ℝ => q.1-2*q.2) := by fun_prop
  repeat' constructor
  all_goals intro h1 h2
  · apply (affineRow 0 0).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [hc1.continuousAt.eventually (lt_mem_nhds h1),
      hc2.continuousAt.eventually (lt_mem_nhds h2)] with q hq1 hq2
    simp only [actual_four_activation_region_formulae q.1 q.2 |>.1 hq1.le hq2.le]
    simp [affineRow]
  · apply (affineRow 1 2).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [hc1.continuousAt.eventually (gt_mem_nhds h1),
      hc2.continuousAt.eventually (lt_mem_nhds h2)] with q hq1 hq2
    rw [actual_four_activation_region_formulae q.1 q.2 |>.2.1 hq1.le hq2.le]
    simp [affineRow]
  · apply (affineRow 1 (-2)).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [hc1.continuousAt.eventually (lt_mem_nhds h1),
      hc2.continuousAt.eventually (gt_mem_nhds h2)] with q hq1 hq2
    rw [actual_four_activation_region_formulae q.1 q.2 |>.2.2.1 hq1.le hq2.le]
    simp [affineRow,sub_eq_add_neg]
  · apply (affineRow 2 0).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [hc1.continuousAt.eventually (gt_mem_nhds h1),
      hc2.continuousAt.eventually (gt_mem_nhds h2)] with q hq1 hq2
    rw [actual_four_activation_region_formulae q.1 q.2 |>.2.2.2 hq1.le hq2.le]
    simp [affineRow]

theorem actual_four_open_regions_are_nonempty :
    ∃ p00 p10 p01 p11 : ℝ×ℝ,
      p00.1+2*p00.2 < 0 ∧ p00.1-2*p00.2 < 0 ∧
      0 < p10.1+2*p10.2 ∧ p10.1-2*p10.2 < 0 ∧
      p01.1+2*p01.2 < 0 ∧ 0 < p01.1-2*p01.2 ∧
      0 < p11.1+2*p11.2 ∧ 0 < p11.1-2*p11.2 := by
  refine ⟨(-1,0),(0,1),(0,-1),(1,0),?_⟩
  norm_num

theorem actual_physical_box_bound (x y xb yb r : ℝ) (hr : 0 ≤ r)
    (hx : |x-xb| ≤ r) (hy : |y-yb| ≤ r) :
    |normalizedCorrection x y-normalizedCorrection xb yb| ≤ 3*r := by
  rw [actual_physical_correction_is_max_of_four_affine_regions,
    actual_physical_correction_is_max_of_four_affine_regions]
  apply abs_max_pair_bound
  · apply abs_max_pair_bound
    · simp;positivity
    · have he : 2*x-2*xb=2*(x-xb) := by ring
      rw [he,abs_mul]
      norm_num
      linarith
  · apply abs_max_pair_bound
    · have he : (x+2*y)-(xb+2*yb)=(x-xb)+2*(y-yb) := by ring
      rw [he]
      calc
        _ ≤ |x-xb|+|2*(y-yb)| := abs_add_le _ _
        _ ≤ 3*r := by rw [abs_mul];norm_num;linarith
    · have he : (x-2*y)-(xb-2*yb)=(x-xb)-2*(y-yb) := by ring
      rw [he]
      calc
        _ ≤ |x-xb|+|2*(y-yb)| := abs_sub _ _
        _ ≤ 3*r := by rw [abs_mul];norm_num;linarith

theorem actual_hardware_exact_box_error_bound (T d Tb db : ℝ)
    (hT : |T-Tb| ≤ 1/5) (hd : |d-db| ≤ 1/500) :
    |physicalCorrection T d-physicalCorrection Tb db| ≤ 3/50 := by
  have h:=actual_hardware_error_box_is_normalized T d Tb db hT hd
  simpa only [physicalCorrection,show (3:ℝ)*(1/50)=3/50 by norm_num] using
    actual_physical_box_bound _ _ _ _ _ (by norm_num) h.1 h.2

theorem actual_hardware_error_allowance_is_attained_in_one_active_region :
    |(201/5:ℝ)-40|=1/5 ∧ |(301/500:ℝ)-3/5|=1/500 ∧
    0 < normalizeTemperature (201/5)+2*normalizeDistance (301/500) ∧
    normalizeTemperature (201/5)-2*normalizeDistance (301/500) < 0 ∧
    |physicalCorrection (201/5) (301/500)-physicalCorrection 40 (3/5)|=3/50 := by
  norm_num [normalizeTemperature,normalizeDistance,physicalCorrection,normalizedCorrection]

theorem actual_regional_gradient_l1_norms :
    |(0:ℝ)|+|0|=0 ∧ |(1:ℝ)|+|2|=3 ∧ |(1:ℝ)|+|-2|=3 ∧
    |(2:ℝ)|+|0|=2 ∧ max (max 0 3) (max 3 (2:ℝ))=3 := by norm_num

theorem actual_sdp_bound_square_and_sign : sdpBound^2=8/1875 ∧ 0<sdpBound := by
  constructor
  · dsimp [sdpBound]
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4/3),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  · dsimp [sdpBound];positivity

theorem actual_sdp_and_radius_six_decimal_roundings_and_rejection :
    |Real.sqrt 2*(1/50)-28284/10^6|<1/(2*10^6) ∧
    |sdpBound-65320/10^6|<1/(2*10^6) ∧ (3/50:ℝ)<sdpBound := by
  have hs:=actual_sdp_bound_square_and_sign
  have hr:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp:=Real.sqrt_nonneg 2
  constructor
  · rw [abs_lt];constructor <;> nlinarith
  constructor
  · rw [abs_lt];constructor <;> nlinarith [sq_nonneg (sdpBound-65320/10^6)]
  · nlinarith

theorem actual_exact_scaling_threshold_is_three_sqrt_six_over_eight :
    scalingThreshold=3*Real.sqrt 6/8 := by
  have hs:=actual_sdp_bound_square_and_sign
  have h6:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  have hp : 0 ≤ 3*Real.sqrt 6/8 := by positivity
  have he : (3*Real.sqrt 6/8*sdpBound)^2=(3/50:ℝ)^2 := by
    rw [mul_pow,div_pow,mul_pow,h6,hs.1]
    norm_num
  have he' : 3*Real.sqrt 6/8*sdpBound=3/50 :=
    (sq_eq_sq₀ (mul_nonneg hp hs.2.le) (by norm_num)).mp he
  dsimp [scalingThreshold]
  apply (div_eq_iff hs.2.ne').mpr
  linarith

theorem actual_scaled_sdp_allowance_iff_exact_threshold (s : ℝ) :
    s*sdpBound ≤ 3/50 ↔ s ≤ scalingThreshold := by
  dsimp [scalingThreshold]
  exact (le_div_iff₀ actual_sdp_bound_square_and_sign.2).symm

theorem actual_exact_threshold_rounds_to_the_source_target :
    |scalingThreshold-918559/10^6|<1/(2*10^6) := by
  rw [actual_exact_scaling_threshold_is_three_sqrt_six_over_eight]
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  have hp:=Real.sqrt_nonneg 6
  rw [abs_lt]
  constructor <;> nlinarith

theorem actual_scaled_hardware_sdp_bound (T d Tb db s : ℝ) (hs : 0 ≤ s)
    (hT : |T-Tb| ≤ s/5) (hd : |d-db| ≤ s/500) :
    |physicalCorrection T d-physicalCorrection Tb db| ≤ s*sdpBound := by
  have he:=actual_preprocessing_difference_equalities T d Tb db
  have h : |normalizeTemperature T-normalizeTemperature Tb| ≤ s/50 ∧
      |normalizeDistance d-normalizeDistance db| ≤ s/50 := by
    rw [he.1,he.2,abs_div,abs_mul]
    norm_num
    constructor <;> linarith
  have hx2:=sq_le_sq₀ (abs_nonneg (normalizeTemperature T-normalizeTemperature Tb))
    (by positivity : (0:ℝ) ≤ s/50) |>.mpr h.1
  have hy2:=sq_le_sq₀ (abs_nonneg (normalizeDistance d-normalizeDistance db))
    (by positivity : (0:ℝ) ≤ s/50) |>.mpr h.2
  rw [sq_abs] at hx2 hy2
  have hinput : (normalizeTemperature T-normalizeTemperature Tb)^2+
      (normalizeDistance d-normalizeDistance db)^2 ≤ (s*(Real.sqrt 2*(1/50)))^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith
  have hb:=actual_physical_sdp_bound _ _ _ _ _ (by positivity) hinput
  change |physicalCorrection T d-physicalCorrection Tb db| ≤ _ at hb
  convert hb using 1 <;> dsimp [sdpBound] <;> ring

theorem actual_scaled_hardware_is_sdp_certified_at_the_threshold
    (T d Tb db s : ℝ) (hs : 0 ≤ s) (hscale : s ≤ scalingThreshold)
    (hT : |T-Tb| ≤ s/5) (hd : |d-db| ≤ s/500) :
    |physicalCorrection T d-physicalCorrection Tb db| ≤ 3/50 := by
  exact (actual_scaled_hardware_sdp_bound T d Tb db s hs hT hd).trans
    ((actual_scaled_sdp_allowance_iff_exact_threshold s).mpr hscale)

theorem actual_raw_unit_euclidean_radius_is_different_from_normalized_radius :
    (1/5:ℝ)^2+(1/500)^2=10001/250000 ∧
    (1/50:ℝ)^2+(1/50)^2=1/1250 ∧
    (1/5:ℝ)^2+(1/500)^2 ≠ (1/50:ℝ)^2+(1/50)^2 := by norm_num

theorem actual_rounded_denominator_has_a_different_six_decimal_quotient :
    |((3/50:ℝ)/(65320/10^6))-918555/10^6|<1/(2*10^6) ∧
    1/(2*10^6) < |((3/50:ℝ)/(65320/10^6))-918559/10^6| := by norm_num

end SafeLearning.CompleteModulesPhysicalSensorBox28
