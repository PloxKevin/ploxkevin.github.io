import SafeLearning.CompleteFoundationsBalancedSensorReconstruction27

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators Matrix ENNReal

namespace SafeLearning.CompleteModulesAffineIBP28

def box {ι : Type*} (lo hi : ι → ℝ) : Set (ι → ℝ) :=
  {x | ∀ j, lo j ≤ x j ∧ x j ≤ hi j}
def center {ι : Type*} (lo hi : ι → ℝ) : ι → ℝ := fun j => (hi j+lo j)/2
def radius {ι : Type*} (lo hi : ι → ℝ) : ι → ℝ := fun j => (hi j-lo j)/2
def affine {ι κ : Type*} [Fintype ι] (W : Matrix κ ι ℝ) (b : κ → ℝ)
    (a : ι → ℝ) : κ → ℝ := W *ᵥ a+b
def outputRadius {ι κ : Type*} [Fintype ι] (W : Matrix κ ι ℝ)
    (lo hi : ι → ℝ) : κ → ℝ := fun i => ∑ j, |W i j| *radius lo hi j
def upperCorner {ι κ : Type*} (W : Matrix κ ι ℝ) (lo hi : ι → ℝ)
    (i : κ) : ι → ℝ := fun j =>
  center lo hi j+(if 0≤W i j then radius lo hi j else -radius lo hi j)
def lowerCorner {ι κ : Type*} (W : Matrix κ ι ℝ) (lo hi : ι → ℝ)
    (i : κ) : ι → ℝ := fun j =>
  center lo hi j-(if 0≤W i j then radius lo hi j else -radius lo hi j)

theorem original_ordered_box_has_nonnegative_radius {ι : Type*}
    (lo hi : ι → ℝ) (h : ∀ j,lo j≤hi j) : ∀ j,0≤radius lo hi j := by
  intro j
  dsimp [radius]
  linarith [h j]

theorem original_box_exact_center_radius {ι : Type*} (lo hi a : ι → ℝ) :
    a∈box lo hi ↔ ∀ j,|a j-center lo hi j|≤radius lo hi j := by
  constructor
  · intro h j
    rcases h j with ⟨hl,hh⟩
    rw [abs_le]
    dsimp [center,radius]
    constructor <;> linarith
  · intro h j
    rcases abs_le.mp (h j) with ⟨hl,hh⟩
    dsimp [center,radius] at hl hh
    constructor <;> linarith

theorem actual_finite_matrix_center_radius_sound {ι κ : Type*} [Fintype ι]
    (W : Matrix κ ι ℝ) (b : κ → ℝ) (lo hi a : ι → ℝ)
    (ha : a∈box lo hi) (i : κ) :
    |affine W b a i-affine W b (center lo hi) i|≤outputRadius W lo hi i := by
  have h := (original_box_exact_center_radius lo hi a).mp ha
  have he : affine W b a i-affine W b (center lo hi) i =
      ∑ j,W i j*(a j-center lo hi j) := by
    simp [affine,Matrix.mulVec,dotProduct,mul_sub,Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ j,|W i j*(a j-center lo hi j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ outputRadius W lo hi i := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)

theorem actual_finite_matrix_ibp_interval {ι κ : Type*} [Fintype ι]
    (W : Matrix κ ι ℝ) (b : κ → ℝ) (lo hi a : ι → ℝ)
    (ha : a∈box lo hi) :
    affine W b a∈box (affine W b (center lo hi)-outputRadius W lo hi)
      (affine W b (center lo hi)+outputRadius W lo hi) := by
  intro i
  rcases abs_le.mp (actual_finite_matrix_center_radius_sound W b lo hi a ha i) with ⟨hl,hh⟩
  change affine W b (center lo hi) i-outputRadius W lo hi i≤affine W b a i ∧
    affine W b a i≤affine W b (center lo hi) i+outputRadius W lo hi i
  constructor <;> linarith

theorem actual_upper_sign_corner_is_in_original_box {ι κ : Type*}
    (W : Matrix κ ι ℝ) (lo hi : ι → ℝ) (h : ∀j,lo j≤hi j) (i : κ) :
    upperCorner W lo hi i∈box lo hi := by
  intro j
  dsimp [upperCorner,center,radius]
  split_ifs <;> constructor <;> linarith [h j]

theorem actual_lower_sign_corner_is_in_original_box {ι κ : Type*}
    (W : Matrix κ ι ℝ) (lo hi : ι → ℝ) (h : ∀j,lo j≤hi j) (i : κ) :
    lowerCorner W lo hi i∈box lo hi := by
  intro j
  dsimp [lowerCorner,center,radius]
  split_ifs <;> constructor <;> linarith [h j]

theorem actual_upper_sign_corner_attains_matrix_coordinate {ι κ : Type*} [Fintype ι]
    (W : Matrix κ ι ℝ) (b : κ → ℝ) (lo hi : ι → ℝ) (i : κ) :
    affine W b (upperCorner W lo hi i) i =
      affine W b (center lo hi) i+outputRadius W lo hi i := by
  have hs : (∑ j,W i j*upperCorner W lo hi i j) =
      (∑ j,W i j*center lo hi j)+∑ j,|W i j| *radius lo hi j := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [upperCorner]
    split_ifs with h
    · rw [abs_of_nonneg h];ring
    · rw [abs_of_nonpos (le_of_not_ge h)];ring
  dsimp [affine,Matrix.mulVec,dotProduct,outputRadius]
  rw [hs]
  ring

theorem actual_lower_sign_corner_attains_matrix_coordinate {ι κ : Type*} [Fintype ι]
    (W : Matrix κ ι ℝ) (b : κ → ℝ) (lo hi : ι → ℝ) (i : κ) :
    affine W b (lowerCorner W lo hi i) i =
      affine W b (center lo hi) i-outputRadius W lo hi i := by
  have hs : (∑ j,W i j*lowerCorner W lo hi i j) =
      (∑ j,W i j*center lo hi j)-∑ j,|W i j| *radius lo hi j := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [lowerCorner]
    split_ifs with h
    · rw [abs_of_nonneg h];ring
    · rw [abs_of_nonpos (le_of_not_ge h)];ring
  dsimp [affine,Matrix.mulVec,dotProduct,outputRadius]
  rw [hs]
  ring

theorem actual_finite_matrix_attained_coordinate_extrema {ι κ : Type*} [Fintype ι]
    (W : Matrix κ ι ℝ) (b : κ → ℝ) (lo hi : ι → ℝ)
    (h : ∀j,lo j≤hi j) (i : κ) :
    IsGreatest {t:ℝ | ∃a∈box lo hi,t=affine W b a i}
      (affine W b (center lo hi) i+outputRadius W lo hi i) ∧
    IsLeast {t:ℝ | ∃a∈box lo hi,t=affine W b a i}
      (affine W b (center lo hi) i-outputRadius W lo hi i) := by
  constructor
  · constructor
    · exact ⟨upperCorner W lo hi i,actual_upper_sign_corner_is_in_original_box W lo hi h i,
        (actual_upper_sign_corner_attains_matrix_coordinate W b lo hi i).symm⟩
    · rintro t ⟨a,ha,rfl⟩
      exact (actual_finite_matrix_ibp_interval W b lo hi a ha i).2
  · constructor
    · exact ⟨lowerCorner W lo hi i,actual_lower_sign_corner_is_in_original_box W lo hi h i,
        (actual_lower_sign_corner_attains_matrix_coordinate W b lo hi i).symm⟩
    · rintro t ⟨a,ha,rfl⟩
      exact (actual_finite_matrix_ibp_interval W b lo hi a ha i).1

abbrev V := Fin 2 → ℝ
def W : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,-1]
def inputSquare : Set V := box (fun _=>-1) (fun _=>1)
def ibpSquare : Set V := box (fun _=>-2) (fun _=>2)
def diamond : Set V := {z | |z 0|+|z 1|≤2}
def trueImage : Set V := (W.mulVec) '' inputSquare

theorem actual_source_matrix_coordinate_action (a : V) :
    W *ᵥ a=![a 0+a 1,a 0-a 1] := by
  ext i
  fin_cases i <;> simp [W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,sub_eq_add_neg]

theorem actual_source_center_radius_and_ibp_box :
    center (fun _:Fin 2=>-1) (fun _=>1)=0 ∧
    radius (fun _:Fin 2=>-1) (fun _=>1)=1 ∧
    outputRadius W (fun _=>-1) (fun _=>1)=(fun _=>2) ∧
    box (affine W 0 (center (fun _=>-1) (fun _=>1))-outputRadius W (fun _=>-1) (fun _=>1))
      (affine W 0 (center (fun _=>-1) (fun _=>1))+outputRadius W (fun _=>-1) (fun _=>1)) =
        ibpSquare := by
  have hc : center (fun _:Fin 2=>-1) (fun _=>1)=0 := by ext i;norm_num [center]
  have hr : radius (fun _:Fin 2=>-1) (fun _=>1)=1 := by ext i;norm_num [radius]
  have ho : outputRadius W (fun _=>-1) (fun _=>1)=(fun _=>2) := by
    ext i;fin_cases i <;> norm_num [outputRadius,radius,W,Fin.sum_univ_succ]
  refine ⟨hc,hr,ho,?_⟩
  rw [hc,ho]
  ext a
  simp [affine,ibpSquare,box]

theorem actual_source_true_image_iff_diamond (z : V) :
    z∈trueImage ↔ |z 0|+|z 1|≤2 := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    rcases ha 0 with ⟨h0l,h0h⟩
    rcases ha 1 with ⟨h1l,h1h⟩
    rw [actual_source_matrix_coordinate_action]
    change |a 0+a 1|+|a 0-a 1|≤2
    by_cases hp : 0≤a 0+a 1
    · by_cases hq : 0≤a 0-a 1
      · rw [abs_of_nonneg hp,abs_of_nonneg hq];linarith
      · rw [abs_of_nonneg hp,abs_of_nonpos (le_of_not_ge hq)];linarith
    · by_cases hq : 0≤a 0-a 1
      · rw [abs_of_nonpos (le_of_not_ge hp),abs_of_nonneg hq];linarith
      · rw [abs_of_nonpos (le_of_not_ge hp),abs_of_nonpos (le_of_not_ge hq)];linarith
  · intro hz
    refine ⟨![(z 0+z 1)/2,(z 0-z 1)/2],?_,?_⟩
    · intro j
      have ha : |z 0+z 1|≤2 := (abs_add_le _ _).trans hz
      have hb : |z 0-z 1|≤2 := (abs_sub _ _).trans hz
      rcases abs_le.mp ha with ⟨a,b⟩
      rcases abs_le.mp hb with ⟨c,d⟩
      fin_cases j
      · change -1≤(z 0+z 1)/2 ∧ (z 0+z 1)/2≤1
        constructor <;> linarith
      · change -1≤(z 0-z 1)/2 ∧ (z 0-z 1)/2≤1
        constructor <;> linarith
    · rw [actual_source_matrix_coordinate_action]
      ext j
      fin_cases j <;> simp <;> ring

theorem actual_source_true_image_is_diamond : trueImage=diamond := by
  ext z
  exact actual_source_true_image_iff_diamond z

theorem actual_source_four_vertex_images :
    W *ᵥ (![1,1]:V)=![2,0] ∧ W *ᵥ (![-1,-1]:V)=![-2,0] ∧
    W *ᵥ (![1,-1]:V)=![0,2] ∧ W *ᵥ (![-1,1]:V)=![0,-2] := by
  simp only [actual_source_matrix_coordinate_action]
  norm_num

theorem actual_source_ibp_corner_is_unreachable :
    (![2,2]:V)∈ibpSquare ∧ (![2,2]:V)∉trueImage := by
  constructor
  · intro i;fin_cases i <;> norm_num
  · rw [actual_source_true_image_iff_diamond]
    norm_num

theorem actual_source_next_affine_layer_overestimates :
    IsGreatest {t:ℝ | ∃z∈trueImage,t=z 0+z 1} 2 ∧
    IsGreatest {t:ℝ | ∃z∈ibpSquare,t=z 0+z 1} 4 := by
  constructor
  · constructor
    · refine ⟨![2,0],?_,by norm_num⟩
      rw [actual_source_true_image_iff_diamond];norm_num
    · rintro t ⟨z,hz,rfl⟩
      have h := (actual_source_true_image_iff_diamond z).mp hz
      linarith [le_abs_self (z 0),le_abs_self (z 1)]
  · constructor
    · exact ⟨![2,2],actual_source_ibp_corner_is_unreachable.1,by norm_num⟩
    · rintro t ⟨z,hz,rfl⟩
      linarith [(hz 0).2,(hz 1).2]

theorem actual_source_square_volumes :
    volume inputSquare=4 ∧ volume ibpSquare=16 := by
  have h1 : inputSquare=Icc (fun _:Fin 2=>-1) (fun _=>1) := by
    ext a
    constructor
    · intro h;exact ⟨fun j=>(h j).1,fun j=>(h j).2⟩
    · rintro ⟨hl,hh⟩ j;exact ⟨hl j,hh j⟩
  have h2 : ibpSquare=Icc (fun _:Fin 2=>-2) (fun _=>2) := by
    ext a
    constructor
    · intro h;exact ⟨fun j=>(h j).1,fun j=>(h j).2⟩
    · rintro ⟨hl,hh⟩ j;exact ⟨hl j,hh j⟩
  rw [h1,h2,Real.volume_Icc_pi,Real.volume_Icc_pi]
  norm_num [Fin.prod_univ_succ]

theorem actual_source_diamond_is_measurable : MeasurableSet diamond := by
  apply measurableSet_le
  · exact ((measurable_pi_apply 0).abs.add (measurable_pi_apply 1).abs)
  · exact measurable_const

theorem actual_source_matrix_preimage_diamond : W.mulVec ⁻¹' diamond=inputSquare := by
  ext a
  change W *ᵥ a∈diamond ↔ a∈inputSquare
  rw [←actual_source_true_image_is_diamond]
  constructor
  · rintro ⟨x,hx,he⟩
    have h0 := congrArg (fun z:V=>z 0) he
    have h1 := congrArg (fun z:V=>z 1) he
    rw [actual_source_matrix_coordinate_action,actual_source_matrix_coordinate_action] at h0 h1
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
    have hxa : x=a := by
      ext j
      fin_cases j
      · change x 0=a 0;linarith
      · change x 1=a 1;linarith
    simpa [hxa] using hx
  · intro ha;exact ⟨a,ha,rfl⟩

theorem actual_source_determinant_area_of_diamond : volume diamond=8 := by
  have hd : W.det≠0 := by norm_num [W,Matrix.det_fin_two]
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hd
  have he := congrArg (fun m:Measure V=>m diamond) hm
  rw [Measure.map_apply (Matrix.toLin' W).continuous_of_finiteDimensional.measurable
    actual_source_diamond_is_measurable] at he
  change volume (W.mulVec ⁻¹' diamond)=ENNReal.ofReal |W.det⁻¹| *volume diamond at he
  rw [actual_source_matrix_preimage_diamond,actual_source_square_volumes.1] at he
  norm_num [W,Matrix.det_fin_two] at he
  have h := congrArg (fun v:ℝ≥0∞=>(2:ℝ≥0∞)*v) he
  have hc : (2:ℝ≥0∞)*ENNReal.ofReal (1/2:ℝ)=1 := by
    calc
      _=ENNReal.ofReal (2*(1/2:ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _=1 := by norm_num
  norm_num [←mul_assoc,hc] at h
  exact h.symm

theorem actual_source_ibp_area_is_twice_true_image_area :
    volume ibpSquare=16 ∧ volume trueImage=8 ∧
    volume ibpSquare=2*volume trueImage := by
  rw [actual_source_true_image_is_diamond,actual_source_determinant_area_of_diamond,
    actual_source_square_volumes.2]
  norm_num

abbrev E := EuclideanSpace ℝ (Fin 2)
def euclideanTrueImage : Set E := WithLp.toLp 2 '' trueImage
def euclideanIBPBox : Set E := WithLp.toLp 2 '' ibpSquare

theorem actual_euclidean_true_image_coordinate_characterization (z:E) :
    z∈euclideanTrueImage ↔ |z 0|+|z 1|≤2 := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (actual_source_true_image_iff_diamond a).mp ha
  · intro hz
    exact ⟨WithLp.ofLp z,(actual_source_true_image_iff_diamond _).mpr hz,rfl⟩

theorem actual_euclidean_box_and_image_areas :
    volume euclideanIBPBox=16 ∧ volume euclideanTrueImage=8 := by
  have hd : MeasurableSet trueImage := by
    rw [actual_source_true_image_is_diamond];exact actual_source_diamond_is_measurable
  have hb : MeasurableSet ibpSquare := by
    have he : ibpSquare=Icc (fun _:Fin 2=>-2) (fun _=>2) := by
      ext a
      constructor
      · intro h;exact ⟨fun j=>(h j).1,fun j=>(h j).2⟩
      · rintro ⟨hl,hh⟩ j;exact ⟨hl j,hh j⟩
    rw [he]
    exact measurableSet_Icc
  have ht := (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage hd.nullMeasurableSet
  have hs := (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage hb.nullMeasurableSet
  have het : euclideanTrueImage=WithLp.ofLp ⁻¹' trueImage := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩;exact ha
    · intro ha;exact ⟨WithLp.ofLp z,ha,rfl⟩
  have hes : euclideanIBPBox=WithLp.ofLp ⁻¹' ibpSquare := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩;exact ha
    · intro ha;exact ⟨WithLp.ofLp z,ha,rfl⟩
  rw [het,hes]
  constructor
  · exact hs.trans actual_source_square_volumes.2
  · exact ht.trans (by rw [actual_source_true_image_is_diamond];exact actual_source_determinant_area_of_diamond)

end SafeLearning.CompleteModulesAffineIBP28
