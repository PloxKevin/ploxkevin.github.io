import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal

namespace SafeLearning.CompleteFoundationsCubicGrids

def unitCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}

def gridPoint (d N : ℕ) (k : Fin d → Fin (N+1)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => ((k i : ℕ) : ℝ)/(N : ℝ))

def unitGrid (d N : ℕ) : Finset (EuclideanSpace ℝ (Fin d)) := by
  classical
  exact Finset.univ.image (gridPoint d N)

def gridRadius (d N : ℕ) : ℝ := Real.sqrt d/(2*N)

def cellCenter (d N : ℕ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ => 1/(2*(N : ℝ)))

theorem nearest_coordinate (N : ℕ) (hN : 0<N) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ k : Fin (N+1), |x-(k : ℕ)/(N : ℝ)|≤1/(2*N) := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hx₀ : 0≤x := hx.1
  have hx₁ : x≤1 := hx.2
  let a : ℝ := (N : ℝ)*x+1/2
  have ha : 0≤a := by dsimp [a];positivity
  have hk : Nat.floor a<N+1 := by
    apply (Nat.floor_lt ha).mpr
    push_cast
    dsimp [a]
    nlinarith
  refine ⟨⟨Nat.floor a,hk⟩,?_⟩
  have h₁ := Nat.floor_le ha
  have h₂ := Nat.lt_floor_add_one a
  have hb : |(N : ℝ)*x-(Nat.floor a : ℝ)|≤1/2 := by
    rw [abs_le]
    dsimp [a] at h₁ h₂
    constructor <;> linarith
  change |x-(Nat.floor a : ℝ)/(N : ℝ)|≤1/(2*N)
  have hid : x-(Nat.floor a : ℝ)/(N : ℝ)=((N : ℝ)*x-Nat.floor a)/(N : ℝ) := by
    field_simp
  rw [hid,abs_div,abs_of_pos hNr]
  calc
    _ ≤ (1/2)/(N : ℝ) := div_le_div_of_nonneg_right hb hNr.le
    _ = _ := by ring

theorem grid_point_injective (d N : ℕ) (hN : 0<N) : Function.Injective (gridPoint d N) := by
  intro k l h
  funext i
  have he := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) h
  change ((k i : ℕ) : ℝ)/(N : ℝ)=((l i : ℕ) : ℝ)/(N : ℝ) at he
  have hNr : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  have hc : ((k i : ℕ) : ℝ)=((l i : ℕ) : ℝ) := by
    field_simp at he
    exact he
  apply Fin.ext
  exact_mod_cast hc

theorem grid_cardinality (d N : ℕ) (hN : 0<N) : (unitGrid d N).card=(N+1)^d := by
  classical
  rw [unitGrid,Finset.card_image_of_injective _ (grid_point_injective d N hN)]
  simp

theorem grid_spacing_formula (d N : ℕ) (hN : 0<N) :
    ((unitGrid d N).card : ℝ)=(1/(1/(N : ℝ))+1)^d ∧
    gridRadius d N=(Real.sqrt d/2)*(1/(N : ℝ)) := by
  constructor
  · rw [grid_cardinality d N hN]
    simp
  · unfold gridRadius
    ring

theorem grid_point_in_cube (d N : ℕ) (hN : 0<N) (k : Fin d → Fin (N+1)) :
    gridPoint d N k ∈ unitCube d := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  intro i
  change ((k i : ℕ) : ℝ)/(N : ℝ) ∈ Icc (0 : ℝ) 1
  constructor
  · positivity
  · rw [div_le_iff₀ hNr,one_mul]
    exact_mod_cast Nat.le_of_lt_succ (k i).isLt

theorem grid_members_in_cube (d N : ℕ) (hN : 0<N) :
    ∀ g ∈ unitGrid d N,g ∈ unitCube d := by
  classical
  intro g hg
  rcases Finset.mem_image.mp hg with ⟨k,_,rfl⟩
  exact grid_point_in_cube d N hN k

theorem radius_nonnegative (d N : ℕ) : 0≤gridRadius d N := by
  unfold gridRadius
  positivity

theorem radius_square (d N : ℕ) :
    (gridRadius d N)^2=(d : ℝ)*(1/(2*(N : ℝ)))^2 := by
  rw [gridRadius,div_pow,Real.sq_sqrt (Nat.cast_nonneg d)]
  ring

theorem cube_grid_covers (d N : ℕ) (hN : 0<N) :
    ∀ x ∈ unitCube d,∃ g ∈ unitGrid d N,dist x g≤gridRadius d N := by
  classical
  intro x hx
  have hchoice : ∀ i : Fin d,∃ k : Fin (N+1), |x i-(k : ℕ)/(N : ℝ)|≤1/(2*N) :=
    fun i => nearest_coordinate N hN (x i) (hx i)
  choose k hk using hchoice
  refine ⟨gridPoint d N k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩,?_⟩
  have hs : dist x (gridPoint d N k)^2≤(d : ℝ)*(1/(2*(N : ℝ)))^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ _i : Fin d,(1/(2*(N : ℝ)))^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : dist (x i) (gridPoint d N k i)≤1/(2*(N : ℝ)) := by
          simpa only [gridPoint,PiLp.toLp_apply,Real.dist_eq] using hk i
        exact pow_le_pow_left₀ dist_nonneg hi 2
      _ = _ := by simp
  have hr := radius_square d N
  have hp := radius_nonnegative d N
  nlinarith [dist_nonneg (x := x) (y := gridPoint d N k)]

theorem cell_center_in_cube (d N : ℕ) (hN : 0<N) : cellCenter d N ∈ unitCube d := by
  have hNr : (1 : ℝ)≤N := by exact_mod_cast hN
  intro i
  change 1/(2*(N : ℝ)) ∈ Icc (0 : ℝ) 1
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity)]
    linarith

theorem cell_center_distance_lower (d N : ℕ) (hN : 0<N) :
    ∀ g ∈ unitGrid d N,gridRadius d N≤dist (cellCenter d N) g := by
  classical
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  intro g hg
  rcases Finset.mem_image.mp hg with ⟨k,_,rfl⟩
  have hb : ∀ i : Fin d,1/(2*(N : ℝ))≤dist (cellCenter d N i) (gridPoint d N k i) := by
    intro i
    change 1/(2*(N : ℝ))≤dist (1/(2*(N : ℝ))) (((k i : ℕ) : ℝ)/(N : ℝ))
    rw [Real.dist_eq]
    by_cases hi : (k i : ℕ)=0
    · rw [hi,Nat.cast_zero,zero_div,sub_zero,abs_of_nonneg (by positivity)]
    · have hk : (1 : ℝ)≤(k i : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
      have hdivide : 1/(N : ℝ)≤((k i : ℕ) : ℝ)/(N : ℝ) :=
        div_le_div_of_nonneg_right hk hNr.le
      have heq : 1/(N : ℝ)=2*(1/(2*(N : ℝ))) := by field_simp
      have hneg := neg_le_abs (1/(2*(N : ℝ))-((k i : ℕ) : ℝ)/(N : ℝ))
      linarith
  have hs : (d : ℝ)*(1/(2*(N : ℝ)))^2≤dist (cellCenter d N) (gridPoint d N k)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ = ∑ _i : Fin d,(1/(2*(N : ℝ)))^2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (by positivity) (hb i) 2)
  have hr := radius_square d N
  have hp := radius_nonnegative d N
  nlinarith [dist_nonneg (x := cellCenter d N) (y := gridPoint d N k)]

theorem exact_cube_covering_radius (d N : ℕ) (hN : 0<N) :
    IsLeast {r : ℝ | ∀ x ∈ unitCube d,∃ g ∈ unitGrid d N,dist x g≤r} (gridRadius d N) := by
  refine ⟨cube_grid_covers d N hN,?_⟩
  intro r hr
  rcases hr (cellCenter d N) (cell_center_in_cube d N hN) with ⟨g,hg,hd⟩
  exact (cell_center_distance_lower d N hN g hg).trans hd

theorem grid_margin {d N : ℕ} (hN : 0<N) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (L : ℝ≥0) (s : ℝ) (hf : LipschitzOnWith L f (unitCube d))
    (hs : ∀ g ∈ unitGrid d N,s≤f g) :
    ∀ x ∈ unitCube d,s-(L : ℝ)*gridRadius d N≤f x := by
  intro x hx
  rcases cube_grid_covers d N hN x hx with ⟨g,hg,hclose⟩
  have hb := hf.dist_le_mul g (grid_members_in_cube d N hN g hg) x hx
  rw [Real.dist_eq,dist_comm] at hb
  have ht := (le_abs_self (f g-f x)).trans hb
  have hmul := mul_le_mul_of_nonneg_left hclose L.coe_nonneg
  have hval := hs g hg
  linarith

theorem cell_center_infimum_distance (d N : ℕ) (hN : 0<N) :
    Metric.infDist (cellCenter d N) (unitGrid d N : Set (EuclideanSpace ℝ (Fin d)))=
      gridRadius d N := by
  rcases cube_grid_covers d N hN (cellCenter d N) (cell_center_in_cube d N hN) with
    ⟨g,hg,hd⟩
  apply le_antisymm
  · exact (Metric.infDist_le_dist_of_mem hg).trans hd
  · exact (Metric.le_infDist ⟨g,hg⟩).mpr (fun _ hy => cell_center_distance_lower d N hN _ hy)

def gridMarginExample (d N : ℕ) (L : ℝ≥0) (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  s-(L : ℝ)*Metric.infDist x (unitGrid d N : Set (EuclideanSpace ℝ (Fin d)))

theorem grid_margin_example_lipschitz (d N : ℕ) (L : ℝ≥0) (s : ℝ) :
    LipschitzWith L (gridMarginExample d N L s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (Metric.lipschitz_infDist_pt
    (unitGrid d N : Set (EuclideanSpace ℝ (Fin d)))).dist_le_mul x y
  rw [Real.dist_eq] at hh
  norm_num only [NNReal.coe_one,one_mul] at hh
  have hid : gridMarginExample d N L s x-gridMarginExample d N L s y=
      -(L : ℝ)*(Metric.infDist x (unitGrid d N : Set (EuclideanSpace ℝ (Fin d)))-
        Metric.infDist y (unitGrid d N : Set (EuclideanSpace ℝ (Fin d)))) := by
    unfold gridMarginExample
    ring
  rw [Real.dist_eq,hid,abs_mul,abs_neg,abs_of_nonneg L.coe_nonneg]
  exact mul_le_mul_of_nonneg_left hh L.coe_nonneg

theorem grid_margin_example_samples (d N : ℕ) (L : ℝ≥0) (s : ℝ) :
    ∀ g ∈ unitGrid d N,gridMarginExample d N L s g=s := by
  intro g hg
  simp only [gridMarginExample,Metric.infDist_zero_of_mem hg,mul_zero,sub_zero]

theorem grid_margin_example_center (d N : ℕ) (hN : 0<N) (L : ℝ≥0) (s : ℝ) :
    gridMarginExample d N L s (cellCenter d N)=s-(L : ℝ)*gridRadius d N := by
  rw [gridMarginExample,cell_center_infimum_distance d N hN]

theorem one_dimension_source_margin (f : EuclideanSpace ℝ (Fin 1) → ℝ)
    (hf : LipschitzOnWith 2 f (unitCube 1)) (hs : ∀ g ∈ unitGrid 1 10,3/20≤f g) :
    ∀ x ∈ unitCube 1,1/20≤f x := by
  intro x hx
  have hh := grid_margin (by norm_num : 0<10) f 2 (3/20) hf hs x hx
  norm_num [gridRadius] at hh
  exact hh

theorem one_dimensional_distance (x y : EuclideanSpace ℝ (Fin 1)) :
    dist x y=dist (x 0) (y 0) := by
  rw [EuclideanSpace.dist_eq]
  simp [Real.sqrt_sq,dist_nonneg]

theorem real_one_dimension_source_margin (f : ℝ → ℝ)
    (hf : LipschitzOnWith 2 f (Icc (0 : ℝ) 1))
    (hs : ∀ k : Fin 11,3/20≤f ((k : ℕ)/(10 : ℝ))) :
    ∀ x ∈ Icc (0 : ℝ) 1,1/20≤f x := by
  intro x hx
  rcases nearest_coordinate 10 (by norm_num) x hx with ⟨k,hk⟩
  have hki : (k : ℕ)/(10 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · have hkn : (k : ℕ)≤10 := Nat.le_of_lt_succ k.isLt
      have hkr : (k : ℝ)≤10 := by exact_mod_cast hkn
      linarith
  have hh := hf.dist_le_mul x hx ((k : ℕ)/(10 : ℝ)) hki
  rw [Real.dist_eq,Real.dist_eq] at hh
  have ht := (neg_le_abs (f x-f ((k : ℕ)/(10 : ℝ)))).trans hh
  norm_num at hk hh ht
  have hsample := hs k
  linarith

theorem three_dimension_source_margin (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hf : LipschitzOnWith 2 f (unitCube 3)) (hs : ∀ g ∈ unitGrid 3 10,3/20≤f g) :
    ∀ x ∈ unitCube 3,3/20-Real.sqrt 3/10≤f x := by
  intro x hx
  have hh := grid_margin (by norm_num : 0<10) f 2 (3/20) hf hs x hx
  norm_num [gridRadius] at hh
  linarith

theorem sqrt_three_enclosure :
    (1732050/1000000 : ℝ)<Real.sqrt 3 ∧ Real.sqrt 3<(1732051/1000000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

theorem source_grid_decimal_enclosures :
    |((3/20 : ℝ)-Real.sqrt 3/10)-(-23205/1000000)|≤1/2000000 ∧
    |((3/20 : ℝ)/Real.sqrt 3)-(86603/1000000)|≤1/2000000 ∧
    |(1/12 : ℝ)-(83333/1000000)|≤1/2000000 := by
  have he := sqrt_three_enclosure
  have hp : (0 : ℝ)<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · rw [abs_le]
    constructor <;> linarith [he.1,he.2]
  constructor
  · rw [abs_le]
    constructor
    · have hh : (86603/1000000 : ℝ)-1/2000000≤(3/20 : ℝ)/Real.sqrt 3 := by
        rw [le_div_iff₀ hp]
        nlinarith [he.2]
      linarith
    · have hh : (3/20 : ℝ)/Real.sqrt 3≤(86603/1000000 : ℝ)+1/2000000 := by
        rw [div_le_iff₀ hp]
        nlinarith [he.1]
      linarith
  · norm_num

theorem required_three_dimension_spacing (delta : ℝ) :
    0≤(3/20 : ℝ)-Real.sqrt 3*delta ↔ delta≤(3/20 : ℝ)/Real.sqrt 3 := by
  rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<3))]
  constructor <;> intro h <;> linarith

theorem twelve_step_grid_suffices :
    0≤(3/20 : ℝ)-2*gridRadius 3 12 ∧ (unitGrid 3 12).card=2197 := by
  have he := sqrt_three_enclosure
  constructor
  · norm_num [gridRadius]
    linarith [he.2]
  · norm_num [grid_cardinality 3 12 (by norm_num)]

theorem twelve_grid_certifies (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hf : LipschitzOnWith 2 f (unitCube 3)) (hs : ∀ g ∈ unitGrid 3 12,3/20≤f g) :
    ∀ x ∈ unitCube 3,0≤f x := by
  intro x hx
  exact twelve_step_grid_suffices.1.trans (grid_margin (by norm_num) f 2 (3/20) hf hs x hx)

theorem coarse_grid_cannot_certify_nonnegative :
    LipschitzWith 2 (gridMarginExample 3 10 2 (3/20)) ∧
    (∀ g ∈ unitGrid 3 10,gridMarginExample 3 10 2 (3/20) g=3/20) ∧
    cellCenter 3 10 ∈ unitCube 3 ∧ gridMarginExample 3 10 2 (3/20) (cellCenter 3 10)<0 := by
  refine ⟨grid_margin_example_lipschitz 3 10 2 (3/20),grid_margin_example_samples 3 10 2 (3/20),
    cell_center_in_cube 3 10 (by norm_num),?_⟩
  rw [grid_margin_example_center 3 10 (by norm_num)]
  norm_num [gridRadius]
  linarith [sqrt_three_enclosure.1]

theorem positive_function_consistent_with_coarse_samples :
    LipschitzWith 2 (fun _ : EuclideanSpace ℝ (Fin 3) => (3/20 : ℝ)) ∧
    (∀ g ∈ unitGrid 3 10,(3/20 : ℝ)≥3/20) ∧
    (∀ x ∈ unitCube 3,(0 : ℝ)<(fun _ : EuclideanSpace ℝ (Fin 3) => (3/20 : ℝ)) x) := by
  refine ⟨LipschitzWith.const' _,fun _ _ => le_refl _,fun _ _ => by norm_num⟩

theorem teaching_grid_cardinalities :
    (unitGrid 1 10).card=11 ∧ (unitGrid 6 10).card=1771561 ∧
    (1750000 : ℕ)<(unitGrid 6 10).card ∧ (unitGrid 6 10).card<1850000 := by
  norm_num [grid_cardinality _ _ (by norm_num : 0<10)]

end SafeLearning.CompleteFoundationsCubicGrids
