import SafeLearning.Modules

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Matrix

namespace SafeLearning.CompleteModulesCrownOtherRadii28

private theorem relu_interval_sound (lo hi x : ℝ) (h : x∈Icc lo hi) :
    max x 0∈Icc (max lo 0) (max hi 0) := by
  exact ⟨max_le_max h.1 le_rfl,max_le_max h.2 le_rfl⟩

private theorem linear_gradient_box (a b dx dy r : ℝ)
    (hx : |dx|≤r) (hy : |dy|≤r) : |a*dx+b*dy|≤(|a|+|b|)*r := by
  calc
    |a*dx+b*dy|≤|a*dx|+|b*dy| := abs_add_le _ _
    _=|a| *|dx|+|b| *|dy| := by rw [abs_mul,abs_mul]
    _≤(|a|+|b|)*r := by
      nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg a),
        mul_le_mul_of_nonneg_left hy (abs_nonneg b)]

private theorem relu_lower_line_general (slope x : ℝ) (hs : slope∈Icc 0 1) :
    slope*x≤max x 0 := by
  by_cases hp : 0≤x
  · rw [max_eq_left hp];nlinarith [hs.2]
  · rw [max_eq_right (le_of_not_ge hp)]
    exact mul_nonpos_of_nonneg_of_nonpos hs.1 (le_of_not_ge hp)

private theorem relu_triangle_general (lo hi x : ℝ) (hl : lo<0) (hh : 0<hi)
    (hx : x∈Icc lo hi) : max x 0≤hi*(x-lo)/(hi-lo) := by
  have hd : 0<hi-lo := by linarith
  apply (le_div_iff₀ hd).mpr
  by_cases hp : 0≤x
  · rw [max_eq_left hp]
    have hm:=mul_nonneg (by linarith : 0≤-lo) (by linarith [hx.2] : 0≤hi-x)
    nlinarith
  · rw [max_eq_right (le_of_not_ge hp)]
    have hm:=mul_nonneg (le_of_lt hh) (by linarith [hx.1] : 0≤x-lo)
    nlinarith

abbrev V := Fin 2 → ℝ
def sourceW : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;-1,2]
def sourceB : V := ![1,1]
def sourceOutputW : V := ![-2,2]
def sourceBox (epsilon : ℝ) : Set V := {x | ∀j,1-epsilon≤x j ∧ x j≤1+epsilon}
def preactivation (x : V) : V := ![x 0+x 1+1,-x 0+2*x 1+1]
def output (x : V) : ℝ := -2*max (preactivation x 0) 0+2*max (preactivation x 1) 0
def preLo (epsilon : ℝ) : V := ![3-2*epsilon,2-3*epsilon]
def preHi (epsilon : ℝ) : V := ![3+2*epsilon,2+3*epsilon]
def hiddenLo (epsilon : ℝ) : V := fun j=>max (preLo epsilon j) 0
def hiddenHi (epsilon : ℝ) : V := fun j=>max (preHi epsilon j) 0
def ibpInterval (epsilon : ℝ) : Set ℝ :=
  Icc (-2*hiddenHi epsilon 0+2*hiddenLo epsilon 1)
    (-2*hiddenLo epsilon 0+2*hiddenHi epsilon 1)
def lowerLine (alpha : ℝ) (x : V) : ℝ :=
  -2*preactivation x 0+2*alpha*preactivation x 1
def upperLine (x : V) : ℝ :=
  -2*preactivation x 0+2*((13/18)*(preactivation x 1+5/2))
def lowerOmega (alpha : ℝ) : V := ![-2-2*alpha,-2+4*alpha]
def lowerConstant (alpha : ℝ) : ℝ := -2+2*alpha
def lowerGamma (alpha : ℝ) : ℝ := -9+alpha-(3/2)*|4*alpha-2|
def upperLambda : V := ![-31/9,8/9]
def upperConstant : ℝ := 55/18

theorem actual_source_first_matrix_layer (x : V) :
    sourceW *ᵥ x+sourceB=preactivation x := by
  ext j
  fin_cases j <;> simp [sourceW,sourceB,preactivation,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem actual_source_output_matrix_layer (x : V) :
    sourceOutputW ⬝ᵥ (fun j=>max (preactivation x j) 0)=output x := by
  simp [sourceOutputW,dotProduct,Fin.sum_univ_succ,output]

theorem actual_source_affine_center_and_radius (epsilon : ℝ) :
    sourceW *ᵥ (![1,1]:V)+sourceB=![3,2] ∧
    (fun i=>∑ j,|sourceW i j| *epsilon)=(![2*epsilon,3*epsilon]:V) := by
  constructor
  · rw [actual_source_first_matrix_layer];norm_num [preactivation]
  · ext i
    fin_cases i <;> simp [sourceW,Fin.sum_univ_succ] <;> ring

theorem actual_source_preactivation_bounds (epsilon : ℝ) (x : V)
    (hx : x∈sourceBox epsilon) :
    ∀j,preLo epsilon j≤preactivation x j ∧ preactivation x j≤preHi epsilon j := by
  have h0:=hx 0
  have h1:=hx 1
  intro j
  fin_cases j
  · change 3-2*epsilon≤x 0+x 1+1 ∧ x 0+x 1+1≤3+2*epsilon
    constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]
  · change 2-3*epsilon≤-x 0+2*x 1+1 ∧ -x 0+2*x 1+1≤2+3*epsilon
    constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

theorem actual_source_coordinate_bounds_have_feasible_corners (epsilon : ℝ)
    (he : 0≤epsilon) :
    (![1-epsilon,1-epsilon]:V)∈sourceBox epsilon ∧
    (![1+epsilon,1+epsilon]:V)∈sourceBox epsilon ∧
    (![1+epsilon,1-epsilon]:V)∈sourceBox epsilon ∧
    (![1-epsilon,1+epsilon]:V)∈sourceBox epsilon ∧
    preactivation (![1-epsilon,1-epsilon]:V) 0=preLo epsilon 0 ∧
    preactivation (![1+epsilon,1+epsilon]:V) 0=preHi epsilon 0 ∧
    preactivation (![1+epsilon,1-epsilon]:V) 1=preLo epsilon 1 ∧
    preactivation (![1-epsilon,1+epsilon]:V) 1=preHi epsilon 1 := by
  repeat' constructor
  all_goals first
  | intro j;fin_cases j <;> simp <;> linarith
  | simp [preactivation,preLo,preHi];ring

theorem actual_source_ibp_is_sound (epsilon : ℝ) (x : V)
    (hx : x∈sourceBox epsilon) : output x∈ibpInterval epsilon := by
  have h:=actual_source_preactivation_bounds epsilon x hx
  have h0:=relu_interval_sound (preLo epsilon 0)
    (preHi epsilon 0) (preactivation x 0) (h 0)
  have h1:=relu_interval_sound (preLo epsilon 1)
    (preHi epsilon 1) (preactivation x 1) (h 1)
  change -2*max (preHi epsilon 0) 0+2*max (preLo epsilon 1) 0≤
      -2*max (preactivation x 0) 0+2*max (preactivation x 1) 0 ∧
    -2*max (preactivation x 0) 0+2*max (preactivation x 1) 0≤
      -2*max (preLo epsilon 0) 0+2*max (preHi epsilon 1) 0
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

theorem actual_source_both_radii_bounds_and_hidden_intervals :
    preLo (1/2)=(![2,1/2]:V) ∧ preHi (1/2)=(![4,7/2]:V) ∧
    hiddenLo (1/2)=(![2,1/2]:V) ∧ hiddenHi (1/2)=(![4,7/2]:V) ∧
    preLo (3/2)=(![0,-5/2]:V) ∧ preHi (3/2)=(![6,13/2]:V) ∧
    hiddenLo (3/2)=(![0,0]:V) ∧ hiddenHi (3/2)=(![6,13/2]:V) := by
  repeat' constructor
  all_goals ext j;fin_cases j <;> norm_num [preLo,preHi,hiddenLo,hiddenHi]

theorem actual_source_both_radii_neuron_statuses :
    (∀j,0<preLo (1/2) j) ∧
    0≤preLo (3/2) 0 ∧ preLo (3/2) 1<0 ∧ 0<preHi (3/2) 1 ∧
    |preLo (3/2) 1|≤preHi (3/2) 1 := by
  constructor
  · intro j;fin_cases j <;> norm_num [preLo]
  · norm_num [preLo,preHi]

theorem actual_source_both_ibp_intervals :
    ibpInterval (1/2)=Icc (-7) 3 ∧ ibpInterval (3/2)=Icc (-12) 13 := by
  norm_num [ibpInterval,hiddenLo,hiddenHi,preLo,preHi]

theorem actual_half_radius_output_is_affine (x : V) (hx : x∈sourceBox (1/2)) :
    output x=-4*x 0+2*x 1 := by
  have h:=actual_source_preactivation_bounds (1/2) x hx
  have h0 : 0≤preactivation x 0 := by have hh:=(h 0).1;norm_num [preLo] at hh;linarith
  have h1 : 0≤preactivation x 1 := by have hh:=(h 1).1;norm_num [preLo] at hh;linarith
  rw [output,max_eq_left h0,max_eq_left h1]
  simp [preactivation]
  ring

theorem actual_half_radius_crown_and_exact_bounds (x : V)
    (hx : x∈sourceBox (1/2)) : output x∈Icc (-5) 1 := by
  rw [actual_half_radius_output_is_affine x hx]
  have h0:=hx 0
  have h1:=hx 1
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

theorem actual_half_radius_crown_row_center_and_l1 :
    (![-4,2]:V) ⬝ᵥ (![1,1]:V)=-2 ∧
    ∑j,|(![-4,2]:V) j|=6 ∧ (-2-(1/2)*6:ℝ)=-5 ∧ (-2+(1/2)*6:ℝ)=1 := by
  norm_num [dotProduct,Fin.sum_univ_succ]

theorem actual_half_radius_full_exact_image : output '' sourceBox (1/2)=Icc (-5) 1 := by
  ext t
  constructor
  · rintro ⟨x,hx,rfl⟩;exact actual_half_radius_crown_and_exact_bounds x hx
  · rintro ⟨hl,hh⟩
    let s:ℝ:=(t+5)/6
    have hs0 : 0≤s := by dsimp [s];linarith
    have hs1 : s≤1 := by dsimp [s];linarith
    let x:V:=![3/2-s,1/2+s]
    have hx : x∈sourceBox (1/2) := by
      intro j
      fin_cases j
      · change 1-1/2≤3/2-s ∧ 3/2-s≤1+1/2;constructor <;> linarith
      · change 1-1/2≤1/2+s ∧ 1/2+s≤1+1/2;constructor <;> linarith
    refine ⟨x,hx,?_⟩
    rw [actual_half_radius_output_is_affine x hx]
    dsimp [x,s]
    ring

theorem actual_half_radius_extrema_are_at_source_points :
    (![3/2,1/2]:V)∈sourceBox (1/2) ∧ output (![3/2,1/2]:V)=-5 ∧
    (![1/2,3/2]:V)∈sourceBox (1/2) ∧ output (![1/2,3/2]:V)=1 := by
  repeat' constructor
  · intro j;fin_cases j <;> norm_num
  · norm_num [output,preactivation]
  · intro j;fin_cases j <;> norm_num
  · norm_num [output,preactivation]

theorem actual_three_halves_lower_crown_line_is_sound (alpha : ℝ) (x : V)
    (halpha : alpha∈Icc 0 1) (hx : x∈sourceBox (3/2)) :
    lowerLine alpha x≤output x := by
  have h:=actual_source_preactivation_bounds (3/2) x hx
  have h0 : 0≤preactivation x 0 := by simpa [preLo] using (h 0).1
  have hl:=relu_lower_line_general alpha (preactivation x 1) halpha
  rw [output,max_eq_left h0]
  dsimp [lowerLine]
  linarith

theorem actual_three_halves_lower_crown_coefficients (alpha : ℝ) (x : V) :
    lowerLine alpha x=lowerOmega alpha ⬝ᵥ x+lowerConstant alpha := by
  simp [lowerLine,preactivation,lowerOmega,lowerConstant,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_three_halves_lower_crown_box_support (alpha : ℝ) (x : V)
    (halpha : alpha∈Icc 0 1) (hx : x∈sourceBox (3/2)) :
    lowerGamma alpha≤lowerLine alpha x := by
  have hx0 : |x 0-1|≤3/2 := by apply abs_le.mpr;constructor <;> linarith [(hx 0).1,(hx 0).2]
  have hx1 : |x 1-1|≤3/2 := by apply abs_le.mpr;constructor <;> linarith [(hx 1).1,(hx 1).2]
  have hb:=linear_gradient_box (-2-2*alpha) (-2+4*alpha)
    (x 0-1) (x 1-1) (3/2) hx0 hx1
  rw [abs_of_nonpos (by linarith [halpha.1] : -2-2*alpha≤0)] at hb
  have hl:=abs_le.mp hb |>.1
  dsimp [lowerGamma,lowerLine,preactivation]
  have he : (-2+4*alpha)=(4*alpha-2) := by ring
  rw [he] at hl
  nlinarith

theorem actual_three_halves_lower_gamma_source_formula (alpha : ℝ) :
    lowerGamma alpha=-6+4*alpha-(3/2)*(2+2*alpha+|4*alpha-2|) := by
  dsimp [lowerGamma]
  ring

theorem actual_three_halves_alpha_source_values_and_optimum :
    lowerGamma 0=-12 ∧ lowerGamma 1=-11 ∧ lowerGamma (1/2)=-17/2 ∧
    IsGreatest (lowerGamma '' Icc 0 1) (-17/2) := by
  refine ⟨by norm_num [lowerGamma],by norm_num [lowerGamma],by norm_num [lowerGamma],?_,?_⟩
  · exact ⟨1/2,by norm_num,by norm_num [lowerGamma]⟩
  · rintro t ⟨alpha,halpha,rfl⟩
    dsimp [lowerGamma]
    by_cases h : alpha≤1/2
    · rw [abs_of_nonpos (by linarith : 4*alpha-2≤0)];linarith
    · rw [abs_of_nonneg (by linarith : 0≤4*alpha-2)];linarith

theorem actual_three_halves_upper_chord_is_sound (x : V)
    (hx : x∈sourceBox (3/2)) : output x≤upperLine x := by
  have h:=actual_source_preactivation_bounds (3/2) x hx
  have h0 : 0≤preactivation x 0 := by simpa [preLo] using (h 0).1
  have hz : preactivation x 1∈Icc (-5/2) (13/2) := by simpa [preLo,preHi] using h 1
  have hc:=relu_triangle_general (-5/2) (13/2) (preactivation x 1)
    (by norm_num) (by norm_num) hz
  norm_num at hc
  rw [output,max_eq_left h0]
  dsimp [upperLine]
  linarith

theorem actual_three_halves_upper_crown_coefficients (x : V) :
    upperLine x=upperLambda ⬝ᵥ x+upperConstant := by
  simp [upperLine,preactivation,upperLambda,upperConstant,dotProduct,Fin.sum_univ_succ]
  ring

theorem actual_three_halves_upper_crown_box_support (x : V)
    (hx : x∈sourceBox (3/2)) : upperLine x≤7 := by
  have h0:=(hx 0).1
  have h1:=(hx 1).2
  dsimp [upperLine,preactivation]
  linarith

theorem actual_three_halves_upper_center_l1_and_gamma :
    upperLambda ⬝ᵥ (![1,1]:V)+upperConstant=1/2 ∧
    ∑j,|upperLambda j|=39/9 ∧ (1/2+(3/2)*(39/9):ℝ)=7 := by
  norm_num [upperLambda,upperConstant,dotProduct,Fin.sum_univ_succ]

theorem actual_three_halves_crown_and_alpha_intervals (x : V)
    (hx : x∈sourceBox (3/2)) :
    output x∈Icc (-11) 7 ∧ output x∈Icc (-17/2) 7 := by
  have hu:=(actual_three_halves_upper_chord_is_sound x hx).trans
    (actual_three_halves_upper_crown_box_support x hx)
  have hl:=actual_three_halves_lower_crown_box_support 1 x (by norm_num) hx |>.trans
    (actual_three_halves_lower_crown_line_is_sound 1 x (by norm_num) hx)
  have ha:=actual_three_halves_lower_crown_box_support (1/2) x (by norm_num) hx |>.trans
    (actual_three_halves_lower_crown_line_is_sound (1/2) x (by norm_num) hx)
  norm_num [lowerGamma] at hl ha
  exact ⟨⟨hl,hu⟩,⟨ha,hu⟩⟩

theorem actual_three_halves_active_and_inactive_regions (x : V)
    (hx : x∈sourceBox (3/2)) :
    (0≤preactivation x 1 → output x=-4*x 0+2*x 1) ∧
    (preactivation x 1≤0 → output x=-2*x 0-2*x 1-2) := by
  have h:=actual_source_preactivation_bounds (3/2) x hx
  have h0 : 0≤preactivation x 0 := by simpa [preLo] using (h 0).1
  constructor
  · intro h1;rw [output,max_eq_left h0,max_eq_left h1];simp [preactivation];ring
  · intro h1;rw [output,max_eq_left h0,max_eq_right h1];simp [preactivation];ring

theorem actual_three_halves_source_extrema_and_kink :
    (![5/2,3/4]:V)∈sourceBox (3/2) ∧ preactivation (![5/2,3/4]:V) 1=0 ∧
    output (![5/2,3/4]:V)=-17/2 ∧
    (![-1/2,5/2]:V)∈sourceBox (3/2) ∧ output (![-1/2,5/2]:V)=7 := by
  repeat' constructor
  · intro j;fin_cases j <;> norm_num
  · norm_num [preactivation]
  · norm_num [output,preactivation]
  · intro j;fin_cases j <;> norm_num
  · norm_num [output,preactivation]

theorem actual_three_halves_full_exact_image : output '' sourceBox (3/2)=Icc (-17/2) 7 := by
  ext t
  constructor
  · rintro ⟨x,hx,rfl⟩;exact (actual_three_halves_crown_and_alpha_intervals x hx).2
  · rintro ⟨hl,hh⟩
    let s:ℝ:=(2*t+17)/31
    have hs0 : 0≤s := by dsimp [s];linarith
    have hs1 : s≤1 := by dsimp [s];linarith
    let x:V:=![5/2-3*s,3/4+(7/4)*s]
    have hx : x∈sourceBox (3/2) := by
      intro j
      fin_cases j
      · change 1-3/2≤5/2-3*s ∧ 5/2-3*s≤1+3/2;constructor <;> linarith
      · change 1-3/2≤3/4+(7/4)*s ∧ 3/4+(7/4)*s≤1+3/2;constructor <;> linarith
    have hz : 0≤preactivation x 1 := by
      change 0≤-(5/2-3*s)+2*(3/4+(7/4)*s)+1
      linarith
    refine ⟨x,hx,?_⟩
    rw [(actual_three_halves_active_and_inactive_regions x hx).1 hz]
    dsimp [x,s]
    ring

end SafeLearning.CompleteModulesCrownOtherRadii28
