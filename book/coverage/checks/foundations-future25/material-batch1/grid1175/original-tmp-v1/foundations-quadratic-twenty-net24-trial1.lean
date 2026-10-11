import Mathlib
import SafeLearning.CompleteFoundationsCubicGrids
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsQuadraticTwentyNet24

def domain : Set ℝ := Icc (-19/20) (19/20)
def h (x : ℝ) : ℝ := 1-x^2
def finePoint (i : Fin 20) : ℝ := -19/20+(i.val:ℝ)/10
def coarsePoint (i : Fin 10) : ℝ := -19/20+(i.val:ℝ)/5
noncomputable def fineGrid : Finset ℝ := by classical exact Finset.univ.image finePoint
noncomputable def coarseGrid : Finset ℝ := by classical exact Finset.univ.image coarsePoint

theorem actual_derivative (x : ℝ) : HasDerivAt h (-2*x) x := by
  convert (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;> simp [h] <;> ring

theorem actual_derivative_maximum_is_attained :
    IsGreatest ((fun x : ℝ => |deriv h x|) '' domain) (19/10) := by
  refine ⟨⟨-19/20,by norm_num [domain],?_⟩,?_⟩
  · rw [(actual_derivative (-19/20)).deriv];norm_num
  · rintro value ⟨x,hx,rfl⟩
    rw [(actual_derivative x).deriv,abs_le]
    rcases hx with ⟨ha,hb⟩
    constructor <;> linarith

theorem actual_lipschitz_bound : LipschitzOnWith (19/10) h domain := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (h x) (h y)≤(19/10:ℝ)*dist x y
  rw [Real.dist_eq,Real.dist_eq]
  have he : h x-h y=(y-x)*(x+y) := by dsimp [h];ring
  rw [he,abs_mul,abs_sub_comm y x]
  have hs : |x+y|≤19/10 := by
    rw [abs_le];constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
  nlinarith [abs_nonneg (x-y)]

theorem actual_fine_nodes_inside (i : Fin 20) : finePoint i ∈ domain := by
  have hi0 : 0≤(i.val:ℝ) := Nat.cast_nonneg _
  have hi19 : (i.val:ℝ)≤19 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  dsimp [finePoint,domain];constructor <;> linarith

theorem actual_coarse_nodes_inside (i : Fin 10) : coarsePoint i ∈ domain := by
  have hi0 : 0≤(i.val:ℝ) := Nat.cast_nonneg _
  have hi9 : (i.val:ℝ)≤9 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  dsimp [coarsePoint,domain];constructor <;> linarith

theorem actual_fine_node_count_and_spacing : fineGrid.card=20 ∧
    ∀ i j : Fin 20,finePoint j-finePoint i=((j.val:ℝ)-i.val)/10 := by
  constructor
  · classical
    have hinj : Function.Injective finePoint := by
      intro i j he
      have hv : (i.val:ℝ)=j.val := by dsimp [finePoint]at he;linarith
      apply Fin.ext;exact_mod_cast hv
    rw [fineGrid,Finset.card_image_of_injective _ hinj]
    simp
  · intro i j;dsimp [finePoint];ring

theorem actual_coarse_node_count_and_spacing : coarseGrid.card=10 ∧
    ∀ i j : Fin 10,coarsePoint j-coarsePoint i=((j.val:ℝ)-i.val)/5 := by
  constructor
  · classical
    have hinj : Function.Injective coarsePoint := by
      intro i j he
      have hv : (i.val:ℝ)=j.val := by dsimp [coarsePoint]at he;linarith
      apply Fin.ext;exact_mod_cast hv
    rw [coarseGrid,Finset.card_image_of_injective _ hinj]
    simp
  · intro i j;dsimp [coarsePoint];ring

theorem actual_fine_twenty_points_cover (x : ℝ) (hx : x∈domain) :
    ∃ i : Fin 20,|x-finePoint i|≤1/20 := by
  by_cases h0 : x≤(0-9)/10
  · refine ⟨⟨0,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h1 : x≤(1-9)/10
  · refine ⟨⟨1,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h2 : x≤(2-9)/10
  · refine ⟨⟨2,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h3 : x≤(3-9)/10
  · refine ⟨⟨3,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h4 : x≤(4-9)/10
  · refine ⟨⟨4,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h5 : x≤(5-9)/10
  · refine ⟨⟨5,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h6 : x≤(6-9)/10
  · refine ⟨⟨6,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h7 : x≤(7-9)/10
  · refine ⟨⟨7,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h8 : x≤(8-9)/10
  · refine ⟨⟨8,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h9 : x≤(9-9)/10
  · refine ⟨⟨9,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h10 : x≤(10-9)/10
  · refine ⟨⟨10,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h11 : x≤(11-9)/10
  · refine ⟨⟨11,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h12 : x≤(12-9)/10
  · refine ⟨⟨12,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h13 : x≤(13-9)/10
  · refine ⟨⟨13,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h14 : x≤(14-9)/10
  · refine ⟨⟨14,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h15 : x≤(15-9)/10
  · refine ⟨⟨15,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h16 : x≤(16-9)/10
  · refine ⟨⟨16,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h17 : x≤(17-9)/10
  · refine ⟨⟨17,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h18 : x≤(18-9)/10
  · refine ⟨⟨18,by decide⟩,?_⟩
    rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]
  refine ⟨⟨19,by decide⟩,?_⟩
  rw [abs_le];norm_num [finePoint];constructor <;> linarith [hx.1,hx.2]

theorem actual_coarse_ten_points_cover (x : ℝ) (hx : x∈domain) :
    ∃ i : Fin 10,|x-coarsePoint i|≤1/10 := by
  by_cases h0 : x≤(0-17)/20
  · refine ⟨⟨0,by decide⟩,?_⟩
    rw [abs_le];norm_num [coarsePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h1 : x≤(4-17)/20
  · refine ⟨⟨1,by decide⟩,?_⟩
    rw [abs_le];norm_num [coarsePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h2 : x≤(8-17)/20
  · refine ⟨⟨2,by decide⟩,?_⟩
    rw [abs_le];norm_num [coarsePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h3 : x≤(12-17)/20
  · refine ⟨⟨3,by decide⟩,?_⟩
    rw [abs_le];norm_num [coarsePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h4 : x≤(16-17)/20
  · refine ⟨⟨4,by decide⟩,?_⟩
    rw [abs_le];norm_num [coarsePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h5 : x≤(20-17)/20
  · refine ⟨⟨5,by decide⟩,?_⟩
    rw [abs_le];norm_num [coarsePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h6 : x≤(24-17)/20
  · refine ⟨⟨6,by decide⟩,?_⟩
    rw [abs_le];norm_num [coarsePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h7 : x≤(28-17)/20
  · refine ⟨⟨7,by decide⟩,?_⟩
    rw [abs_le];norm_num [coarsePoint];constructor <;> linarith [hx.1,hx.2]
  by_cases h8 : x≤(32-17)/20
  · refine ⟨⟨8,by decide⟩,?_⟩
    rw [abs_le];norm_num [coarsePoint];constructor <;> linarith [hx.1,hx.2]
  refine ⟨⟨9,by decide⟩,?_⟩
  rw [abs_le];norm_num [coarsePoint];constructor <;> linarith [hx.1,hx.2]

theorem actual_net_radii_are_exact :
    IsLeast {r : ℝ | ∀ x∈domain,∃ i : Fin 20,|x-finePoint i|≤r} (1/20) ∧
    IsLeast {r : ℝ | ∀ x∈domain,∃ i : Fin 10,|x-coarsePoint i|≤r} (1/10) := by
  constructor
  · refine ⟨actual_fine_twenty_points_cover,?_⟩
    intro r hr
    obtain ⟨i,hi⟩:=hr (-9/10) (by norm_num [domain])
    fin_cases i <;> norm_num [finePoint]at hi ⊢ <;> linarith
  · refine ⟨actual_coarse_ten_points_cover,?_⟩
    intro r hr
    obtain ⟨i,hi⟩:=hr (-17/20) (by norm_num [domain])
    fin_cases i <;> norm_num [coarsePoint]at hi ⊢ <;> linarith

theorem actual_function_positive_and_minimum_values :
    (∀ x∈domain,97/400≤h x) ∧ h (-19/20)=97/400 ∧ h (19/20)=97/400 := by
  refine ⟨?_,by norm_num [h],by norm_num [h]⟩
  intro x hx
  dsimp [h]
  have ha: -19/20≤x:=hx.1
  have hb:x≤19/20:=hx.2
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

theorem actual_all_fine_samples_minimum_and_margin :
    (∀ i : Fin 20,97/400≤h (finePoint i)) ∧
    h (finePoint 0)=97/400 ∧ h (finePoint 19)=97/400 ∧
    (19/10:ℝ)*(1/20)=19/200 ∧ 19/200<97/400 := by
  refine ⟨fun i=>actual_function_positive_and_minimum_values.1 _ (actual_fine_nodes_inside i),?_,?_,?_,?_⟩ <;> norm_num [finePoint,h]

theorem actual_net_margin_certificate {X : Type*} [PseudoMetricSpace X]
    (f : X→ℝ) (D : Set X) (L : ℝ≥0) (τ m : ℝ)
    (hf : LipschitzOnWith L f D)
    (Z : Set X) (hZ : Z⊆D)
    (hnet : ∀ x∈D,∃ z∈Z,dist x z≤τ)
    (hsample : ∀ z∈Z,m≤f z) :
    ∀ x∈D,m-(L:ℝ)*τ≤f x := by
  intro x hx
  obtain ⟨z,hz,hd⟩:=hnet x hx
  have ha:=hf.dist_le_mul x hx z (hZ hz)
  rw [Real.dist_eq]at ha
  have hb: (L:ℝ)*dist x z≤(L:ℝ)*τ:=mul_le_mul_of_nonneg_left hd L.coe_nonneg
  have hc: f z-f x≤|f x-f z|:=by rw [abs_sub_comm];exact le_abs_self _
  linarith [hsample z hz]

theorem actual_fine_grid_certifies_strict_positivity_from_samples :
    ∀ x∈domain,1/400≤h x := by
  intro x hx
  obtain ⟨i,hi⟩:=actual_fine_twenty_points_cover x hx
  have hb:=actual_lipschitz_bound.dist_le_mul x hx (finePoint i) (actual_fine_nodes_inside i)
  rw [Real.dist_eq,Real.dist_eq]at hb
  have hs:=actual_all_fine_samples_minimum_and_margin.1 i
  have hc: h (finePoint i)-h x≤|h x-h (finePoint i)|:=by rw [abs_sub_comm];exact le_abs_self _
  nlinarith

theorem actual_coarse_margin_fails_although_function_is_positive :
    (19/10:ℝ)*(1/10)=19/100 ∧
    h (coarsePoint 0)=97/400 ∧ h (coarsePoint 0)<(19/10:ℝ)*(1/10) ∧
    ¬(∀ i : Fin 10,(19/10:ℝ)*(1/10)≤h (coarsePoint i)) ∧
    (∀ x∈domain,0<h x) := by
  refine ⟨by norm_num,by norm_num [h,coarsePoint],by norm_num [h,coarsePoint],?_,?_⟩
  · intro he;have hh:=he 0;norm_num [h,coarsePoint]at hh
  · intro x hx;have hh:=actual_function_positive_and_minimum_values.1 x hx;linarith

theorem actual_finer_radius_increases_the_same_measurement_margin
    (L : ℝ≥0) (m τfine τcoarse : ℝ) (hτ : τfine≤τcoarse) :
    m-(L:ℝ)*τcoarse≤m-(L:ℝ)*τfine := by
  have hh:=mul_le_mul_of_nonneg_left hτ L.coe_nonneg;linarith

theorem actual_cube_grid_cost_power_bounds (d N : ℕ) (hN : 0<N) :
    N^d≤(SafeLearning.CompleteFoundationsCubicGrids.unitGrid d N).card ∧
    (SafeLearning.CompleteFoundationsCubicGrids.unitGrid d N).card≤2^d*N^d ∧
    SafeLearning.CompleteFoundationsCubicGrids.gridRadius d N=(Real.sqrt d/2)*(1/(N:ℝ)) := by
  have hc:=SafeLearning.CompleteFoundationsCubicGrids.grid_cardinality d N hN
  have hr:=SafeLearning.CompleteFoundationsCubicGrids.grid_spacing_formula d N hN
  refine ⟨?_,?_,hr.2⟩
  · rw [hc];exact Nat.pow_le_pow_left (Nat.le_succ N)
  · rw [hc,←mul_pow]
    apply Nat.pow_le_pow_left
    omega

end SafeLearning.CompleteFoundationsQuadraticTwentyNet24
