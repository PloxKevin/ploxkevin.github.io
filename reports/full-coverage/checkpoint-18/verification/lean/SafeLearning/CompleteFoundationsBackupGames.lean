import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsBackupGames
open scoped BigOperators

def margins : Fin 3 → Fin 2 → ℝ := ![![3/5,1/10],![7/20,3/10],![4/5,-1/20]]
def safe (c : Fin 3) : Prop := ∀ j, 0 ≤ margins c j
def worstMargin (c : Fin 3) : ℝ := min (margins c 0) (margins c 1)
def bestSingleMargin (c : Fin 3) : ℝ := max (margins c 0) (margins c 1)

theorem actual_safety_is_worst_margin_nonnegative (c : Fin 3) :
    safe c ↔ 0 ≤ worstMargin c := by
  simp only [safe,worstMargin,le_min_iff]
  constructor
  · intro h;exact ⟨h 0,h 1⟩
  · rintro ⟨h0,h1⟩ j;fin_cases j <;> assumption

theorem actual_safe_controllers (c : Fin 3) : safe c ↔ c=0 ∨ c=1 := by
  rw [actual_safety_is_worst_margin_nonnegative]
  fin_cases c <;> norm_num [worstMargin,margins]

theorem actual_worst_margins :
    worstMargin 0=1/10 ∧ worstMargin 1=3/10 ∧ worstMargin 2= -1/20 := by
  norm_num [worstMargin,margins]

theorem actual_unique_max_min (c : Fin 3) :
    (∀ d,worstMargin d ≤ worstMargin c) ↔ c=1 := by
  fin_cases c
  · constructor
    · intro h;have := h 1;norm_num [worstMargin,margins] at this
    · norm_num
  · constructor
    · intro _;rfl
    · intro _ d;fin_cases d <;> norm_num [worstMargin,margins]
  · constructor
    · intro h;have := h 1;norm_num [worstMargin,margins] at this
    · norm_num

theorem actual_unique_largest_single_margin (c : Fin 3) :
    (∀ d,bestSingleMargin d ≤ bestSingleMargin c) ↔ c=2 := by
  fin_cases c
  · constructor
    · intro h;have := h 2;norm_num [bestSingleMargin,margins] at this
    · norm_num
  · constructor
    · intro h;have := h 2;norm_num [bestSingleMargin,margins] at this
    · norm_num
  · constructor
    · intro _;rfl
    · intro _ d;fin_cases d <;> norm_num [bestSingleMargin,margins]

theorem actual_single_margin_rule_selects_unsafe :
    ¬safe 2 ∧ (∀ c,bestSingleMargin c ≤ bestSingleMargin 2) ∧ safe 1 := by
  exact ⟨by rw [actual_safe_controllers];norm_num,
    (actual_unique_largest_single_margin 2).mpr rfl,
    (actual_safe_controllers 1).mpr (Or.inr rfl)⟩

def X : Set ℝ := Set.Icc 0 2
def Y : Set ℝ := Set.Icc (-3) 0
def game (x y : ℝ) : ℝ := (x-1)^2-(y+2)^2
def upperValue (x : ℝ) : ℝ := sSup (game x '' Y)
def lowerValue (y : ℝ) : ℝ := sInf ((fun x => game x y) '' X)
def minMax : ℝ := sInf (upperValue '' X)
def maxMin : ℝ := sSup (lowerValue '' Y)

theorem actual_source_domains : (1:ℝ)∈X ∧ (-2:ℝ)∈Y ∧ (0:ℝ)∈Y := by
  norm_num [X,Y]

theorem actual_saddle_inequalities (x y : ℝ) :
    game 1 y ≤ game 1 (-2) ∧ game 1 (-2) ≤ game x (-2) := by
  constructor <;> simp only [game] <;> nlinarith [sq_nonneg (x-1),sq_nonneg (y+2)]

theorem actual_unique_inner_y (x y : ℝ) :
    (∀ z∈Y,game x z ≤ game x y) ↔ y= -2 := by
  constructor
  · intro h;have := h (-2) actual_source_domains.2.1
    simp only [game] at this
    nlinarith [sq_nonneg (y+2)]
  · rintro rfl z _;simp only [game];nlinarith [sq_nonneg (z+2)]

theorem actual_unique_inner_x (x y : ℝ) :
    (∀ z∈X,game x y ≤ game z y) ↔ x=1 := by
  constructor
  · intro h;have := h 1 actual_source_domains.1
    simp only [game] at this
    nlinarith [sq_nonneg (x-1)]
  · rintro rfl z _;simp only [game];nlinarith [sq_nonneg (z-1)]

theorem actual_inner_supremum (x : ℝ) : upperValue x=(x-1)^2 := by
  have hb : BddAbove (game x '' Y) := ⟨(x-1)^2,by
    rintro _ ⟨y,_,rfl⟩;simp only [game];nlinarith [sq_nonneg (y+2)]⟩
  apply le_antisymm
  · exact csSup_le (Set.Nonempty.image _ ⟨-2,actual_source_domains.2.1⟩) (by
    rintro _ ⟨z,_,rfl⟩;simp only [game];nlinarith [sq_nonneg (z+2)])
  · convert le_csSup hb (Set.mem_image_of_mem (game x) actual_source_domains.2.1) using 1 <;>
      norm_num [upperValue,game]

theorem actual_inner_infimum (y : ℝ) : lowerValue y= -(y+2)^2 := by
  have hb : BddBelow ((fun x => game x y) '' X) := ⟨-(y+2)^2,by
    rintro _ ⟨x,_,rfl⟩;simp only [game];nlinarith [sq_nonneg (x-1)]⟩
  apply le_antisymm
  · convert csInf_le hb (Set.mem_image_of_mem (fun x => game x y) actual_source_domains.1) using 1 <;>
      norm_num [lowerValue,game]
  · exact le_csInf (Set.Nonempty.image _ ⟨1,actual_source_domains.1⟩) (by
    rintro _ ⟨z,_,rfl⟩;simp only [game];nlinarith [sq_nonneg (z-1)])

theorem actual_min_max_and_max_min : minMax=0 ∧ maxMin=0 := by
  constructor
  · have hb : BddBelow (upperValue '' X) := ⟨0,by
      rintro _ ⟨x,_,rfl⟩;rw [actual_inner_supremum];exact sq_nonneg _⟩
    apply le_antisymm
    · convert csInf_le hb (Set.mem_image_of_mem upperValue actual_source_domains.1) using 1 <;>
        norm_num [minMax,actual_inner_supremum]
    · exact le_csInf (Set.Nonempty.image _ ⟨1,actual_source_domains.1⟩) (by
      rintro _ ⟨z,_,rfl⟩;rw [actual_inner_supremum];exact sq_nonneg _)
  · have hb : BddAbove (lowerValue '' Y) := ⟨0,by
      rintro _ ⟨y,_,rfl⟩;rw [actual_inner_infimum];nlinarith [sq_nonneg (y+2)]⟩
    apply le_antisymm
    · exact csSup_le (Set.Nonempty.image _ ⟨-2,actual_source_domains.2.1⟩) (by
      rintro _ ⟨z,_,rfl⟩;rw [actual_inner_infimum];nlinarith [sq_nonneg (z+2)])
    · convert le_csSup hb (Set.mem_image_of_mem lowerValue actual_source_domains.2.1) using 1 <;>
        norm_num [maxMin,actual_inner_infimum]

theorem actual_unique_outer_choices (x y : ℝ) :
    ((x∈X ∧ ∀ z∈X,upperValue x ≤ upperValue z) ↔ x=1) ∧
    ((y∈Y ∧ ∀ z∈Y,lowerValue z ≤ lowerValue y) ↔ y= -2) := by
  constructor
  · constructor
    · rintro ⟨_,h⟩;have := h 1 actual_source_domains.1
      simp only [actual_inner_supremum] at this
      nlinarith [sq_nonneg (x-1)]
    · rintro rfl;refine ⟨actual_source_domains.1,?_⟩
      intro z _;simp only [actual_inner_supremum];nlinarith [sq_nonneg (z-1)]
  · constructor
    · rintro ⟨_,h⟩;have := h (-2) actual_source_domains.2.1
      simp only [actual_inner_infimum] at this
      nlinarith [sq_nonneg (y+2)]
    · rintro rfl;refine ⟨actual_source_domains.2.1,?_⟩
      intro z _;simp only [actual_inner_infimum];nlinarith [sq_nonneg (z+2)]

theorem actual_separate_minimization_is_different (x y : ℝ) (hy : y∈Y) :
    game 1 0= -4 ∧ -4 ≤ game x y ∧ game 1 0 < game 1 (-2) := by
  rcases hy with ⟨hy0,hy1⟩
  constructor
  · norm_num [game]
  · constructor
    · simp only [game];nlinarith [sq_nonneg (x-1),mul_nonneg (show 0≤-y by linarith)
        (show 0≤y+4 by linarith)]
    · norm_num [game]


theorem actual_square_jensen (u v c a b : ℝ) (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    (a*u+b*v-c)^2 ≤ a*(u-c)^2+b*(v-c)^2 := by
  have hid : a*(u-c)^2+b*(v-c)^2-(a*u+b*v-c)^2=a*b*(u-v)^2 := by
    have he : b=1-a := by linarith
    rw [he];ring
  have hp : 0≤a*b*(u-v)^2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  linarith

theorem actual_convex_and_concave_roles :
    (∀ y : ℝ,ConvexOn ℝ X (fun x=>game x y)) ∧
    (∀ x : ℝ,ConcaveOn ℝ Y (game x)) := by
  constructor
  · intro y;refine ⟨convex_Icc _ _,?_⟩
    intro u _ v _ a b ha hb hab
    have h:=actual_square_jensen u v 1 a b ha hb hab
    simp only [game,smul_eq_mul]
    nlinarith [congrArg (fun z : ℝ => z*(y+2)^2) hab]
  · intro x;refine ⟨convex_Icc _ _,?_⟩
    intro u _ v _ a b ha hb hab
    have h:=actual_square_jensen u v (-2) a b ha hb hab
    simp only [game,smul_eq_mul]
    nlinarith [congrArg (fun z : ℝ => z*(x-1)^2) hab]

end SafeLearning.CompleteFoundationsBackupGames
