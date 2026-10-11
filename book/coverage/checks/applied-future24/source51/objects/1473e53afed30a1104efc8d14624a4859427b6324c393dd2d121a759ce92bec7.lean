import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Kernel checked statements for Primers 0, A and B.  The companion JSON maps each
statement to source exercises and distinguishes complete from partial coverage.
No numerical floating point oracle, custom axiom, or omitted proof is used.
-/
namespace SafeLearning.PrimersFoundations

open Set
open scoped BigOperators

section LogicAndSets
variable {α β : Type*}

theorem deMorgan (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  classical
  ext x
  simp only [mem_compl_iff, mem_inter_iff, mem_union, not_and_or]
theorem preimage_intersection (f : α → β) (A B : Set β) :
    f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B := rfl
theorem preimage_union (f : α → β) (A B : Set β) :
    f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B := rfl
theorem preimage_complement (f : α → β) (A : Set β) :
    f ⁻¹' Aᶜ = (f ⁻¹' A)ᶜ := rfl
theorem injective_image_intersection (f : α → β) (hf : Function.Injective f)
    (A B : Set α) : f '' (A ∩ B) = f '' A ∩ f '' B := Set.image_inter hf
theorem image_union_preserved (f : α → β) (A B : Set α) :
    f '' (A ∪ B) = f '' A ∪ f '' B := Set.image_union f A B
theorem feedback_negation (C : Set α) (U : Set β) (P : α → β → Prop) :
    (¬ ∀ x ∈ C, ∃ u ∈ U, P x u) ↔ ∃ x ∈ C, ∀ u ∈ U, ¬ P x u := by
  simp only [not_forall, not_exists, not_and, not_imp, exists_prop]
theorem shared_input_implies_feedback (P : α → β → Prop) :
    (∃ u, ∀ x, P x u) → ∀ x, ∃ u, P x u := by rintro ⟨u, h⟩ x; exact ⟨u, h x⟩
theorem reachability_monotone (f : α → α) :
    Monotone (fun S : Set α => S ∪ f '' S) := by
  intro A B h x hx
  rcases hx with hx | ⟨a, ha, rfl⟩
  · exact Or.inl (h hx)
  · exact Or.inr ⟨a, h ha, rfl⟩
theorem invariant_iterates (f : α → α) (C : Set α)
    (hf : ∀ x ∈ C, f x ∈ C) (x : α) (hx : x ∈ C) (n : ℕ) :
    f^[n] x ∈ C := by
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa [Function.iterate_succ_apply'] using hf _ ih

theorem interval_feedback :
    (∀ x : ℝ, x ∈ Icc (-1) 1 → ∃ u ∈ Icc (-1) 1, 2*x+u ∈ Icc (-1) 1) ∧
    ¬ (∃ u : ℝ, u ∈ Icc (-1) 1 ∧ ∀ x ∈ Icc (-1) 1, 2*x+u ∈ Icc (-1) 1) := by
  constructor
  · intro x hx; refine ⟨-x, ?_, ?_⟩ <;> simp only [mem_Icc] at * <;> constructor <;> linarith [hx.1, hx.2]
  · rintro ⟨u, _, h⟩
    have h1 := h 1 (by norm_num)
    have h2 := h (-1) (by norm_num)
    simp only [mem_Icc] at h1 h2
    linarith [h1.2, h2.1]

theorem cancellation_range (a : ℝ) :
    (∀ x ∈ Icc (-1 : ℝ) 1, ∃ u ∈ Icc (-a) a, x+u=0) ↔ 1 ≤ a := by
  constructor
  · intro h; obtain ⟨u, hu, he⟩ := h 1 (by norm_num)
    have := hu.1; linarith
  · intro ha x hx; refine ⟨-x, ?_, by ring⟩
    constructor <;> linarith [hx.1, hx.2]
theorem no_shared_cancellation : ¬ ∃ u : ℝ, ∀ x ∈ Icc (-1 : ℝ) 1, x+u=0 := by
  rintro ⟨u, h⟩
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  linarith
theorem square_not_injective : ¬ Function.Injective (fun x : ℝ => x^2) := by
  intro h; have := h (a₁ := (-1)) (a₂ := 1) (by norm_num); norm_num at this
theorem square_not_surjective : ¬ Function.Surjective (fun x : ℝ => x^2) := by
  intro h; obtain ⟨x, hx⟩ := h (-1); nlinarith [sq_nonneg x]
theorem square_injective_nonnegative (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^2=y^2) : x=y := by nlinarith [sq_nonneg (x-y)]
theorem square_surjective_nonnegative (y : ℝ) (hy : 0 ≤ y) :
    ∃ x : ℝ, 0 ≤ x ∧ x^2=y := ⟨Real.sqrt y, Real.sqrt_nonneg y, Real.sq_sqrt hy⟩
theorem square_image_counterexample :
    (fun x : ℝ => x^2) '' (({(-2)} : Set ℝ) ∩ {2}) = ∅ ∧
    (fun x : ℝ => x^2) '' ({(-2)} : Set ℝ) ∩
      (fun x : ℝ => x^2) '' ({2} : Set ℝ) = {4} := by
  norm_num
end LogicAndSets

section ScalarFoundations
theorem square_nonnegative (x : ℝ) : 0 ≤ x^2 := sq_nonneg x
theorem completing_square (x : ℝ) :
    x^2+2*x+2 ≥ 1 ∧ (x^2+2*x+2=1 ↔ x = -1) := by
  constructor
  · nlinarith [sq_nonneg (x+1)]
  · constructor <;> intro h <;> nlinarith [sq_nonneg (x+1)]
theorem square_order_positive (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a^2 ≤ b^2 := by nlinarith
theorem square_implication (x : ℝ) : (3 < x → 9 < x^2) ∧ (x^2 ≤ 9 → x ≤ 3) := by constructor <;> intro h <;> nlinarith
theorem square_converse_counterexample :
    (-4 : ℝ)^2 > 9 ∧ ¬ (-4 : ℝ) > 3 ∧ (-3 : ℝ) ≤ -2 ∧ ¬ (-3 : ℝ)^2 ≤ (-2)^2 := by norm_num
theorem real_counterexamples :
    (1/2 : ℝ)^2 < 1/2 ∧ (0 : ℝ)*1=0 ∧ (1 : ℝ) ≠ 0 ∧
    (-1 : ℝ)^2=1^2 ∧ (-1 : ℝ) ≠ 1 := by norm_num
theorem even_square_iff (n : ℤ) : Even (n^2) ↔ Even n := by
  rw [show n^2=n*n by ring, Int.even_mul]
  tauto
theorem finite_sum_integers (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j+1 : ℕ) : ℝ)) = (n : ℝ)*((n : ℝ)+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
theorem affine_fixed_point (x : ℝ) : (x+3)/4=x ↔ x=1 := by constructor <;> intro h <;> linarith
theorem affine_iteration :
    ((-1 : ℝ)+3)/4=1/2 ∧ ((1/2 : ℝ)+3)/4=7/8 ∧
    ((7/8 : ℝ)+3)/4=31/32 := by norm_num
theorem affine_error (x : ℝ) : (x+3)/4-1=(x-1)/4 := by ring
theorem alternate_fixed_point (x : ℝ) : -x/2+3=x ↔ x=2 := by constructor <;> intro h <;> linarith
theorem alternate_error (x y : ℝ) : |(-x/2+3)-(-y/2+3)|=|x-y|/2 := by
  have h : (-x/2+3)-(-y/2+3)=-(x-y)/2 := by ring
  rw [h, abs_div, abs_neg]; norm_num
theorem geometric_thresholds :
    2*(1/2 : ℝ)^7 > 1/100 ∧ 2*(1/2 : ℝ)^8 ≤ 1/100 ∧
    4*(1/2 : ℝ)^8 > 1/100 ∧ 4*(1/2 : ℝ)^9 ≤ 1/100 := by norm_num
theorem interval_invariant_step (x : ℝ) (h : x ∈ Icc (0 : ℝ) 1) :
    x/2+1/4 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [h.1,h.2]
theorem contraction_fixed_unique (g : ℝ → ℝ)
    (hg : ∀ x y, |g x-g y| ≤ |x-y|/3) (a b : ℝ)
    (ha : g a=a) (hb : g b=b) : a=b := by
  have h := hg a b
  rw [ha,hb] at h
  have hab : |a-b|=0 := by linarith [abs_nonneg (a-b)]
  exact sub_eq_zero.mp (abs_eq_zero.mp hab)
theorem cauchy_schwarz_two (a b x y : ℝ) :
    (a*x+b*y)^2 ≤ (a^2+b^2)*(x^2+y^2) := by nlinarith [sq_nonneg (a*y-b*x)]
theorem young_scaled (a b η : ℝ) (hη : 0 < η) :
    2*a*b ≤ η*a^2+b^2/η := by
  have hd : b^2/η*η=b^2 := div_mul_cancel₀ _ (ne_of_gt hη)
  nlinarith [sq_nonneg (η*a-b)]
theorem am_gm (a b : ℝ) : 2*a*b ≤ a^2+b^2 := by nlinarith [sq_nonneg (a-b)]
theorem lipschitz_transfer (fx fg L d ell h : ℝ)
    (hlip : |fx-fg| ≤ L*d) (hlower : ell ≤ fg) (hmargin : h ≤ ell-L*d) : h ≤ fx := by
  have := neg_abs_le (fx-fg); linarith
theorem grid_margin_numbers :
    (35/100 : ℝ)-3*(1/10)=5/100 ∧
    (35/100 : ℝ)-3*(1/5)= -25/100 ∧
    (15/100 : ℝ)-2*(5/100)=5/100 := by norm_num
theorem geometric_finite (r : ℝ) (hr : r ≠ 1) (T : ℕ) :
    ∑ t ∈ Finset.range T, r^t = (1-r^T)/(1-r) := by
  rw [geom_sum_eq hr]
  have hr1 : r-1 ≠ 0 := sub_ne_zero.mpr hr
  have h1r : 1-r ≠ 0 := sub_ne_zero.mpr hr.symm
  field_simp
  <;> ring
theorem geometric_discounted_mean (r : ℝ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => (n : ℝ)*r^n) (r/(1-r)^2) := by
  simpa [Real.norm_eq_abs] using hasSum_coe_mul_geometric_of_norm_lt_one hr
theorem sequence_threshold (t : ℕ) : (3 : ℝ)/((t : ℝ)+1) < 1/10 ↔ 30 ≤ t := by
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (t : ℝ)+1)]
  constructor
  · intro h
    have hreal : (29 : ℝ) < t := by linarith
    have hnat : 29 < t := by exact_mod_cast hreal
    omega
  · intro h
    have hreal : (30 : ℝ) ≤ t := by exact_mod_cast h
    linarith
theorem excursion_budget (count : ℕ) (h : (count : ℝ)*(1/5)^2 ≤ 6) : count ≤ 150 := by
  have : (count : ℝ) ≤ 150 := by linarith
  exact_mod_cast this
theorem polynomial_growth (n : ℝ) (hn : 1 ≤ n) :
    2*n^2 ≤ 2*n^2+3*n+1 ∧ 2*n^2+3*n+1 ≤ 6*n^2 := by constructor <;> nlinarith
theorem compute_budgets :
    (4 : ℝ)/40 = 1/10 ∧ (8 : ℝ)/80=1/10 ∧
    (1600 : ℕ)*100=160000 ∧ (80 : ℕ)*1000=80000 ∧
    (20 : ℕ)^6=64000000 ∧ (20 : ℕ)^10=10240000000000 := by norm_num
theorem quadratic_interval_minimum (x : ℝ) :
    -1/4 ≤ x^2-x ∧ (x^2-x= -1/4 ↔ x=1/2) := by
  constructor
  · nlinarith [sq_nonneg (x-1/2)]
  · constructor <;> intro h <;> nlinarith [sq_nonneg (x-1/2)]
theorem minimum_norm_halfspace (x y : ℝ) (h : 1 ≤ x+y) :
    1/2 ≤ x^2+y^2 := by nlinarith [sq_nonneg (x-y)]
theorem finite_minmax_gap :
    min (max (0 : ℝ) 2) (max 1 0)=1 ∧ max (min (0 : ℝ) 1) (min 2 0)=0 := by norm_num
end ScalarFoundations

section MetricFacts
variable {α : Type*} [MetricSpace α]
theorem distance_to_set_lipschitz (C : Set α) (x y : α) :
    |Metric.infDist x C-Metric.infDist y C| ≤ dist x y := by
  have h1 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := C)
  have h2 := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := C)
  rw [dist_comm y x] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end MetricFacts


section MatrixAndQuadraticFacts
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

theorem norm_exercise_numbers :
    (2 : ℝ)*1+(-1)*2+2*0=0 ∧
    (2 : ℝ)^2+(-1)^2+2^2=3^2 ∧
    (3 : ℝ)^2+(-4)^2=5^2 ∧
    (3 : ℝ)*(3/25)-4*(-4/25)=1 ∧
    (3/25 : ℝ)^2+(-4/25)^2=(1/5)^2 := by norm_num

theorem box_support (x y : ℝ) (hx : |x| ≤ 1/5) (hy : |y| ≤ 1/5) :
    3*x-4*y ≤ 7/5 := by
  have hxx := (abs_le.mp hx).2
  have hyy := (abs_le.mp hy).1
  linarith

theorem ball_support (x y : ℝ) (h : x^2+y^2 ≤ (1/5)^2) :
    3*x-4*y ≤ 1 := by
  have hc := cauchy_schwarz_two 3 (-4) x y
  nlinarith

theorem matrix_norm_example_product :
    ( Matrix.of ![![1,-2],![0,3]] : Mat2).mulVec ![0,1] = ![-2,3] := by
  ext i; fin_cases i <;> norm_num [Matrix.of_apply,Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem diagonal_product :
    ( Matrix.of ![![3,0],![0,1/2]] : Mat2) * Matrix.of ![![1/2,0],![0,3]] = Matrix.of ![![3/2,0],![0,3/2]] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.of_apply,Matrix.mul_apply,Fin.sum_univ_two]

theorem geometric_matrix_inverse :
    ( Matrix.of ![![1/2,0],![0,3/4]] : Mat2) * Matrix.of ![![2,0],![0,4/3]] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.of_apply,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]

theorem eigenbasis_example :
    ( Matrix.of ![![3,1],![1,3]] : Mat2).mulVec ![1,1] = ![4,4] ∧
    ( Matrix.of ![![3,1],![1,3]] : Mat2).mulVec ![1,-1] = ![2,-2] ∧
    ( Matrix.of ![![3,1],![1,3]] : Mat2).mulVec ![1,2] = ![5,7] := by
  constructor
  · ext i; fin_cases i <;> norm_num [Matrix.of_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  constructor <;> ext i <;> fin_cases i <;> norm_num [Matrix.of_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem rayleigh_example (x y : ℝ) :
    2*(x^2+y^2) ≤ 3*x^2+2*x*y+3*y^2 ∧
    3*x^2+2*x*y+3*y^2 ≤ 4*(x^2+y^2) := by
  constructor <;> nlinarith [sq_nonneg (x+y),sq_nonneg (x-y)]

theorem nonsymmetric_example (x y : ℝ) :
    x*(x+4*y)+y*y = x^2+4*x*y+y^2 ∧
    ((1 : ℝ)^2+4*1*(-1)+(-1)^2)= -2 := by constructor <;> ring

theorem psd_indefinite_examples (x y : ℝ) :
    0 ≤ 2*x^2 ∧ (2 : ℝ)*1^2+6*1*1+2*1^2=10 ∧
    (2 : ℝ)*1^2+6*1*(-1)+2*(-1)^2= -2 := by
  constructor
  · positivity
  norm_num

theorem cholesky_example :
    ( Matrix.of ![![2,0],![1,1]] : Mat2) * ( Matrix.of ![![2,0],![1,1]] : Mat2).transpose = Matrix.of ![![4,2],![2,2]] ∧
    ( Matrix.of ![![4,2],![2,2]] : Mat2).mulVec ![1,1] = ![6,4] := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
  · ext i; fin_cases i <;> norm_num [Matrix.of_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem ellipsoid_support_bound (x y : ℝ) (h : 4*x^2+y^2 ≤ 1) :
    (x+2*y)^2 ≤ 17/4 := by
  have hc := cauchy_schwarz_two (1/2) 2 (2*x) y
  nlinarith

theorem minimum_norm_solution (x y : ℝ) (h : x+2*y=5) :
    5 ≤ x^2+y^2 ∧ (x^2+y^2=5 ↔ x=1 ∧ y=2) := by
  constructor
  · nlinarith [sq_nonneg (2*x-y)]
  · constructor
    · intro he
      have hn : (2*x-y)^2=0 := by nlinarith
      have hz : 2*x-y=0 := sq_eq_zero_iff.mp hn
      constructor <;> linarith
    · rintro ⟨rfl,rfl⟩; norm_num

theorem svd_example :
    ( Matrix.of ![![1,0],![0,-1]] : Mat2) * Matrix.of ![![2,0],![0,1]] = Matrix.of ![![2,0],![0,-1]] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.of_apply,Matrix.mul_apply,Fin.sum_univ_two]

theorem power_estimate_squares :
    (5 : ℝ)<3^2 ∧ (730/82 : ℝ)<3^2 ∧ (730/82 : ℝ)>5 ∧
    (3 : ℝ)^2/5>1 ∧ (3 : ℝ)^2/10≤1 := by norm_num

theorem block_three_product :
    ( Matrix.of ![![2,1,0],![1,3,0],![0,0,4]] : Mat3).mulVec ![1,2,3] = ![4,7,12] := by
  ext i; fin_cases i <;> norm_num [Matrix.of_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem schur_completed_square (a x y : ℝ) :
    a*x^2+4*x*y+3*y^2=(a-4/3)*x^2+3*(y+2*x/3)^2 := by ring

theorem schur_psd_iff (a : ℝ) :
    (∀ x y : ℝ, 0 ≤ a*x^2+4*x*y+3*y^2) ↔ 4/3 ≤ a := by
  constructor
  · intro h; have := h 3 (-2); nlinarith
  · intro h x y
    rw [schur_completed_square]
    positivity

theorem rank_one_inverse_example :
    ( Matrix.of ![![3,2],![2,5]] : Mat2) * Matrix.of ![![5/11,-2/11],![-2/11,3/11]] = 1 ∧
    (3 : ℝ)*5-2*2=11 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.of_apply,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
  · norm_num

theorem reflection_and_projection (x y : ℝ) :
    x^2+(-y)^2=x^2+y^2 ∧ (x^2 ≤ x^2+y^2) := by
  constructor
  · ring
  · nlinarith [sq_nonneg y]

theorem cayley_example :
    ( Matrix.of ![![1,1],![-1,1]] : Mat2) * Matrix.of ![![1/2,1/2],![-1/2,1/2]] = Matrix.of ![![0,1],![-1,0]] ∧
    ( Matrix.of ![![0,1],![-1,0]] : Mat2).transpose * Matrix.of ![![0,1],![-1,0]] = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two,Matrix.one_apply]

theorem cayley_no_neg_one (w Aw : ℝ) (h : w-Aw= -(w+Aw)) : w=0 := by linarith

theorem function_projection_arithmetic :
    (1/3 : ℝ)-1/2+1/4=1/12 ∧ (1/2 : ℝ)^2+1/12=1/3 := by norm_num

theorem feature_gram_positive (a b : ℝ) :
    a^2+2*a*b+2*b^2=(a+b)^2+b^2 ∧
    0 ≤ a^2+2*a*b+2*b^2 ∧
    (a^2+2*a*b+2*b^2=0 ↔ a=0 ∧ b=0) := by
  constructor
  · ring
  constructor
  · nlinarith [sq_nonneg (a+b),sq_nonneg b]
  constructor
  · intro h
    have hb : b=0 := by nlinarith [sq_nonneg (a+b),sq_nonneg b]
    subst b; constructor <;> nlinarith [sq_nonneg a]
  · rintro ⟨rfl,rfl⟩; norm_num

theorem rkhs_interpolation :
    ( Matrix.of ![![1,1],![1,2]] : Mat2) * Matrix.of ![![2,-1],![-1,1]] = 1 ∧
    (1 : ℝ)^2+2^2=5 ∧ (1 : ℝ)*(-1)+3*2=5 ∧
    ∀ x : ℝ, -(1+0*x)+2*(1+1*x)=1+2*x := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.of_apply,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
  norm_num
  intro x; ring

theorem legacy_matrix_gram :
    ( Matrix.of ![![1,-2],![3,4]] : Mat2).transpose * Matrix.of ![![1,-2],![3,4]] = Matrix.of ![![10,10],![10,20]] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]

theorem legacy_cholesky_family (a x y z : ℝ) :
    x^2+4*x*y+5*y^2+4*y*z+a*z^2=(x+2*y)^2+(y+2*z)^2+(a-4)*z^2 := by ring

theorem legacy_cholesky_psd_iff (a : ℝ) :
    (∀ x y z : ℝ, 0 ≤ x^2+4*x*y+5*y^2+4*y*z+a*z^2) ↔ 4 ≤ a := by
  constructor
  · intro h; have := h 4 (-2) 1; nlinarith
  · intro h x y z; rw [legacy_cholesky_family]; positivity

theorem legacy_cholesky_solve :
    ( Matrix.of ![![1,2,0],![2,5,2],![0,2,5]] : Mat3).mulVec ![1,0,1] = ![1,4,5] := by
  ext i; fin_cases i <;> norm_num [Matrix.of_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem legacy_ellipsoid_inverse :
    ( Matrix.of ![![5,-4],![-4,5]] : Mat2) * Matrix.of ![![5/9,4/9],![4/9,5/9]] = 1 ∧
    ( Matrix.of ![![2/3,1/3],![1/3,2/3]] : Mat2) * Matrix.of ![![2/3,1/3],![1/3,2/3]] = Matrix.of ![![5/9,4/9],![4/9,5/9]] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.of_apply,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]

theorem legacy_pseudoinverse_residual :
    ( Matrix.of ![![1,2],![2,4]] : Mat2).mulVec ![1/25,2/25] = ![1/5,2/5] ∧
    (4/5 : ℝ)*1+(-2/5)*2=0 := by
  constructor
  · ext i; fin_cases i <;> norm_num [Matrix.of_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · norm_num

theorem generalized_schur_rank_one (a s t x y : ℝ) :
    a*t^2+2*t*(s*x+2*s*y)+(x+2*y)^2 =
      (x+2*y+s*t)^2+(a-s^2)*t^2 := by ring

theorem legacy_logdet_arithmetic :
    (3 : ℝ)*3-1*1=8 ∧ (1 : ℝ)-(1/4)/(3/2)=5/6 ∧
    (3 : ℝ)*(1+(5/6)/(1/2))=8 := by norm_num

theorem generalized_eigen_inequality (x y : ℝ) :
    (x+y)^2 ≤ (3/2)*(x^2+2*y^2) := by nlinarith [sq_nonneg (x-2*y)]

theorem generalized_eigen_boundary (F : ℝ) :
    (1-F)*(2-F)-F^2=2-3*F ∧
    (2-3*F ≥ 0 ↔ F ≤ 2/3) := by constructor; ring; constructor <;> intro h <;> linarith
end MatrixAndQuadraticFacts


section OptimizationFacts

theorem quadratic_partial_x (x y : ℝ) :
    HasDerivAt (fun z : ℝ => z^2+z*y+2*y^2) (2*x+y) x := by
  convert (((hasDerivAt_id x).pow 2).add ((hasDerivAt_id x).mul_const y)).add_const (2*y^2) using 1 <;> (try funext z) <;> simp [Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq] <;> ring

theorem quadratic_partial_y (x y : ℝ) :
    HasDerivAt (fun z : ℝ => x^2+x*z+2*z^2) (x+4*y) y := by
  convert (HasDerivAt.add (hasDerivAt_const y (x^2))
    (((hasDerivAt_id y).const_mul x).add (((hasDerivAt_id y).pow 2).const_mul 2))) using 1 <;> (try funext z) <;> simp [Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq] <;> ring

theorem polynomial_curve_derivative (t : ℝ) :
    HasDerivAt (fun z : ℝ => 1-z^2-z^4) (-2*t-4*t^3) t := by
  convert ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).sub
    ((hasDerivAt_id t).pow 4) using 1 <;> (try funext z) <;> simp [Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq] <;> ring

theorem chain_rule_curve (t : ℝ) :
    (-2*t)*1+(-2*t^2)*(2*t)= -2*t-4*t^3 := by ring

theorem taylor_model_value :
    (1 : ℝ)+1/10+(1/10)^2/2+(1/5)^2=229/200 := by norm_num

theorem least_squares_minimum (x y : ℝ) :
    0 ≤ (x-1)^2+(2*y-1)^2 ∧
    ((x-1)^2+(2*y-1)^2=0 ↔ x=1 ∧ y=1/2) := by
  constructor
  · positivity
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (x-1),sq_nonneg (2*y-1)]
  · rintro ⟨rfl,rfl⟩; norm_num

theorem determinant_curve_derivative :
    HasDerivAt (fun t : ℝ => Real.log (6+3*t-t^2)) (1/2) 0 := by
  have h := ((((hasDerivAt_id (0 : ℝ)).const_mul 3).const_add 6).sub
    ((hasDerivAt_id (0 : ℝ)).pow 2)).log (by norm_num : (6+3*(0 : ℝ)-0^2) ≠ 0)
  convert h using 1 <;> (try funext z) <;> norm_num [Pi.div_apply,id_eq]

theorem sensitivity_remainder (t : ℝ) (ht : 1+t ≠ 0) :
    2/(1+t)-(2-2*t)=2*t^2/(1+t) := by field_simp; ring

theorem sensitivity_derivative :
    HasDerivAt (fun t : ℝ => 2/(1+t)) (-2) 0 := by
  convert (hasDerivAt_const (0 : ℝ) (2 : ℝ)).div
    ((hasDerivAt_id (0 : ℝ)).const_add 1) (by norm_num : 1+(0 : ℝ) ≠ 0) using 1 <;> (try funext z) <;> norm_num [Pi.div_apply,id_eq]

theorem square_chord_bound (x y : ℝ) (hx : |x| ≤ 2) (hy : |y| ≤ 2) :
    |x^2-y^2| ≤ 4*|x-y| := by
  have hs : |x+y| ≤ 4 := (abs_add_le x y).trans (by linarith)
  calc
    |x^2-y^2|=|(x-y)*(x+y)| := by congr 1; ring
    _ = |x-y| *|x+y| := abs_mul _ _
    _ ≤ |x-y| *4 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = 4*|x-y| := by ring

theorem square_derivative_lipschitz (x y : ℝ) : |2*x-2*y|=2*|x-y| := by
  rw [show 2*x-2*y=2*(x-y) by ring,abs_mul]; norm_num

theorem state_error_recurrence (d : ℕ → ℝ)
    (h0 : d 0=0) (hs : ∀ n, d (n+1) ≤ (6/5)*d n+1/100) (n : ℕ) :
    d n ≤ (1/20)*((6/5 : ℝ)^n-1) := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hn := hs n
    rw [pow_succ]
    nlinarith

theorem state_error_numbers :
    (1/20 : ℝ)*((6/5)^5-1)=4651/62500 ∧
    (1/20 : ℝ)*((6/5)^6-1)=155155/1562500 ∧
    (1/5 : ℝ)-2*(4651/62500)=7995/156250 ∧
    (1/5 : ℝ)-2*(155155/1562500)=219/156250 := by norm_num

theorem interval_convex_combination (a b t : ℝ)
    (ha : a ∈ Icc (-1 : ℝ) 2) (hb : b ∈ Icc (-1 : ℝ) 2)
    (ht : t ∈ Icc (0 : ℝ) 1) : t*a+(1-t)*b ∈ Icc (-1 : ℝ) 2 := by
  have h0 : 0 ≤ 1-t := by linarith [ht.2]
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ha.1),
    mul_nonneg h0 (sub_nonneg.mpr hb.1),mul_nonneg ht.1 (sub_nonneg.mpr ha.2),
    mul_nonneg h0 (sub_nonneg.mpr hb.2)]

theorem absolute_value_subgradients (s : ℝ) :
    (∀ y : ℝ, s*y ≤ |y|) ↔ -1 ≤ s ∧ s ≤ 1 := by
  constructor
  · intro h; have h1:=h 1; have hm:=h (-1); norm_num at h1 hm; exact ⟨by linarith, h1⟩
  · rintro ⟨hl,hu⟩ y
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]; nlinarith
    · have hn : y ≤ 0 := le_of_not_ge hy
      rw [abs_of_nonpos hn]; nlinarith

theorem restricted_conjugate_nonnegative (y x : ℝ) (hy : 0 ≤ y) :
    y*x-x^2/2 ≤ y^2/2 ∧ y*y-y^2/2=y^2/2 := by
  constructor
  · nlinarith [sq_nonneg (x-y)]
  · ring

theorem restricted_conjugate_negative (y x : ℝ) (hy : y < 0) (hx : 0 ≤ x) :
    y*x-x^2/2 ≤ 0 ∧ y*0-(0 : ℝ)^2/2=0 := by
  constructor
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_lt hy) hx, sq_nonneg x]
  · ring

theorem gradient_step_threshold (η : ℝ) : |1-4*η|<1 ↔ 0<η ∧ η<1/2 := by
  rw [abs_lt]; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem gradient_step_examples :
    (1-4*(2/5 : ℝ))*2= -6/5 ∧ (1-4*(2/5 : ℝ))*(-6/5)=18/25 ∧
    1-4*(1/4 : ℝ)=0 ∧ 1-4*(1/2 : ℝ)= -1 ∧ 1-4*(3/5 : ℝ)= -7/5 := by norm_num

theorem newton_quadratic_minimum (x y : ℝ) :
    -5 ≤ x^2+4*y^2-2*x-8*y ∧
    (x^2+4*y^2-2*x-8*y= -5 ↔ x=1 ∧ y=1) := by
  constructor
  · nlinarith [sq_nonneg (x-1),sq_nonneg (y-1)]
  constructor
  · intro h; constructor <;> nlinarith [sq_nonneg (x-1),sq_nonneg (y-1)]
  · rintro ⟨rfl,rfl⟩; norm_num

theorem newton_backtracking_domain :
    (4 : ℝ)+1*(-12)<0 ∧ (4 : ℝ)+(1/2)*(-12)<0 ∧
    (4 : ℝ)+(1/4)*(-12)=1 ∧ (3/4 : ℝ)*(-12)= -9 := by norm_num

theorem newton_backtracking_armijo :
    (1 : ℝ)-Real.log 1 ≤ 4-Real.log 4-9/16 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  have hlog : Real.log (4 : ℝ)=2*Real.log 2 := by
    rw [show (4 : ℝ)=2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [Real.log_one,hlog]
  linarith

theorem kkt_scalar_optimum (x : ℝ) (hx : x ≤ 1) : 4 ≤ (x-3)^2 := by nlinarith [sq_nonneg (x-1)]

theorem kkt_halfspace_optimum (x y : ℝ) (h : x+y ≤ 1) :
    9/4 ≤ ((x-2)^2+(y-2)^2)/2 := by nlinarith [sq_nonneg (x-y)]

theorem penalty_right_branch (x : ℝ) :
    (x-2)^2+3*(x-1)^2=4*(x-5/4)^2+3/4 := by ring

theorem penalty_minimum (x : ℝ) :
    3/4 ≤ (x-2)^2+3*(max (x-1) 0)^2 := by
  by_cases h : x ≤ 1
  · rw [max_eq_right (by linarith : x-1 ≤ 0)]
    nlinarith [sq_nonneg (x-1)]
  · rw [max_eq_left (by linarith : 0 ≤ x-1),penalty_right_branch]
    nlinarith [sq_nonneg (x-5/4)]

theorem approximate_kkt_numbers :
    (2 : ℝ)*(9/10-2)+11/5=0 ∧ (11/5 : ℝ)*(1-9/10)=11/50 := by norm_num

theorem qp_expansion (x y : ℝ) :
    (x-1)^2+2*(y+1)^2=x^2+2*y^2-2*x+4*y+3 := by ring

theorem lp_optimum (x y : ℝ) (hx : x ≤ 2) (hxy : x+y ≤ 3) :
    2*x+y ≤ 5 ∧ (2*x+y=5 ↔ x=2 ∧ y=1) := by
  constructor
  · linarith
  constructor
  · intro he; constructor <;> linarith
  · rintro ⟨rfl,rfl⟩; norm_num

theorem filter_with_box_optimum (x y : ℝ)
    (hsafe : 4 ≤ x+2*y) (hbox : y ≤ 3/2) :
    13/8 ≤ (x^2+y^2)/2 := by
  nlinarith [sq_nonneg (x-1),sq_nonneg (y-3/2)]

theorem actuator_infeasible (x y : ℝ) (hx : x ≤ 3/2) (hy : y ≤ 3/2) : x+2*y<5 := by linarith

theorem saddle_quadratic (x y : ℝ) :
    -(y+2)^2 ≤ 0 ∧ 0 ≤ (x-1)^2 := by constructor; nlinarith [sq_nonneg (y+2)]; positivity

theorem legacy_taylor_numbers :
    (1 : ℝ)+2*(1/10)=6/5 ∧ (1/2 : ℝ)*(4*(1/10)^2+(1/10)^2)=1/40 ∧
    (6/5 : ℝ)+1/40=49/40 := by norm_num

theorem legacy_regularizer_step :
    (Matrix.of ![![1,1],![1,0]] : Mat2) * Matrix.of ![![1,1],![0,1]] = Matrix.of ![![1,2],![1,1]] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.of_apply,Matrix.mul_apply,Fin.sum_univ_two]

theorem legacy_regularizer_decrease :
    ((9/10 : ℝ)^2+(4/5)^2-1)^2/4+
    2*((9/10 : ℝ)*(-1/10)+(4/5)*(9/10))^2/4+
    ((-1/10 : ℝ)^2+(9/10)^2-1)^2/4 = 10287/40000 ∧
    (10287/40000 : ℝ)<3/4 := by norm_num

theorem translated_conjugate (w e : ℝ) :
    w*e-(w-1)^2/2=e+e^2/2-(w-(1+e))^2/2 := by ring

theorem translated_conjugate_negative (w e : ℝ) (hw : 0 ≤ w) (he : e < -1) :
    w*e-(w-1)^2/2 ≤ -1/2 := by
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hw (by linarith : e+1 ≤ 0),sq_nonneg w]

theorem fenchel_young_numbers :
    (1/2 : ℝ)+(1/2+(1/2)^2/2)=9/8 ∧ (9/8 : ℝ)≥2*(1/2) ∧
    (1/2 : ℝ)+(1+1^2/2)=2*1 := by norm_num

theorem legacy_gradient_thresholds :
    (50 : ℝ)*(81/100)^84>1/1000000 ∧ (50 : ℝ)*(81/100)^85≤1/1000000 ∧
    (55 : ℝ)*(81/121)^44>1/1000000 ∧ (55 : ℝ)*(81/121)^45≤1/1000000 := by norm_num

theorem legacy_filter_optimum (x y : ℝ) (hsafe : 21/5 ≤ x+2*y) (hbox : x ≤ 3/2) :
    149/800 ≤ ((x-2)^2+(y-1)^2)/2 := by
  nlinarith [sq_nonneg (x-3/2),sq_nonneg (y-27/20)]

theorem newton_singular_model_counterexample :
    (∀ x y : ℝ, 0 ≤ x^2) ∧ ((0 : ℝ)^2=0) ∧
    (0 : ℝ)≠1 := by constructor; intro x y; positivity; constructor <;> norm_num
end OptimizationFacts


section GeneralTheorems
open Filter

theorem banach_unique_exists {α : Type*} [MetricSpace α] [Nonempty α]
    [CompleteSpace α] {K : NNReal} {f : α → α} (hf : ContractingWith K f) :
    ∃! x : α, f x=x := by
  refine ⟨ContractingWith.fixedPoint f hf,hf.fixedPoint_isFixedPt,?_⟩
  intro y hy
  exact hf.fixedPoint_unique hy

theorem banach_iterates_converge {α : Type*} [MetricSpace α] [Nonempty α]
    [CompleteSpace α] {K : NNReal} {f : α → α} (hf : ContractingWith K f) (x : α) :
    Tendsto (fun n => f^[n] x) atTop (nhds (ContractingWith.fixedPoint f hf)) := hf.tendsto_iterate_fixedPoint x

theorem banach_apriori_bound {α : Type*} [MetricSpace α] [Nonempty α]
    [CompleteSpace α] {K : NNReal} {f : α → α} (hf : ContractingWith K f) (x : α) (n : ℕ) :
    dist (f^[n] x) (ContractingWith.fixedPoint f hf) ≤ dist x (f x)*(K : ℝ)^n/(1-K) :=
  hf.apriori_dist_iterate_fixedPoint_le x n

theorem gram_matrix_psd {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : (A.transpose*A).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self A

theorem psd_congruence {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (B : Matrix n m ℝ) :
    (B.transpose*A*B).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.conjTranspose_mul_mul_same B

theorem psd_diagonal_iff {n : Type*} [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal d).PosSemidef ↔ ∀ i, 0 ≤ d i := Matrix.posSemidef_diagonal_iff

theorem trace_cyclic {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) :
    Matrix.trace (A*B)=Matrix.trace (B*A) := Matrix.trace_mul_comm A B

theorem weierstrass_minimum {α : Type*} [TopologicalSpace α] {C : Set α}
    (hC : IsCompact C) (hne : C.Nonempty) (f : α → ℝ) (hf : ContinuousOn f C) :
    ∃ x ∈ C, ∀ y ∈ C, f x ≤ f y := hC.exists_isMinOn hne hf

theorem interval_topology :
    interior (Ioc (-1 : ℝ) 1)=Ioo (-1 : ℝ) 1 ∧
    closure (Ioc (-1 : ℝ) 1)=Icc (-1 : ℝ) 1 ∧
    frontier (Ioc (-1 : ℝ) 1)={-1,1} := by
  exact ⟨interior_Ioc,closure_Ioc (by norm_num),frontier_Ioc (by norm_num)⟩

theorem continuous_nonnegative_set_closed {α : Type*} [TopologicalSpace α]
    (f : α → ℝ) (hf : Continuous f) : IsClosed {x | 0 ≤ f x} :=
  isClosed_le continuous_const hf

theorem continuous_positive_set_open {α : Type*} [TopologicalSpace α]
    (f : α → ℝ) (hf : Continuous f) : IsOpen {x | 0 < f x} :=
  isOpen_lt continuous_const hf

theorem finite_safe_feedback :
    (∀ x : Fin 3, ∃ u : Bool, (x=2 ∨ (x=0 ∧ u=true) ∨ (x=1 ∧ u=false))) ∧
    ¬ (∃ u : Bool, ∀ x : Fin 3, (x=2 ∨ (x=0 ∧ u=true) ∨ (x=1 ∧ u=false))) := by decide

theorem finite_set_operations :
    ({0,2,4} ∪ {2,3,4} : Finset ℤ)={0,2,3,4} ∧
    ({0,2,4} ∩ {2,3,4} : Finset ℤ)={2,4} ∧
    ({0,2,4} \ {2,3,4} : Finset ℤ)={0} ∧
    ({0,1,2,3,4,5} \ {0,2,4} : Finset ℤ)={1,3,5} := by decide

theorem finite_set_builder :
    ({-2,-1,0,1,2,3} : Finset ℤ).filter (fun x => x^2≤4)={-2,-1,0,1,2} ∧
    ({-2,-1,0,1,2,3} : Finset ℤ).filter (fun x => x>0)={1,2,3} := by decide

theorem quantifier_example_truths :
    (∀ x : ℝ, 0≤x^2) ∧ (¬ ∃ x : ℝ, x^2<0) ∧
    (∀ x : ℝ, ∃ y : ℝ, y=x+2) ∧ (¬ ∃ y : ℝ, ∀ x : ℝ, y=x+2) := by
  refine ⟨sq_nonneg, ?_, fun x => ⟨x+2,rfl⟩, ?_⟩
  · rintro ⟨x,hx⟩; nlinarith [sq_nonneg x]
  · rintro ⟨y,hy⟩; have := hy y; linarith

theorem negated_quantifier_examples :
    (¬ ∀ x : ℝ, 1 ≤ x^2) ∧
    (¬ ∃ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, y < x) := by
  constructor
  · intro h; have := h 0; norm_num at this
  · rintro ⟨x,hx,h⟩; exact (lt_irrefl x) (h x hx)
end GeneralTheorems


section ConvexFirstOrder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convex_first_order {C : Set E} {f : E → ℝ} {x y : E}
    {f' : E →L[ℝ] ℝ} (hconv : ConvexOn ℝ C f)
    (hx : x ∈ C) (hy : y ∈ C) (hder : HasFDerivAt f f' x) :
    f x+f' (y-x) ≤ f y := by
  have hd : HasFDerivAt f f' (AffineMap.lineMap x y (0 : ℝ)) := by simpa using hder
  have hgder := hd.comp_hasDerivAt (0 : ℝ) (AffineMap.hasDerivAt_lineMap (a := x) (b := y))
  have hgconv := hconv.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
  have hs := hgconv.le_slope_of_hasDerivAt (x := (0 : ℝ)) (y := 1)
    (by simpa using hx) (by simpa using hy) (by norm_num) hgder
  have hsub : f' (y-x) ≤ f y-f x := by
    simpa [Function.comp_def,slope_def_field] using hs
  linarith

theorem convex_stationary_global_minimum {C : Set E} {f : E → ℝ} {x : E}
    (hconv : ConvexOn ℝ C f) (hx : x ∈ C) (hder : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) :
    ∀ y ∈ C, f x ≤ f y := by
  intro y hy
  simpa using convex_first_order hconv hx hy hder

theorem kkt_convex_sufficiency {m n : ℕ} {C : Set E} {x : E}
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (h : Fin n → E → ℝ)
    (f₀' : E →L[ℝ] ℝ) (f' : Fin m → E →L[ℝ] ℝ) (h' : Fin n → E →L[ℝ] ℝ)
    (lam : Fin m → ℝ) (ν : Fin n → ℝ)
    (hx : x ∈ C) (hconv₀ : ConvexOn ℝ C f₀) (hconv : ∀ i, ConvexOn ℝ C (f i))
    (hder₀ : HasFDerivAt f₀ f₀' x) (hder : ∀ i, HasFDerivAt (f i) (f' i) x)
    (haffine : ∀ j y, y ∈ C → h j y-h j x=h' j (y-x))
    (hfeasible : ∀ i, f i x ≤ 0) (heq : ∀ j, h j x=0)
    (hdual : ∀ i, 0 ≤ lam i) (hcomp : ∀ i, lam i*f i x=0)
    (hstation : ∀ d : E, f₀' d+(∑ i, lam i*f' i d)+(∑ j, ν j*h' j d)=0) :
    ∀ y ∈ C, (∀ i, f i y ≤ 0) → (∀ j, h j y=0) → f₀ x ≤ f₀ y := by
  intro y hy hyfeas hyeq
  have hlin₀ := convex_first_order hconv₀ hx hy hder₀
  have hineq : ∀ i, lam i*f' i (y-x) ≤ 0 := by
    intro i
    have hlin := convex_first_order (hconv i) hx hy (hder i)
    have hw := mul_le_mul_of_nonneg_left hlin (hdual i)
    have hc := hcomp i
    have hyw := mul_nonpos_of_nonneg_of_nonpos (hdual i) (hyfeas i)
    nlinarith
  have hsineq : (∑ i, lam i*f' i (y-x)) ≤ 0 := Finset.sum_nonpos (fun i _ => hineq i)
  have heqlin : ∀ j, h' j (y-x)=0 := by
    intro j
    have ha := haffine j y hy
    rw [heq j,hyeq j] at ha
    linarith
  have hseq : (∑ j, ν j*h' j (y-x))=0 := by simp [heqlin]
  have hs := hstation (y-x)
  rw [hseq] at hs
  linarith
end ConvexFirstOrder


section FiniteReachability
theorem certificate_reachability_monotone {α : Type*} (P : α → α → Prop) :
    Monotone (fun S : Set α => S ∪ {x | ∃ y ∈ S, P x y}) := by
  intro A B h x hx
  rcases hx with hx | ⟨y,hy,hP⟩
  · exact Or.inl (h hx)
  · exact Or.inr ⟨y,h hy,hP⟩

def reachFiveF : Fin 5 → Fin 5 := ![1,2,2,4,3]
def reachFive (S : Finset (Fin 5)) : Finset (Fin 5) := S ∪ S.image reachFiveF
theorem reachFive_iterates : reachFive {0}={0,1} ∧ reachFive {0,1}={0,1,2} ∧
    reachFive {0,1,2}={0,1,2} := by decide

def reachNineValue : Fin 9 → ℚ := ![18/10,23/10,14/10,24/10,14/10,24/10,14/10,4/10,14/10]
def reachNine (ε : ℚ) (S : Finset (Fin 9)) : Finset (Fin 9) :=
    S ∪ Finset.univ.filter (fun x => ∃ y ∈ S, reachNineValue y-ε-|((x.val : ℚ)-(y.val : ℚ))| ≥ 0)
theorem reachNine_error_iterates :
    reachNine (1/2) {0}={0,1} ∧ reachNine (1/2) {0,1}={0,1,2} ∧
    reachNine (1/2) {0,1,2}={0,1,2} := by
  constructor
  · ext x; fin_cases x <;> norm_num [reachNine,reachNineValue]
  constructor <;> ext x <;> fin_cases x <;> norm_num [reachNine,reachNineValue]

theorem reachNine_exact_closure :
    reachNine 0 {0,1,2,3,4,5,6,7}={0,1,2,3,4,5,6,7} := by
  ext x; fin_cases x <;> norm_num [reachNine,reachNineValue]
end FiniteReachability

end SafeLearning.PrimersFoundations
