import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsLogic

theorem negations_instantiated :
    ((¬ ∀ x : ℝ, 1 ≤ x^2) ↔ ∃ x : ℝ, x^2 < 1) ∧
    ((¬ ∃ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, y < x) ↔
      ∀ x ∈ Icc (0 : ℝ) 1, ∃ y ∈ Icc (0 : ℝ) 1, x ≤ y) := by
  constructor <;> simp only [not_forall, not_le, not_exists, not_and, not_imp, not_lt, exists_prop]

theorem finite_set_membership_inclusion :
    (2 : ℤ) ∈ ({-2,-1,0,1,2} : Finset ℤ) ∧
    ¬ ({1,2,3} : Finset ℤ) ⊆ {-2,-1,0,1,2} := by decide

theorem shrinking_interval_union :
    (⋃ n : ℕ, Icc (-(1/((n : ℝ)+1))) (1/((n : ℝ)+1)))=Icc (-1 : ℝ) 1 := by
  ext x
  simp only [mem_iUnion,mem_Icc]
  constructor
  · rintro ⟨n,hlo,hhi⟩
    have hn : (1 : ℝ) ≤ n+1 := by have hn := Nat.cast_nonneg (α := ℝ) n; linarith
    have hsmall : 1/((n : ℝ)+1) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
    constructor <;> linarith
  · rintro ⟨hlo,hhi⟩; exact ⟨0,by norm_num; exact ⟨hlo,hhi⟩⟩

theorem shrinking_interval_intersection :
    (⋂ n : ℕ, Icc (-(1/((n : ℝ)+1))) (1/((n : ℝ)+1)))={0} := by
  ext x
  simp only [mem_iInter,mem_Icc,mem_singleton_iff]
  constructor
  · intro h
    by_contra hx
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hx)
    have hh := abs_le.mpr (h n)
    linarith
  · intro hx; subst x
    intro n; have hp : 0 ≤ 1/((n : ℝ)+1) := by positivity
    constructor <;> linarith

theorem interval_deMorgan :
    (Icc (-1 : ℝ) 2)ᶜ=Iio (-1) ∪ Ioi 2 := by
  ext x
  simp only [mem_compl_iff,mem_Icc,not_and_or,not_le,mem_union,mem_Iio,mem_Ioi]

theorem finite_square_image :
    ({-2,-1,0,1,2} : Finset ℤ).image (fun x => x^2)={0,1,4} ∧
    (9 : ℤ) ∉ ({-2,-1,0,1,2} : Finset ℤ).image (fun x => x^2) := by decide

theorem composition_examples (x : ℝ) :
    ((fun x : ℝ => 2*x-1) ∘ (fun x : ℝ => x^2)) x=2*x^2-1 ∧
    ((fun x : ℝ => x^2) ∘ (fun x : ℝ => 2*x-1)) x=4*x^2-4*x+1 ∧
    2*(2 : ℝ)^2-1=7 ∧ (2*(2 : ℝ)-1)^2=9 := by
  dsimp; constructor
  · ring
  constructor
  · ring
  · norm_num

theorem square_interval_image :
    (fun x : ℝ => x^2) '' Icc (-3 : ℝ) 1=Icc 0 9 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩; constructor
    · positivity
    · nlinarith [hx.1,hx.2]
  · intro hy
    refine ⟨-Real.sqrt y,?_,?_⟩
    · have hs := Real.sq_sqrt hy.1
      have hp := Real.sqrt_nonneg y
      constructor <;> nlinarith [hy.2]
    · simpa using Real.sq_sqrt hy.1

theorem square_interval_preimage :
    (fun x : ℝ => x^2) ⁻¹' Icc (1 : ℝ) 4=Icc (-2) (-1) ∪ Icc 1 2 := by
  ext x
  simp only [mem_preimage,mem_Icc,mem_union]
  constructor
  · rintro ⟨hlo,hhi⟩
    by_cases hx : x ≤ 0
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith
  · rintro (⟨hlo,hhi⟩ | ⟨hlo,hhi⟩) <;> constructor <;> nlinarith

theorem negative_square_preimage : (fun x : ℝ => x^2) ⁻¹' {(-1)}=∅ := by
  ext x
  simp only [mem_preimage,mem_singleton_iff,mem_empty_iff_false,iff_false]
  nlinarith [sq_nonneg x]

abbrev Nonnegative := {x : ℝ // 0 ≤ x}
def squareToNonnegative (x : ℝ) : Nonnegative := ⟨x^2,sq_nonneg x⟩
def squareFromNonnegative (x : Nonnegative) : ℝ := x.val^2
def squareNonnegative (x : Nonnegative) : Nonnegative := ⟨x.val^2,sq_nonneg x.val⟩
def sqrtNonnegative (x : Nonnegative) : Nonnegative := ⟨Real.sqrt x.val,Real.sqrt_nonneg _⟩

theorem square_to_nonnegative_classification :
    Function.Surjective squareToNonnegative ∧ ¬ Function.Injective squareToNonnegative := by
  constructor
  · intro y; refine ⟨Real.sqrt y.val,?_⟩
    apply Subtype.ext; exact Real.sq_sqrt y.property
  · intro h
    have hh := h (a₁ := (-1 : ℝ)) (a₂ := 1) (by apply Subtype.ext; norm_num [squareToNonnegative])
    norm_num at hh

theorem square_from_nonnegative_classification :
    Function.Injective squareFromNonnegative ∧ ¬ Function.Surjective squareFromNonnegative := by
  constructor
  · intro x y h; apply Subtype.ext
    exact SafeLearning.PrimersFoundations.square_injective_nonnegative _ _ x.property y.property h
  · intro h; obtain ⟨x,hx⟩ := h (-1)
    dsimp [squareFromNonnegative] at hx
    nlinarith [sq_nonneg x.val]

theorem nonnegative_square_inverse :
    Function.LeftInverse sqrtNonnegative squareNonnegative ∧
    Function.RightInverse sqrtNonnegative squareNonnegative := by
  constructor
  · intro x; apply Subtype.ext
    exact Real.sqrt_sq x.property
  · intro y; apply Subtype.ext
    exact Real.sq_sqrt y.property

theorem affine_iterated_error (a q b : ℝ) (n : ℕ) :
    (fun x : ℝ => b+q*(x-b))^[n] a-b=q^n*(a-b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',pow_succ]
    calc
      _ = q*((fun x : ℝ => b+q*(x-b))^[n] a-b) := by ring
      _ = q^n*q*(a-b) := by rw [ih]; ring

theorem quarter_iteration_error (a : ℝ) (n : ℕ) :
    (fun x : ℝ => (x+3)/4)^[n] a-1=(1/4 : ℝ)^n*(a-1) := by
  have hfun : (fun x : ℝ => (x+3)/4)=(fun x : ℝ => 1+(1/4)*(x-1)) := by ext x; ring
  rw [hfun]; exact affine_iterated_error a (1/4) 1 n

theorem alternating_iteration_error (n : ℕ) :
    (fun x : ℝ => -x/2+3)^[n] 0-2= -2*(-1/2 : ℝ)^n ∧
    |(fun x : ℝ => -x/2+3)^[n] 0-2|=2*(1/2 : ℝ)^n := by
  have hfun : (fun x : ℝ => -x/2+3)=(fun x : ℝ => 2+(-1/2)*(x-2)) := by ext x; ring
  have he : (fun x : ℝ => -x/2+3)^[n] 0-2= -2*(-1/2 : ℝ)^n := by
    rw [hfun,affine_iterated_error]; ring
  refine ⟨he,?_⟩
  rw [he,abs_mul,abs_pow]; norm_num

theorem alternating_iteration_minimal (n : ℕ) :
    |(fun x : ℝ => -x/2+3)^[n] 0-2| ≤ 1/100 ↔ 8 ≤ n := by
  rw [(alternating_iteration_error n).2]
  have hmono : Antitone (fun n : ℕ => (1/2 : ℝ)^n) := pow_right_anti₀ (by norm_num) (by norm_num)
  constructor
  · intro h; by_contra hn
    have hn' : n ≤ 7 := by omega
    have hh := hmono hn'; norm_num at hh; linarith
  · intro hn; have hh := hmono hn; norm_num at hh; linarith

theorem half_open_contraction_counterexample :
    (∀ x ∈ Ioc (0 : ℝ) 1, x/2 ∈ Ioc 0 1) ∧
    (∀ x y : ℝ, |x/2-y/2|=|x-y|/2) ∧
    ¬ ∃ x ∈ Ioc (0 : ℝ) 1, x/2=x := by
  refine ⟨?_,?_,?_⟩
  · intro x hx; constructor <;> linarith [hx.1,hx.2]
  · intro x y; rw [← sub_div,abs_div]; norm_num
  · rintro ⟨x,hx,h⟩; linarith [hx.1]

theorem selfmap_counterexample :
    (1/2*(1 : ℝ)+1) ∉ Icc (0 : ℝ) 1 ∧
    ¬ ∃ x ∈ Icc (0 : ℝ) 1, x/2+1=x := by
  constructor
  · norm_num
  · rintro ⟨x,hx,h⟩; linarith [hx.2]

theorem strict_contraction_counterexample :
    (∀ x y : ℝ, |(-x)-(-y)|=|x-y|) ∧
    (∀ L : ℝ, L < 1 → ¬ ∀ x y : ℝ, |(-x)-(-y)| ≤ L*|x-y|) ∧
    (- (0 : ℝ)=0) := by
  refine ⟨?_,?_,by norm_num⟩
  · intro x y; have h : -x- -y= -(x-y) := by ring
    rw [h,abs_neg]
  · intro L hL h
    have hh := h 1 0; norm_num at hh; linarith

theorem fixedpoint_uniqueness_does_not_supply_existence :
    (∀ x y : ℝ, |((x+1)/3)-((y+1)/3)| ≤ |x-y|/3) ∧
    ¬ ∃ x ∈ Ioo (0 : ℝ) (1/2), (x+1)/3=x := by
  constructor
  · intro x y; have h : (x+1)/3-(y+1)/3=(x-y)/3 := by ring
    rw [h,abs_div]; norm_num
  · rintro ⟨x,hx,h⟩; linarith [hx.2]

theorem missing_endpoint_contraction :
    (∀ x ∈ Ioc (0 : ℝ) 1, x/3 ∈ Ioc 0 1) ∧
    (∀ x y : ℝ, |x/3-y/3|=|x-y|/3) ∧
    ¬ ∃ x ∈ Ioc (0 : ℝ) 1, x/3=x := by
  refine ⟨?_,?_,?_⟩
  · intro x hx; constructor <;> linarith [hx.1,hx.2]
  · intro x y; rw [← sub_div,abs_div]; norm_num
  · rintro ⟨x,hx,h⟩; linarith [hx.1]

theorem invariant_and_rate_from_local_hypothesis (f : ℝ → ℝ) (x : ℕ → ℝ)
    (hx₀ : x 0 ∈ Icc (-1 : ℝ) 1)
    (hf : ∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ (4/5)*|z|)
    (hstep : ∀ n, x (n+1)=f (x n)) :
    ∀ n, |x n| ≤ (4/5 : ℝ)^n*|x 0| ∧ x n ∈ Icc (-1 : ℝ) 1 := by
  have hstart : |x 0| ≤ 1 := abs_le.mpr hx₀
  intro n
  induction n with
  | zero => simpa using And.intro (le_refl |x 0|) hx₀
  | succ n ih =>
    have hp : (4/5 : ℝ)^(n+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hr : |x (n+1)| ≤ (4/5 : ℝ)^(n+1)*|x 0| := by
      rw [hstep,pow_succ]
      have hh := hf (x n) ih.2
      have hm := mul_le_mul_of_nonneg_left ih.1 (by norm_num : (0 : ℝ) ≤ 4/5)
      nlinarith
    refine ⟨hr,abs_le.mp (hr.trans ?_)⟩
    have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg (x 0))
    linarith

theorem alternating_unit_sequence_not_convergent :
    ¬ ∃ l : ℝ, Tendsto (fun n : ℕ => (-1 : ℝ)^n) atTop (𝓝 l) := by
  rintro ⟨l,hl⟩
  have heven : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have hodd : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have h₁ : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 l) := by
    simpa [Function.comp_def,pow_mul] using hl.comp heven
  have h₂ : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 l) := by
    simpa [Function.comp_def,pow_succ,pow_mul] using hl.comp hodd
  have hl₁ : l=1 := tendsto_nhds_unique h₁ tendsto_const_nhds
  have hl₂ : l= -1 := tendsto_nhds_unique h₂ tendsto_const_nhds
  linarith

theorem geometric_invariant_rate (V : ℕ → ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hstep : ∀ n, V (n+1) ≤ q*V n) :
    ∀ n, V n ≤ q^n*V 0 := by
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    have hh := mul_le_mul_of_nonneg_left ih hq
    rw [pow_succ]; nlinarith [hstep n]

theorem telescoping_energy_budget (V a : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n)
    (ha : ∀ n, 0 ≤ a n) (hstep : ∀ n, V (n+1)-V n ≤ -a n/2) :
    ∀ T, (∑ n ∈ Finset.range T, a n) ≤ 2*V 0 := by
  have ht : ∀ T, V T+(∑ n ∈ Finset.range T, a n)/2 ≤ V 0 := by
    intro T; induction T with
    | zero => simp
    | succ T ih => rw [Finset.sum_range_succ]; linarith [hstep T]
  intro T; have hh := ht T; linarith [hV T]

theorem telescoping_summability (V a : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n)
    (ha : ∀ n, 0 ≤ a n) (hstep : ∀ n, V (n+1)-V n ≤ -a n/2) :
    Summable a ∧ Tendsto a atTop (𝓝 0) := by
  have hs : Summable a := summable_of_sum_range_le ha (telescoping_energy_budget V a hV ha hstep)
  exact ⟨hs,hs.tendsto_atTop_zero⟩

theorem telescoping_state_convergence {E : Type*} [NormedAddCommGroup E]
    (V : ℕ → ℝ) (x : ℕ → E) (hV : ∀ n, 0 ≤ V n)
    (hstep : ∀ n, V (n+1)-V n ≤ -‖x n‖^2/2) :
    Tendsto x atTop (𝓝 0) := by
  have hsq := (telescoping_summability V (fun n => ‖x n‖^2) hV (fun n => sq_nonneg _) hstep).2
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hn : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

theorem excursion_budget_finite (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hbudget : ∀ T, (∑ n ∈ Finset.range T, a n) ≤ 6) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1/25 ≤ a n) : S.card ≤ 150 := by
  have hsum : (S.card : ℝ)*(1/25) ≤ ∑ n ∈ S, a n := by
    simpa using Finset.sum_le_sum (fun n hn => hS n hn)
  have hsub : S ⊆ Finset.range (S.sup id+1) := by
    intro n hn; simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => ha n)
  have hb := hbudget (S.sup id+1)
  have hc : (S.card : ℝ) ≤ 150 := by linarith
  exact_mod_cast hc

theorem arbitrarily_late_excursion (N : ℕ) :
    let a : ℕ → ℝ := fun n => if n=N then 1/25 else 0
    (∀ n, 0 ≤ a n) ∧ (∀ T, (∑ n ∈ Finset.range T, a n) ≤ 6) ∧ a N=1/25 := by
  dsimp
  refine ⟨?_,?_,by simp⟩
  · intro n; split_ifs <;> norm_num
  · intro T
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num

end SafeLearning.CompleteFoundationsLogic
