import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace SafeLearning.CompleteFoundationsTeaching

theorem arithmetic_refresh :
    (-3 : ℝ)^2=9 ∧ -(3 : ℝ)^2 = -9 ∧ |(-3 : ℝ)|=3 ∧
    |(-2 : ℝ)-1|=3 ∧ (1/2 : ℝ)+1/3=5/6 ∧ (2 : ℝ)/(1/2)=4 ∧
    (2 : ℝ)^(-3 : ℤ)=1/8 ∧ (1/2 : ℝ)^0+(1/2)^1+(1/2)^2=7/4 ∧
    (-2 : ℝ)^2=4 ∧ (1/4 : ℝ)+1/2=3/4 ∧ (2 : ℝ)^(-2 : ℤ)=1/4 := by norm_num

theorem reciprocal_decreases (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    0 < 1/(s+1) ∧ 1/(t+1) ≤ 1/(s+1) := by
  constructor
  · positivity
  · exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem elementary_equations (x : ℝ) :
    (2*x+1=5 ↔ x=2) ∧ (-2*x ≤ 4 ↔ -2 ≤ x) ∧
    (x^2 ≤ 4 ↔ -2 ≤ x ∧ x ≤ 2) ∧ (-3*x > 6 ↔ x < -2) := by
  constructor
  · constructor <;> intro h <;> linarith
  constructor
  · constructor <;> intro h <;> linarith
  constructor
  · constructor
    · intro h; constructor <;> nlinarith
    · rintro ⟨hl,hu⟩; nlinarith [mul_nonneg (by linarith : 0 ≤ x+2) (by linarith : 0 ≤ 2-x)]
  · constructor <;> intro h <;> linarith

theorem disc_and_box (x y : ℝ) :
    (0 ≤ 1-x^2-y^2 ↔ x^2+y^2 ≤ 1) ∧
    (0 ≤ 1-x^2-y^2 → |x| ≤ 1 ∧ |y| ≤ 1) ∧
    1-(3/5 : ℝ)^2-(4/5)^2=0 ∧ 1-(1 : ℝ)^2-1^2 = -1 := by
  constructor
  · constructor <;> intro h <;> linarith
  constructor
  · intro h; constructor <;> rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg x,sq_nonneg y]
  · norm_num

theorem subset_antisymmetry {X : Type*} (A B : Set X) :
    A=B ↔ A ⊆ B ∧ B ⊆ A := Set.Subset.antisymm_iff

theorem indexed_deMorgan {X I : Type*} (A : I → Set X) :
    (⋃ i, A i)ᶜ=(⋂ i, (A i)ᶜ) ∧ (⋂ i, A i)ᶜ=(⋃ i, (A i)ᶜ) := by
  constructor <;> ext x <;> simp

theorem logical_connectives (P Q : Prop) :
    ((P → Q) ↔ (¬Q → ¬P)) ∧ ((P → Q) ↔ (¬P ∨ Q)) ∧
    ((P ∨ Q) ↔ (¬Q → P)) := by tauto

theorem bounded_quantifier_negation {X : Type*} (A : Set X) (P : X → Prop) :
    (¬ ∀ x ∈ A, P x) ↔ ∃ x ∈ A, ¬P x := by simp

theorem no_largest_real :
    (∀ x : ℝ, ∃ y : ℝ, x < y) ∧ ¬ (∃ y : ℝ, ∀ x : ℝ, x < y) := by
  constructor
  · intro x; exact ⟨x+1,by linarith⟩
  · rintro ⟨y,hy⟩; exact (lt_irrefl y) (hy y)

theorem viability_complement {X U T : Type*} (admissible : Set U) (times : Set T)
    (flow : U → X → T → X) (failure : Set X) :
    {x | ∃ u ∈ admissible, ∀ t ∈ times, flow u x t ∉ failure}ᶜ=
      {x | ∀ u ∈ admissible, ∃ t ∈ times, flow u x t ∈ failure} := by
  ext x; simp only [mem_compl_iff,mem_setOf_eq,not_exists,not_and,not_forall,not_imp,
    not_not,exists_prop]

theorem shifted_equilibrium {E : Type*} [AddCommGroup E] (F : E → E) (p : E)
    (hp : F p=p) : (fun z => F (z+p)-p) 0=0 := by simp [hp]

theorem image_intersection_counterexample :
    (fun x : ℝ => x^2) '' (({(-1)} : Set ℝ) ∩ {1})=∅ ∧
    (fun x : ℝ => x^2) '' ({(-1)} : Set ℝ) ∩
      (fun x : ℝ => x^2) '' ({1} : Set ℝ)={1} := by norm_num

theorem image_intersection_subset {X Y : Type*} (f : X → Y) (A B : Set X) :
    f '' (A ∩ B) ⊆ f '' A ∩ f '' B := Set.image_inter_subset f A B

theorem projection_is_existential {X Y : Type*} (S : Set (X × Y)) :
    Prod.snd '' S={y | ∃ x, (x,y) ∈ S} := by ext y; simp

theorem affine_bijection : Function.Bijective (fun x : ℝ => 2*x+1) := by
  constructor
  · intro x y h; linarith
  · intro y; exact ⟨(y-1)/2,by ring⟩

theorem norm_arbitrarily_small {E : Type*} [NormedAddCommGroup E] (x : E)
    (h : ∀ ε : ℝ, 0 < ε → ‖x‖ ≤ ε) : x=0 := by
  apply norm_eq_zero.mp
  by_contra hn
  have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hn)
  have hh := h (‖x‖/2) (by positivity)
  linarith

theorem banach_first_error_bound {X : Type*} [MetricSpace X]
    (g : X → X) (L : NNReal) (hg : ContractingWith L g) (p : X) (hp : g p=p)
    (x : X) (n : ℕ) : dist (g^[n] x) p ≤ (L : ℝ)^n*dist x p := by
  have hh := hg.toLipschitzWith.iterate n |>.dist_le_mul x p
  have hpiter : g^[n] p=p := (show Function.IsFixedPt g p from hp).iterate n
  simpa only [hpiter,NNReal.coe_pow] using hh

theorem contraction_unique_general {X : Type*} [MetricSpace X]
    (g : X → X) (L : NNReal) (hg : ContractingWith L g) (x y : X)
    (hx : g x=x) (hy : g y=y) : x=y := hg.fixedPoint_unique' hx hy

theorem monotone_bounded_convergence (a : ℕ → ℝ) (ha : Monotone a)
    (hb : BddAbove (Set.range a)) : Tendsto a atTop (𝓝 (⨆ n, a n)) :=
  tendsto_atTop_ciSup ha hb

theorem antitone_bounded_convergence (a : ℕ → ℝ) (ha : Antitone a)
    (hb : BddBelow (Set.range a)) : Tendsto a atTop (𝓝 (⨅ n, a n)) :=
  tendsto_atTop_ciInf ha hb

theorem continuous_limits {X : Type*} [TopologicalSpace X] (a : ℕ → X) (p : X)
    (f : X → ℝ) (hf : ContinuousAt f p) (ha : Tendsto a atTop (𝓝 p)) :
    Tendsto (fun n => f (a n)) atTop (𝓝 (f p)) := hf.tendsto.comp ha

theorem limit_arithmetic (a b : ℕ → ℝ) (x y : ℝ)
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y)) (hy : y ≠ 0) :
    Tendsto (fun n => a n+b n) atTop (𝓝 (x+y)) ∧
    Tendsto (fun n => a n*b n) atTop (𝓝 (x*y)) ∧
    Tendsto (fun n => a n/b n) atTop (𝓝 (x/y)) := ⟨ha.add hb,ha.mul hb,ha.div hb hy⟩

theorem weierstrass_maximum {X : Type*} [TopologicalSpace X]
    (C : Set X) (hc : IsCompact C) (hn : C.Nonempty) (f : X → ℝ)
    (hf : ContinuousOn f C) : ∃ x ∈ C, ∀ y ∈ C, f y ≤ f x := hc.exists_isMaxOn hn hf

theorem compact_positive_margin {X : Type*} [TopologicalSpace X]
    (C : Set X) (hc : IsCompact C) (f : X → ℝ) (hf : ContinuousOn f C)
    (hp : ∀ x ∈ C, 0 < f x) : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ C, m ≤ f x :=
  hc.exists_forall_le' hf hp

theorem heine_cantor {X : Type*} [UniformSpace X] (C : Set X)
    (hc : IsCompact C) (f : X → ℝ) (hf : ContinuousOn f C) :
    UniformContinuousOn f C := hc.uniformContinuousOn_of_continuous hf

theorem lipschitz_net_margin {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (L : NNReal) (hf : LipschitzWith L f) (C Z : Set X) (τ m : ℝ)
    (hnet : ∀ x ∈ C, ∃ z ∈ Z, dist x z ≤ τ)
    (hmargin : ∀ z ∈ Z, m ≤ f z) : ∀ x ∈ C, m-(L : ℝ)*τ ≤ f x := by
  intro x hx
  obtain ⟨z,hz,hd⟩ := hnet x hx
  have hh := hf.dist_le_mul x z
  rw [Real.dist_eq] at hh
  have hm := mul_le_mul_of_nonneg_left hd L.coe_nonneg
  have hb := (abs_le.mp hh).1
  linarith [hmargin z hz]

theorem norm_power_bound {R : Type*} [NormedRing R] [NormOneClass R] (A : R) (k : ℕ) :
    ‖A^k‖ ≤ ‖A‖^k := norm_pow_le A k

theorem exponential_tangent (x : ℝ) : 1+x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

theorem logarithm_tangent (x : ℝ) (hx : 0 < x) : Real.log x ≤ x-1 :=
  Real.log_le_sub_one_of_pos hx

def squareDomain := {x : ℤ // x ∈ ({-2,-1,0,1,2} : Finset ℤ)}
def squareCodomain := {y : ℤ // y ∈ ({0,1,4,9} : Finset ℤ)}
def finiteSquare (x : squareDomain) : squareCodomain := ⟨x.val^2,by
  have hx := x.property
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx <;> rw [hx] <;> norm_num⟩

theorem finite_square_classification :
    ¬ Function.Injective finiteSquare ∧ ¬ Function.Surjective finiteSquare := by
  constructor
  · intro h
    have hh := h (a₁ := ⟨-1,by norm_num⟩) (a₂ := ⟨1,by norm_num⟩)
      (by apply Subtype.ext;norm_num [finiteSquare])
    have he := congrArg Subtype.val hh
    norm_num at he
  · intro h
    obtain ⟨x,hx⟩ := h ⟨9,by norm_num⟩
    have he := congrArg Subtype.val hx
    have hd := x.property
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd
    change x.val^2=9 at he
    rcases hd with hd | hd | hd | hd | hd <;> rw [hd] at he <;> norm_num at he

theorem stabilized_reachFive (n : ℕ) :
    SafeLearning.PrimersFoundations.reachFive^[n+2] {0}={0,1,2} := by
  have hf : Function.IsFixedPt SafeLearning.PrimersFoundations.reachFive ({0,1,2} : Finset (Fin 5)) :=
    SafeLearning.PrimersFoundations.reachFive_iterates.2.2
  rw [Function.iterate_add_apply]
  have htwo : SafeLearning.PrimersFoundations.reachFive^[2] {0}=({0,1,2} : Finset (Fin 5)) := by
    simp only [Function.iterate_succ_apply',Function.iterate_zero_apply]
    rw [SafeLearning.PrimersFoundations.reachFive_iterates.1,
      SafeLearning.PrimersFoundations.reachFive_iterates.2.1]
  rw [htwo]
  exact hf.iterate n

theorem half_open_not_closed : ¬ IsClosed (Ioc (0 : ℝ) 1) := by
  intro h
  have he := h.closure_eq
  rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)] at he
  have hz : (0 : ℝ) ∈ Ioc 0 1 := he ▸ (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  norm_num at hz

theorem half_open_counterexample_limit :
    (∀ n : ℕ, (1/2 : ℝ)^n ∈ Ioc 0 1) ∧
    Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) := by
  constructor
  · intro n
    exact ⟨pow_pos (by norm_num) n,pow_le_one₀ (by norm_num) (by norm_num)⟩
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem sequence_initial_values :
    (3 : ℝ)/(0+1)=3 ∧ (3 : ℝ)/(1+1)=3/2 ∧
    (3 : ℝ)/(2+1)=1 ∧ (3 : ℝ)/(3+1)=3/4 ∧
    (3 : ℝ)/(29+1)=1/10 ∧ (3 : ℝ)/31<1/10 := by norm_num

theorem all_time_excursion_card (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hbudget : ∀ T, (∑ n ∈ Finset.range T, a n) ≤ 6) :
    {n | 1/25 ≤ a n}.Finite ∧ {n | 1/25 ≤ a n}.ncard ≤ 150 := by
  classical
  have hb : ∀ S : Finset ℕ, (∀ n ∈ S, 1/25 ≤ a n) → S.card ≤ 150 := by
    intro S hS
    have hsum : (S.card : ℝ)*(1/25) ≤ ∑ n ∈ S, a n := by
      simpa using Finset.sum_le_sum (fun n hn => hS n hn)
    have hsub : S ⊆ Finset.range (S.sup id+1) := by
      intro n hn; simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => ha n)
    have hh := hbudget (S.sup id+1)
    have hc : (S.card : ℝ) ≤ 150 := by linarith
    exact_mod_cast hc
  have hfinite : {n | 1/25 ≤ a n}.Finite := by
    by_contra hn
    obtain ⟨S,hS,hSf,hSc⟩ := Set.Infinite.exists_subset_ncard_eq hn 151
    have hc := hb hSf.toFinset (by intro n hn;exact hS (hSf.mem_toFinset.mp hn))
    rw [← Set.ncard_eq_toFinset_card S hSf,hSc] at hc
    omega
  refine ⟨hfinite,?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact hb hfinite.toFinset (by intro n hn;exact hfinite.mem_toFinset.mp hn)

theorem finite_excursion_last_index (a : ℕ → ℝ)
    (hf : {n | 1/25 ≤ a n}.Finite) : ∃ N : ℕ, ∀ n ≥ N, a n < 1/25 := by
  obtain ⟨N,hN⟩ := hf.bddAbove
  exact ⟨N+1,by intro n hn;by_contra h;have hh := hN (le_of_not_gt h);omega⟩

end SafeLearning.CompleteFoundationsTeaching
